import TetraStereo.UniversalProof.SourceNativeRawAnnotationGuardProofs.SourceNativeDevelopmentTransaction

set_option autoImplicit false

namespace TetraStereo.UniversalProof.SourceNativeRawAnnotationGuardProofs.SourceNativeRawAnnotationGuard

open TetraStereo.OneCenter TetraStereo.OneCenter.AuthoritativeChemicalInput
open ScheduledDrawingSpatialEndToEndProofs.ScheduledDrawingSpatialWholeMolecule
open SourceNativeDevelopmentTransaction



















inductive RawAnnotationIssue where
  | unsupportedNormalizedAtomParity (index : Nat) (parity : TetrahedralInputParity)
  | unsupportedNormalizedBondDirection (bond : RawBond) (direction : Bool)
  deriving DecidableEq

/-- Visit every actual atom, retaining its normalized parser index. -/
def atomAnnotationIssues : Nat → List AtomSpec → List RawAnnotationIssue
  | _, [] => []
  | index, atom :: rest =>
      (match atom.tetrahedral? with
       | none => []
       | some parity => [.unsupportedNormalizedAtomParity index parity]) ++
        atomAnnotationIssues (index + 1) rest

/-- `ParsedBondKind.directional?` is the actual raw representation of `/` and `\` markers. -/
def bondAnnotationIssues (bonds : List RawBond) : List RawAnnotationIssue :=
  bonds.filterMap fun bond => bond.kind.directional?.map
    (RawAnnotationIssue.unsupportedNormalizedBondDirection bond)

def rawAnnotationIssues (request : SourceNativeDevelopmentRequest) : List RawAnnotationIssue :=
  atomAnnotationIssues 0 request.normalized.result.parsed.atoms ++
    bondAnnotationIssues request.normalized.result.parsed.bonds

/-- Independent annotation-free admission, stated directly over the actual normalized records. -/
def RawAnnotationFree (request : SourceNativeDevelopmentRequest) : Prop :=
  (∀ atom ∈ request.normalized.result.parsed.atoms, atom.tetrahedral? = none) ∧
    ∀ bond ∈ request.normalized.result.parsed.bonds, bond.kind.directional? = none

theorem atomAnnotationIssues_eq_nil_iff (index : Nat) (atoms : List AtomSpec) :
    atomAnnotationIssues index atoms = [] ↔ ∀ atom ∈ atoms, atom.tetrahedral? = none := by
  induction atoms generalizing index with
  | nil => simp [atomAnnotationIssues]
  | cons atom rest ih =>
      rw [atomAnnotationIssues, List.append_eq_nil_iff, ih]
      cases observed : atom.tetrahedral? <;> simp [observed]

theorem bondAnnotationIssues_eq_nil_iff (bonds : List RawBond) :
    bondAnnotationIssues bonds = [] ↔ ∀ bond ∈ bonds, bond.kind.directional? = none := by
  unfold bondAnnotationIssues
  rw [List.filterMap_eq_nil_iff]
  simp

theorem rawAnnotationIssues_eq_nil_iff (request : SourceNativeDevelopmentRequest) :
    rawAnnotationIssues request = [] ↔ RawAnnotationFree request := by
  unfold rawAnnotationIssues RawAnnotationFree
  rw [List.append_eq_nil_iff, atomAnnotationIssues_eq_nil_iff, bondAnnotationIssues_eq_nil_iff]

/-- The successor returns only the original actual five-family payload; refusal is global. -/
noncomputable def guardedProduce (request : SourceNativeDevelopmentRequest) :
    Option (List (ScheduledHybridRepresentedResult request.source)) :=
  if rawAnnotationIssues request = [] then request.produce else none

theorem guardedProduce_eq_some_iff (request : SourceNativeDevelopmentRequest)
    (rows : List (ScheduledHybridRepresentedResult request.source)) :
    guardedProduce request = some rows ↔
      RawAnnotationFree request ∧ request.ConstitutionalAgreement ∧
        request.auditIssues = [] ∧ rows = request.report := by
  unfold guardedProduce
  by_cases free : rawAnnotationIssues request = []
  · rw [if_pos free, SourceNativeDevelopmentRequest.produce_eq_some_iff]
    have admitted := (rawAnnotationIssues_eq_nil_iff request).mp free
    exact ⟨fun accepted => ⟨admitted, accepted⟩, fun accepted => accepted.2⟩
  · rw [if_neg free]
    constructor
    · intro impossible
      cases impossible
    · intro accepted
      exact (free ((rawAnnotationIssues_eq_nil_iff request).mpr accepted.1)).elim

theorem guardedProduce_eq_none_iff (request : SourceNativeDevelopmentRequest) :
    guardedProduce request = none ↔
      ¬ RawAnnotationFree request ∨ ¬ request.ConstitutionalAgreement ∨ request.auditIssues ≠ [] := by
  unfold guardedProduce
  by_cases free : rawAnnotationIssues request = []
  · rw [if_pos free, SourceNativeDevelopmentRequest.produce_eq_none_iff]
    have admitted := (rawAnnotationIssues_eq_nil_iff request).mp free
    exact ⟨Or.inr, fun refused => refused.resolve_left (not_not.mpr admitted)⟩
  · rw [if_neg free]
    have refused : ¬ RawAnnotationFree request := fun admitted =>
      free ((rawAnnotationIssues_eq_nil_iff request).mpr admitted)
    exact ⟨fun _ => Or.inl refused, fun _ => rfl⟩

theorem guardedProduce_member_sound (request : SourceNativeDevelopmentRequest)
    (rows : List (ScheduledHybridRepresentedResult request.source))
    (computed : guardedProduce request = some rows)
    (result : ScheduledHybridRepresentedResult request.source) (present : result ∈ rows) :
    ScheduledHybridRepresentedMeaning request.source request.supplied request.electronicReady
      request.semantics request.ruleFuel result := by
  have accepted := (guardedProduce_eq_some_iff request rows).mp computed
  rw [accepted.2.2.2] at present
  exact SourceNativeDevelopmentRequest.report_member_sound request result present

theorem guardedProduce_eq_none_of_raw_issue (request : SourceNativeDevelopmentRequest)
    (issue : RawAnnotationIssue) (present : issue ∈ rawAnnotationIssues request) :
    guardedProduce request = none := by
  apply (guardedProduce_eq_none_iff request).mpr
  apply Or.inl
  intro admitted
  rw [(rawAnnotationIssues_eq_nil_iff request).mpr admitted] at present
  exact List.not_mem_nil present

namespace ClosedRawCounterexample

/-- The same five atoms and four bonds, with only the original carbon's raw parity changed. -/
def annotatedRawCF : RawMolecule :=
  { ClosedSource.rawCF with atoms :=
      [{ AtomSpec.aliphatic .C with tetrahedral? := some .clockwise },
        AtomSpec.aliphatic .F, AtomSpec.aliphatic .Cl, AtomSpec.aliphatic .Br,
        AtomSpec.aliphatic .I] }

def annotatedNormalizedCF : ChemistryNormalizationResult := normalizeRawMolecule annotatedRawCF

/-- All four actual production certification checks still hold on the annotated parser input. -/
def annotatedCertifiedCF : CertifiedChemistryNormalizationResult where
  result := annotatedNormalizedCF
  admissible := (annotatedNormalizedCF.parsed.admissible?_eq_true_iff).mp (by decide +kernel)
  writtenNeighborExact :=
    (annotatedNormalizedCF.parsed.writtenNeighborExact?_eq_true_iff).mp (by decide +kernel)
  valenceOK := (annotatedNormalizedCF.parsed.valenceOK?_eq_true_iff).mp (by decide +kernel)
  rule2MassesKnown :=
    (annotatedNormalizedCF.parsed.rule2MassesKnown?_eq_true_iff).mp (by decide +kernel)

/-- Source, input, electronic readiness and auxiliary semantics are the existing closed request's. -/
noncomputable def annotatedRequest : SourceNativeDevelopmentRequest :=
  { ClosedSource.closedRequest with normalized := annotatedCertifiedCF }

theorem actual_normalized_annotation_retained :
    (annotatedRequest.normalized.result.parsed.atomAt? 0).bind AtomSpec.tetrahedral? =
      some .clockwise ∧
    annotatedRequest.source = ClosedSource.closedRequest.source ∧
    annotatedRequest.normalized.result.parsed.bonds = ClosedSource.rawCF.bonds := by
  exact ⟨by decide +kernel, rfl, by decide +kernel⟩

theorem annotated_constitutionalAgreement : annotatedRequest.ConstitutionalAgreement := by
  show annotatedNormalizedCF.parsed.toSemanticMolecule? =
    some ClosedSource.closedRequest.source.molecule
  decide +kernel

/-- **Preserved old policy, historical API key.**  The old policy accepts the unexamined raw
annotation and emits its actual drawing-derived solid `R` row.  Use
`annotated_old_produce_contains_R` for new code. -/
theorem annotated_old_produce_contains_S :
    annotatedRequest.produce = some annotatedRequest.report ∧
      (ScheduledHybridRepresentedResult.tetrahedral
        (⟨SingleWedgeOccurrenceAlignmentRegression.cfclbriProductionCenter,
          .assigned (.chiral RS.R)⟩ : TetrahedralStatusRow SingleWedgeSourceRegression.source)) ∈
        annotatedRequest.report := by
  constructor
  · apply (SourceNativeDevelopmentRequest.produce_eq_some_iff _ _).mpr
    exact ⟨annotated_constitutionalAgreement, ClosedSource.closed_auditIssues_nil, rfl⟩
  · exact ClosedSource.closed_report_contains_solid_S

/-- Accurate-name alias for the preserved old-policy acceptance and its solid `R` row. -/
theorem annotated_old_produce_contains_R :
    annotatedRequest.produce = some annotatedRequest.report ∧
      (ScheduledHybridRepresentedResult.tetrahedral
        (⟨SingleWedgeOccurrenceAlignmentRegression.cfclbriProductionCenter,
          .assigned (.chiral RS.R)⟩ : TetrahedralStatusRow SingleWedgeSourceRegression.source)) ∈
        annotatedRequest.report :=
  annotated_old_produce_contains_S

/-- The successor catches the actual normalized raw annotation, regardless of the clean source diagram. -/
theorem annotated_guard_refuses : guardedProduce annotatedRequest = none := by
  apply guardedProduce_eq_none_of_raw_issue annotatedRequest
    (.unsupportedNormalizedAtomParity 0 .clockwise)
  decide +kernel

/-- **Genuine unannotated request, historical API key.**  The genuine unannotated closed request
retains its accepted payload and actual solid `R` member.  Use
`unannotated_guard_preserves_actual_R` for new code. -/
theorem unannotated_guard_preserves_actual_S :
    guardedProduce ClosedSource.closedRequest = some ClosedSource.closedRequest.report ∧
      (ScheduledHybridRepresentedResult.tetrahedral
        (⟨SingleWedgeOccurrenceAlignmentRegression.cfclbriProductionCenter,
          .assigned (.chiral RS.R)⟩ : TetrahedralStatusRow SingleWedgeSourceRegression.source)) ∈
        ClosedSource.closedRequest.report := by
  constructor
  · unfold guardedProduce
    rw [if_pos (show rawAnnotationIssues ClosedSource.closedRequest = [] by decide +kernel)]
    exact ClosedSource.closed_produce_eq_some
  · exact ClosedSource.closed_report_contains_solid_S

/-- Accurate-name alias for the unannotated request's preserved solid `R` row. -/
theorem unannotated_guard_preserves_actual_R :
    guardedProduce ClosedSource.closedRequest = some ClosedSource.closedRequest.report ∧
      (ScheduledHybridRepresentedResult.tetrahedral
        (⟨SingleWedgeOccurrenceAlignmentRegression.cfclbriProductionCenter,
          .assigned (.chiral RS.R)⟩ : TetrahedralStatusRow SingleWedgeSourceRegression.source)) ∈
        ClosedSource.closedRequest.report :=
  unannotated_guard_preserves_actual_S

end ClosedRawCounterexample
end TetraStereo.UniversalProof.SourceNativeRawAnnotationGuardProofs.SourceNativeRawAnnotationGuard
