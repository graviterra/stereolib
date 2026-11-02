import TetraStereo.OneCenter.CIPAuthoritativeOccurrenceFactConformance
import TetraStereo.OneCenter.CIPAuthoritativeStereogenicPerceptionConformance
import TetraStereo.OneCenter.GeometryAnnotatedCIPAnalysis

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Authoritative occurrence facts at the public `StereoAssignment` boundary

This module connects the primitive-stage certificate for
`tetrahedralOccurrenceFactAuthoritative?` to the actual tetrahedral override used by
`analyzeCertifiedNormalized`.  It also states the exact residual boundary: each member of the
authority-facing graph analyzer is either an unchanged legacy `analyzeNormalized` member or a
tetrahedral assignment carrying the new authoritative occurrence-fact judgment.
-/

/-- Exact public outcome conversion for one authoritative occurrence fact. -/
def authoritativeOccurrenceOutcome (fact : RawDescriptorFact) : StereoOutcome :=
  if fact.uppercase then StereoOutcome.tetrahedral fact.descriptor
  else StereoOutcome.pseudoTetrahedral
    (match fact.descriptor with | RS.R => PseudoRS.r | RS.S => PseudoRS.s)

/-- Independent proof-relevant meaning of a public authoritative occurrence override.  The
judgment retains the parsed annotation gate, exclusion of extended-tetrahedral carriers, the full
primitive-stage fact judgment on the hydrogen-expanded molecule, and the exact public outcome. -/
def AuthoritativeOccurrenceStereoAssignmentJudgment
    (result : ChemistryNormalizationResult) (center : Nat)
    (assignment : StereoAssignment) : Prop :=
  ∃ spec parity fact,
    result.parsed.atomAt? center = some spec ∧
    spec.tetrahedral? = some parity ∧
    result.parsed.withExplicitHydrogens.isExtendedTetrahedralParityCarrier center = false ∧
    AuthoritativeTetrahedralOccurrenceFactJudgment result.parsed.withExplicitHydrogens
      (analysisFuel result.parsed.withExplicitHydrogens) center fact ∧
    assignment =
      { unit := StereoUnit.tetrahedral center
        outcome := authoritativeOccurrenceOutcome fact }

/-- The public authoritative override succeeds exactly when its independent primitive-stage
assignment judgment holds. -/
theorem ChemistryNormalizationResult.authoritativeOccurrenceAssignment?_eq_some_iff_judgment
    (result : ChemistryNormalizationResult) (center : Nat)
    (assignment : StereoAssignment) :
    result.authoritativeOccurrenceAssignment? center = some assignment ↔
      AuthoritativeOccurrenceStereoAssignmentJudgment result center assignment := by
  constructor
  · intro produced
    unfold ChemistryNormalizationResult.authoritativeOccurrenceAssignment? at produced
    cases specEq : result.parsed.atomAt? center with
    | none => simp [specEq] at produced
    | some spec =>
        cases parityEq : spec.tetrahedral? with
        | none => simp [specEq, parityEq] at produced
        | some parity =>
            cases extendedEq :
                result.parsed.withExplicitHydrogens.isExtendedTetrahedralParityCarrier center with
            | true => simp [specEq, extendedEq] at produced
            | false =>
                cases factEq : tetrahedralOccurrenceFactAuthoritative?
                    result.parsed.withExplicitHydrogens
                    (analysisFuel result.parsed.withExplicitHydrogens) center with
                | none => simp [specEq, extendedEq, factEq] at produced
                | some fact =>
                    have assignmentEq : assignment =
                        { unit := StereoUnit.tetrahedral center
                          outcome := authoritativeOccurrenceOutcome fact } := by
                      simpa [specEq, parityEq, extendedEq, factEq,
                        authoritativeOccurrenceOutcome] using produced.symm
                    exact ⟨spec, parity, fact, specEq, parityEq, extendedEq,
                      (tetrahedralOccurrenceFactAuthoritative?_eq_some_iff_judgment
                        result.parsed.withExplicitHydrogens
                        (analysisFuel result.parsed.withExplicitHydrogens) center fact).mp factEq,
                      assignmentEq⟩
  · rintro ⟨spec, parity, fact, specEq, parityEq, extendedEq, factJudgment, rfl⟩
    have factEq : tetrahedralOccurrenceFactAuthoritative?
        result.parsed.withExplicitHydrogens
        (analysisFuel result.parsed.withExplicitHydrogens) center = some fact :=
      (tetrahedralOccurrenceFactAuthoritative?_eq_some_iff_judgment
        result.parsed.withExplicitHydrogens
        (analysisFuel result.parsed.withExplicitHydrogens) center fact).mpr factJudgment
    simp [ChemistryNormalizationResult.authoritativeOccurrenceAssignment?, specEq, parityEq,
      extendedEq, factEq, authoritativeOccurrenceOutcome]
    rfl

/-- Exact per-element meaning of the map used by `analyzeWithAuthoritativeOccurrences`. -/
def AuthoritativeOccurrenceOverrideJudgment
    (result : ChemistryNormalizationResult) (base output : StereoAssignment) : Prop :=
  match base.unit with
  | StereoUnit.tetrahedral center =>
      (result.authoritativeOccurrenceAssignment? center = none ∧ output = base) ∨
        AuthoritativeOccurrenceStereoAssignmentJudgment result center output
  | _ => output = base

/-- Applying the public override map is equivalent to the disjoint retained/authoritative
judgment above. -/
theorem ChemistryNormalizationResult.authoritativeOccurrenceOverride_eq_iff
    (result : ChemistryNormalizationResult) (base output : StereoAssignment) :
    (match base.unit with
      | StereoUnit.tetrahedral center =>
          (result.authoritativeOccurrenceAssignment? center).getD base
      | _ => base) = output ↔
      AuthoritativeOccurrenceOverrideJudgment result base output := by
  cases unitEq : base.unit with
  | tetrahedral center =>
      simp only [AuthoritativeOccurrenceOverrideJudgment, unitEq]
      rw [← result.authoritativeOccurrenceAssignment?_eq_some_iff_judgment center output]
      cases overrideEq : result.authoritativeOccurrenceAssignment? center <;>
        simp [eq_comm]
  | doubleBond left right => simp [AuthoritativeOccurrenceOverrideJudgment, unitEq, eq_comm]
  | axis start finish => simp [AuthoritativeOccurrenceOverrideJudgment, unitEq, eq_comm]
  | plane atoms => simp [AuthoritativeOccurrenceOverrideJudgment, unitEq, eq_comm]
  | helix path => simp [AuthoritativeOccurrenceOverrideJudgment, unitEq, eq_comm]
  | polyhedron center => simp [AuthoritativeOccurrenceOverrideJudgment, unitEq, eq_comm]

/-- Every member of the authority-facing graph analyzer retains the exact native source member
and a proof of how the override map treated it. -/
theorem ChemistryNormalizationResult.analyzeWithAuthoritativeOccurrences_member_refines
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment)
    (member : assignment ∈ result.analyzeWithAuthoritativeOccurrences) :
    ∃ base,
      base ∈ analyzeNormalized result ∧
      AuthoritativeOccurrenceOverrideJudgment result base assignment := by
  rw [ChemistryNormalizationResult.analyzeWithAuthoritativeOccurrences,
    List.mem_map] at member
  rcases member with ⟨base, baseMember, mapped⟩
  exact ⟨base, baseMember,
    (result.authoritativeOccurrenceOverride_eq_iff base assignment).mp mapped⟩

/-- Clear residual-boundary form: an authority-facing output is either literally an unchanged
legacy member or carries the authoritative primitive-stage tetrahedral judgment. -/
theorem ChemistryNormalizationResult.analyzeWithAuthoritativeOccurrences_member_native_or_judged
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment)
    (member : assignment ∈ result.analyzeWithAuthoritativeOccurrences) :
    (assignment ∈ analyzeNormalized result) ∨
      ∃ center, AuthoritativeOccurrenceStereoAssignmentJudgment result center assignment := by
  obtain ⟨base, baseMember, refined⟩ :=
    result.analyzeWithAuthoritativeOccurrences_member_refines assignment member
  cases unitEq : base.unit with
  | tetrahedral center =>
      simp [AuthoritativeOccurrenceOverrideJudgment, unitEq] at refined
      rcases refined with retained | judged
      · left
        rw [retained.2]
        exact baseMember
      · exact Or.inr ⟨center, judged⟩
  | doubleBond left right =>
      left
      have outputEq : assignment = base := by
        simpa [AuthoritativeOccurrenceOverrideJudgment, unitEq] using refined
      rw [outputEq]
      exact baseMember
  | axis start finish =>
      left
      have outputEq : assignment = base := by
        simpa [AuthoritativeOccurrenceOverrideJudgment, unitEq] using refined
      rw [outputEq]
      exact baseMember
  | plane atoms =>
      left
      have outputEq : assignment = base := by
        simpa [AuthoritativeOccurrenceOverrideJudgment, unitEq] using refined
      rw [outputEq]
      exact baseMember
  | helix path =>
      left
      have outputEq : assignment = base := by
        simpa [AuthoritativeOccurrenceOverrideJudgment, unitEq] using refined
      rw [outputEq]
      exact baseMember
  | polyhedron center =>
      left
      have outputEq : assignment = base := by
        simpa [AuthoritativeOccurrenceOverrideJudgment, unitEq] using refined
      rw [outputEq]
      exact baseMember

/-- Independent final-assignment meanings currently established at the authority-facing public
boundary: the complete ordinary tetrahedral and ordinary-double-bond judgments, plus an
authoritative occurrence override when the latter replaces a native tetrahedral result. -/
def IndependentlyJudgedAuthorityFacingStereoAssignment
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment) : Prop :=
  IndependentlyJudgedNormalizedStereoAssignment result assignment ∨
    ∃ center, AuthoritativeOccurrenceStereoAssignmentJudgment result center assignment

/-- Sharp public-output boundary.  Every authority-facing result has an independent final
assignment judgment.  A retained native result inherits the complete normalized judgment; an
authoritative tetrahedral override carries its occurrence judgment directly. -/
theorem ChemistryNormalizationResult.analyzeWithAuthoritativeOccurrences_member_judged
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment)
    (member : assignment ∈ result.analyzeWithAuthoritativeOccurrences) :
    IndependentlyJudgedAuthorityFacingStereoAssignment result assignment := by
  obtain ⟨base, baseMember, refined⟩ :=
    result.analyzeWithAuthoritativeOccurrences_member_refines assignment member
  have baseMeaning : IndependentlyJudgedNormalizedStereoAssignment result base :=
    (mem_analyzeNormalized_iff_independently_judged result base).mp baseMember |>.2.2
  have retained (outputEq : assignment = base) :
      IndependentlyJudgedAuthorityFacingStereoAssignment result assignment := by
    subst assignment
    exact Or.inl baseMeaning
  cases unitEq : base.unit with
  | tetrahedral center =>
      simp [AuthoritativeOccurrenceOverrideJudgment, unitEq] at refined
      rcases refined with unchanged | authoritative
      · exact retained unchanged.2
      · exact Or.inr ⟨center, authoritative⟩
  | doubleBond left right =>
      exact retained (by
        simpa [AuthoritativeOccurrenceOverrideJudgment, unitEq] using refined)
  | axis start finish =>
      exact retained (by
        simpa [AuthoritativeOccurrenceOverrideJudgment, unitEq] using refined)
  | plane atoms =>
      exact retained (by
        simpa [AuthoritativeOccurrenceOverrideJudgment, unitEq] using refined)
  | helix path =>
      exact retained (by
        simpa [AuthoritativeOccurrenceOverrideJudgment, unitEq] using refined)
  | polyhedron center =>
      exact retained (by
        simpa [AuthoritativeOccurrenceOverrideJudgment, unitEq] using refined)

/-- Compatibility form of the former judged-or-residual boundary.  The residual type is empty;
the preceding theorem is the sharp statement. -/
theorem ChemistryNormalizationResult.analyzeWithAuthoritativeOccurrences_member_judged_or_residual
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment)
    (member : assignment ∈ result.analyzeWithAuthoritativeOccurrences) :
    IndependentlyJudgedAuthorityFacingStereoAssignment result assignment ∨
      NormalizedStereoAnalysisResidualAssignment result assignment := by
  exact Or.inl
    (result.analyzeWithAuthoritativeOccurrences_member_judged assignment member)

/-- Certified-input specialization at the public authority-facing graph entry point. -/
theorem analyzeCertifiedNormalized_member_native_or_authoritative_judged
    (certified : CertifiedChemistryNormalizationResult) (assignment : StereoAssignment)
    (member : assignment ∈ analyzeCertifiedNormalized certified) :
    (assignment ∈ analyzeNormalized certified.result) ∨
      ∃ center,
        AuthoritativeOccurrenceStereoAssignmentJudgment certified.result center assignment := by
  exact certified.result.analyzeWithAuthoritativeOccurrences_member_native_or_judged
    assignment (by simpa [analyzeCertifiedNormalized] using member)

/-- Certified specialization: every emitted authority-facing assignment is independently judged. -/
theorem analyzeCertifiedNormalized_member_judged
    (certified : CertifiedChemistryNormalizationResult) (assignment : StereoAssignment)
    (member : assignment ∈ analyzeCertifiedNormalized certified) :
    IndependentlyJudgedAuthorityFacingStereoAssignment certified.result assignment := by
  exact certified.result.analyzeWithAuthoritativeOccurrences_member_judged
    assignment (by simpa [analyzeCertifiedNormalized] using member)

/-- Compatibility specialization of the former judged-or-residual boundary. -/
theorem analyzeCertifiedNormalized_member_judged_or_residual
    (certified : CertifiedChemistryNormalizationResult) (assignment : StereoAssignment)
    (member : assignment ∈ analyzeCertifiedNormalized certified) :
    IndependentlyJudgedAuthorityFacingStereoAssignment certified.result assignment ∨
      NormalizedStereoAnalysisResidualAssignment certified.result assignment := by
  exact certified.result.analyzeWithAuthoritativeOccurrences_member_judged_or_residual
    assignment (by simpa [analyzeCertifiedNormalized] using member)







theorem analyzeCertifiedNormalized_member_exactConstitutionalMolecule_and_assignmentJudgment
    (certified : CertifiedChemistryNormalizationResult) (assignment : StereoAssignment)
    (member : assignment ∈ analyzeCertifiedNormalized certified)
    (discovery : AuthoritativeCIPDiscovery.Discovery
      certified.result.parsed.withExplicitHydrogens) :
    CertifiedAuthoritativeSupportedMoleculeCIPConformance
        certified.result.parsed.withExplicitHydrogens discovery ∧
      ((assignment ∈ analyzeNormalized certified.result) ∨
        ∃ center,
          AuthoritativeOccurrenceStereoAssignmentJudgment certified.result center assignment) := by
  constructor
  · exact certifiedAuthoritativeSupportedMoleculeCIPConforms_blueBookP92 discovery
      (certified.result.parsed.withExplicitHydrogens_preserves_stereochemicalAdmissible
        certified.stereochemicalAdmissible)
      certified.expandedRule2MassesKnown
  · exact analyzeCertifiedNormalized_member_native_or_authoritative_judged
      certified assignment member



theorem analyzeCertifiedNormalized_member_exactConstitutionalMolecule_and_judged
    (certified : CertifiedChemistryNormalizationResult) (assignment : StereoAssignment)
    (member : assignment ∈ analyzeCertifiedNormalized certified)
    (discovery : AuthoritativeCIPDiscovery.Discovery
      certified.result.parsed.withExplicitHydrogens) :
    CertifiedAuthoritativeSupportedMoleculeCIPConformance
        certified.result.parsed.withExplicitHydrogens discovery ∧
      IndependentlyJudgedAuthorityFacingStereoAssignment certified.result assignment := by
  constructor
  · exact certifiedAuthoritativeSupportedMoleculeCIPConforms_blueBookP92 discovery
      (certified.result.parsed.withExplicitHydrogens_preserves_stereochemicalAdmissible
        certified.stereochemicalAdmissible)
      certified.expandedRule2MassesKnown
  · exact analyzeCertifiedNormalized_member_judged certified assignment member


theorem analyzeCertifiedNormalized_member_exactConstitutionalMolecule_and_judged_or_residual
    (certified : CertifiedChemistryNormalizationResult) (assignment : StereoAssignment)
    (member : assignment ∈ analyzeCertifiedNormalized certified)
    (discovery : AuthoritativeCIPDiscovery.Discovery
      certified.result.parsed.withExplicitHydrogens) :
    CertifiedAuthoritativeSupportedMoleculeCIPConformance
        certified.result.parsed.withExplicitHydrogens discovery ∧
      (IndependentlyJudgedAuthorityFacingStereoAssignment certified.result assignment ∨
        NormalizedStereoAnalysisResidualAssignment certified.result assignment) := by
  constructor
  · exact certifiedAuthoritativeSupportedMoleculeCIPConforms_blueBookP92 discovery
      (certified.result.parsed.withExplicitHydrogens_preserves_stereochemicalAdmissible
        certified.stereochemicalAdmissible)
      certified.expandedRule2MassesKnown
  · exact analyzeCertifiedNormalized_member_judged_or_residual certified assignment member

end TetraStereo.OneCenter
