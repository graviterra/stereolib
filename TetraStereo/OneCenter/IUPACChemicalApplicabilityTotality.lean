import TetraStereo.OneCenter.AuthoritativeLocalizedApplicability
import TetraStereo.OneCenter.IUPACProvisionSemantics

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace IUPACChemicalApplicability

/-!
# Source-backed chemical admission and normative applicability

Structural well-formedness says that an input's finite indices are valid.  It does not say that the
represented entity is chemically admissible, nor that an IUPAC provision applies to it.  This
module introduces the independent boundary needed to state those two decisions without conflating
them with parser success or analyzer success.

The boundary is deliberately evidence-parametric.  A source family supplies a frozen citation and
digest, executable classifiers, exact reflection theorems, and an external source-fidelity proof.
This module proves totality *of an adopted classifier*; it does not manufacture a universal
chemical oracle or silently identify admissibility with structural well-formedness.
-/






structure FrozenApplicabilitySource where
  normativeSource : IUPACNormativeSource
  citation : String
  artifactSha256 : String
  citationDeclared : citation ≠ ""
  artifactSha256Exact : normativeSource.sha256? = some artifactSha256
  scope : Finset IUPACNormativeProvision
  scopeExact : scope = (IUPACNormativeProvision.sourceProvisions normativeSource).toFinset
  scopeNonempty : scope.Nonempty
  reviewed : IUPACNormativeProvision.ReviewedProvisionBatch scope
  corpus : IUPACNormativeProvision.FrozenProvisionCorpus
  compiler : IUPACNormativeProvision.ScopedProvisionCompiler corpus scope
  referenceFaithful :
    IUPACNormativeProvision.ProvisionBatchReferenceFaithful reviewed corpus
  conformantAnchor : IUPACNormativeProvision
  conformantAnchorMember : conformantAnchor ∈ scope
  conformantAnchorEvidence :
    (compiler.spec conformantAnchor conformantAnchorMember).disposition.IsConformant

/-- Independent, executable policy for chemical admission and provision-relative applicability.

`applicableOnlyIfChemicallyAdmissible` prevents a provision from being reported applicable outside
the policy's chemical domain.  The two reflection fields make both classifications executable
without defining either proposition in terms of a downstream stereochemical analyzer. -/
structure Policy where
  ChemicallyAdmissible : AuthoritativeChemicalInput → Prop
  chemicallyAdmissible? : AuthoritativeChemicalInput → Bool
  chemicalReflection : ∀ input,
    chemicallyAdmissible? input = true ↔ ChemicallyAdmissible input
  Applicable : IUPACNormativeProvision → AuthoritativeChemicalInput → Prop
  applicable? : IUPACNormativeProvision → AuthoritativeChemicalInput → Bool
  applicabilityReflection : ∀ provision input,
    applicable? provision input = true ↔ Applicable provision input
  applicableOnlyIfChemicallyAdmissible : ∀ provision input,
    Applicable provision input → ChemicallyAdmissible input

/-- Evidence-bearing result of the executable chemical-admission classifier. -/
inductive ChemicalAdmissionDecision (policy : Policy)
    (input : AuthoritativeChemicalInput) : Type where
  | admitted (evidence : policy.ChemicallyAdmissible input)
  | rejected (evidence : ¬ policy.ChemicallyAdmissible input)

/-- Chemical rejection, provision applicability, and provision inapplicability remain distinct
terminal outcomes.  In particular, `notApplicable` is meaningful only inside the admitted chemical
domain. -/
inductive ProvisionApplicabilityDecision (policy : Policy)
    (provision : IUPACNormativeProvision) (input : AuthoritativeChemicalInput) : Type where
  | chemicallyRejected (evidence : ¬ policy.ChemicallyAdmissible input)
  | applicable
      (chemical : policy.ChemicallyAdmissible input)
      (evidence : policy.Applicable provision input)
  | notApplicable
      (chemical : policy.ChemicallyAdmissible input)
      (evidence : ¬ policy.Applicable provision input)

namespace Policy

/-- Every finite semantic input receives an evidence-bearing chemical-admission decision from an
adopted executable policy. -/
def classifyChemicalAdmission (policy : Policy) (input : AuthoritativeChemicalInput) :
    ChemicalAdmissionDecision policy input := by
  by_cases checked : policy.chemicallyAdmissible? input = true
  · exact .admitted ((policy.chemicalReflection input).mp checked)
  · exact .rejected fun admitted =>
      checked ((policy.chemicalReflection input).mpr admitted)

/-- Every provision/input pair receives exactly the appropriately typed terminal classification.
This is constructive totality through the two reflected Boolean classifiers, not excluded middle
over an arbitrary source proposition. -/
def classifyProvisionApplicability (policy : Policy)
    (provision : IUPACNormativeProvision) (input : AuthoritativeChemicalInput) :
    ProvisionApplicabilityDecision policy provision input := by
  by_cases chemicalChecked : policy.chemicallyAdmissible? input = true
  · have chemical := (policy.chemicalReflection input).mp chemicalChecked
    by_cases applicableChecked : policy.applicable? provision input = true
    · exact .applicable chemical
        ((policy.applicabilityReflection provision input).mp applicableChecked)
    · exact .notApplicable chemical fun applicable =>
        applicableChecked ((policy.applicabilityReflection provision input).mpr applicable)
  · exact .chemicallyRejected fun chemical =>
      chemicalChecked ((policy.chemicalReflection input).mpr chemical)

/-- A positive executable applicability result also reflects to chemical admission. -/
theorem chemicallyAdmissible_of_applicable?_eq_true (policy : Policy)
    (provision : IUPACNormativeProvision) (input : AuthoritativeChemicalInput)
    (applicable : policy.applicable? provision input = true) :
    policy.ChemicallyAdmissible input :=
  policy.applicableOnlyIfChemicallyAdmissible provision input
    ((policy.applicabilityReflection provision input).mp applicable)

end Policy

/-- Project-owned fidelity relation between an executable policy and the exact independently
reviewed corpus embedded in a frozen source scope.  Applicability agrees pointwise on every scoped
row, and the policy is explicitly inapplicable outside that scope. -/
structure PolicyFaithful (source : FrozenApplicabilitySource) (policy : Policy) : Prop where
  chemicalExact : ∀ input,
    policy.ChemicallyAdmissible input ↔ source.corpus.ChemicallyAdmitted input
  applicabilityExact : ∀ {provision}, provision ∈ source.scope → ∀ input,
    policy.Applicable provision input ↔
      (source.corpus.reference provision).Applicable input
  outsideScopeInapplicable : ∀ {provision}, provision ∉ source.scope → ∀ input,
    ¬ policy.Applicable provision input

/-- A policy becomes source-backed only when it refines the project's exact audited corpus and
also carries the source-family's separate external fidelity evidence.  Choosing a vacuous external
predicate cannot bypass `policyFaithful`. -/
structure SourceBackedPackage (source : FrozenApplicabilitySource)
    (SourceFaithful : FrozenApplicabilitySource → Policy → Prop) where
  policy : Policy
  policyFaithful : PolicyFaithful source policy
  externalSourceFaithful : SourceFaithful source policy

namespace SourceBackedPackage

/-- A source-backed package cannot hide an empty chemical-admission domain: nonemptiness follows
from the conformant disposition of any row in its required nonempty audited scope. -/
theorem exists_chemicallyAdmissible
    {source : FrozenApplicabilitySource}
    {SourceFaithful : FrozenApplicabilitySource → Policy → Prop}
    (package : SourceBackedPackage source SourceFaithful) :
    ∃ input, package.policy.ChemicallyAdmissible input := by
  obtain ⟨input, observation, chemical, _applicable, _judges⟩ :=
    IUPACNormativeProvision.ProvisionDisposition.nonvacuous_of_conformant
      source.conformantAnchorEvidence
  exact ⟨input, (package.policyFaithful.chemicalExact input).mpr chemical⟩

/-- On every scoped provision, executable applicability is exactly the audited frozen-corpus
relation; the external evidence field cannot replace this equality. -/
theorem applicable_iff_corpus
    {source : FrozenApplicabilitySource}
    {SourceFaithful : FrozenApplicabilitySource → Policy → Prop}
    (package : SourceBackedPackage source SourceFaithful)
    {provision : IUPACNormativeProvision} (member : provision ∈ source.scope)
    (input : AuthoritativeChemicalInput) :
    package.policy.Applicable provision input ↔
      (source.corpus.reference provision).Applicable input :=
  package.policyFaithful.applicabilityExact member input

/-- Rows outside the frozen source scope cannot acquire applicability through the global policy
index. -/
theorem not_applicable_outside_scope
    {source : FrozenApplicabilitySource}
    {SourceFaithful : FrozenApplicabilitySource → Policy → Prop}
    (package : SourceBackedPackage source SourceFaithful)
    {provision : IUPACNormativeProvision} (outside : provision ∉ source.scope)
    (input : AuthoritativeChemicalInput) :
    ¬ package.policy.Applicable provision input :=
  package.policyFaithful.outsideScopeInapplicable outside input

end SourceBackedPackage

/-- Evidence that one source-backed provision predicate is exactly the applicability domain of the
existing localized pair-bond analyzer.  This adapter is intentionally a separate proof: the generic
package never assumes all IUPAC provisions share that restricted domain. -/
structure LocalizedCIPAdapter {source : FrozenApplicabilitySource}
    {SourceFaithful : FrozenApplicabilitySource → Policy → Prop}
    (package : SourceBackedPackage source SourceFaithful)
    (provision : IUPACNormativeProvision) where
  provisionMember : provision ∈ source.scope
  applicable_iff_localizedCIPApplicable : ∀ input,
    package.policy.Applicable provision input ↔ input.LocalizedCIPApplicable

namespace LocalizedCIPAdapter

/-- The independently characterized localized analyzer succeeds exactly when the adapted
source-backed provision predicate applies. -/
theorem localizedAnalyzer_isSome_iff_applicable
    {source : FrozenApplicabilitySource}
    {SourceFaithful : FrozenApplicabilitySource → Policy → Prop}
    {package : SourceBackedPackage source SourceFaithful}
    {provision : IUPACNormativeProvision}
    (adapter : LocalizedCIPAdapter package provision)
    (input : AuthoritativeChemicalInput) :
    input.analyzeSupportedLocalizedStereochemistry?.isSome = true ↔
      package.policy.Applicable provision input := by
  rw [input.analyzeSupportedLocalizedStereochemistry?_isSome,
    ← adapter.applicable_iff_localizedCIPApplicable input]

/-- Positive source-backed applicability yields an actual localized analysis, rather than merely
an abstract decidability result. -/
theorem exists_localizedAnalysis_of_applicable
    {source : FrozenApplicabilitySource}
    {SourceFaithful : FrozenApplicabilitySource → Policy → Prop}
    {package : SourceBackedPackage source SourceFaithful}
    {provision : IUPACNormativeProvision}
    (adapter : LocalizedCIPAdapter package provision)
    (input : AuthoritativeChemicalInput)
    (applicable : package.policy.Applicable provision input) :
    ∃ analysis, input.analyzeSupportedLocalizedStereochemistry? = some analysis := by
  apply input.exists_supportedLocalized_analysis_of_applicable
  exact (adapter.applicable_iff_localizedCIPApplicable input).mp applicable

/-- Exact localized adaptation forces the policy to chemically admit every source in the existing
localized analyzer domain. -/
theorem chemicallyAdmissible_of_localizedCIPApplicable
    {source : FrozenApplicabilitySource}
    {SourceFaithful : FrozenApplicabilitySource → Policy → Prop}
    {package : SourceBackedPackage source SourceFaithful}
    {provision : IUPACNormativeProvision}
    (adapter : LocalizedCIPAdapter package provision)
    (input : AuthoritativeChemicalInput)
    (localized : input.LocalizedCIPApplicable) :
    package.policy.ChemicallyAdmissible input :=
  package.policy.applicableOnlyIfChemicallyAdmissible provision input
    ((adapter.applicable_iff_localizedCIPApplicable input).mpr localized)

end LocalizedCIPAdapter
end IUPACChemicalApplicability
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.IUPACChemicalApplicability.Policy.classifyChemicalAdmission
assert_kernel_only TetraStereo.OneCenter.IUPACChemicalApplicability.Policy.classifyProvisionApplicability
assert_kernel_only TetraStereo.OneCenter.IUPACChemicalApplicability.Policy.chemicallyAdmissible_of_applicable?_eq_true
assert_kernel_only TetraStereo.OneCenter.IUPACChemicalApplicability.SourceBackedPackage.exists_chemicallyAdmissible
assert_kernel_only TetraStereo.OneCenter.IUPACChemicalApplicability.SourceBackedPackage.applicable_iff_corpus
assert_kernel_only TetraStereo.OneCenter.IUPACChemicalApplicability.SourceBackedPackage.not_applicable_outside_scope
assert_kernel_only TetraStereo.OneCenter.IUPACChemicalApplicability.LocalizedCIPAdapter.localizedAnalyzer_isSome_iff_applicable
assert_kernel_only TetraStereo.OneCenter.IUPACChemicalApplicability.LocalizedCIPAdapter.exists_localizedAnalysis_of_applicable
assert_kernel_only TetraStereo.OneCenter.IUPACChemicalApplicability.LocalizedCIPAdapter.chemicallyAdmissible_of_localizedCIPApplicable
