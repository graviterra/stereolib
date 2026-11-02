import TetraStereo.OneCenter.CIPAuthoritativeMoleculeDiscoveryTotality
import TetraStereo.OneCenter.CIPAuthoritativeStereoAssignmentConformance
import TetraStereo.OneCenter.ExplicitHydrogenMancudeKekulePreservation

set_option autoImplicit false

namespace TetraStereo.OneCenter

noncomputable section

open AuthoritativeCIPMancudeTotality










/-- The executable primitive/digraph/perception authority wrapper returns throughout the chemical
applicability domain. -/
theorem executableAuthoritativeSupportedMoleculeCIPConformance?_exists_of_chemical_applicability
    (mol : RawMolecule) (admitted : mol.StereochemicalAdmissible)
    (valence : mol.ValenceOK) (kekule : LocalizedMancudeKekuleAdmissible mol) :
    ∃ execution,
      executableAuthoritativeSupportedMoleculeCIPConformance? mol admitted = some execution := by
  obtain ⟨discovery, discovered⟩ :=
    AuthoritativeCIPDiscovery.discoverAll?_exists_of_chemical_applicability
      mol admitted.1.1 admitted.1.2 admitted.2 valence kekule
  let execution : ExecutableAuthoritativeSupportedMoleculeCIPConformance mol :=
    { discovery := discovery
      conformance := authoritativeSupportedMoleculeCIPConforms_blueBookP92 discovery admitted }
  refine ⟨execution, ?_⟩
  unfold executableAuthoritativeSupportedMoleculeCIPConformance?
  rw [discovered]

/-- The strengthened executable authority wrapper also returns and carries exact constitutional
conformance when Rule-2 masses are known. -/
theorem executableCertifiedAuthoritativeSupportedMoleculeCIPConformance?_exists_of_chemical_applicability
    (mol : RawMolecule) (admitted : mol.StereochemicalAdmissible)
    (valence : mol.ValenceOK) (kekule : LocalizedMancudeKekuleAdmissible mol)
    (known : mol.Rule2MassesKnown) :
    ∃ execution,
      executableCertifiedAuthoritativeSupportedMoleculeCIPConformance?
        mol admitted known = some execution := by
  obtain ⟨discovery, discovered⟩ :=
    AuthoritativeCIPDiscovery.discoverAll?_exists_of_chemical_applicability
      mol admitted.1.1 admitted.1.2 admitted.2 valence kekule
  let execution : ExecutableCertifiedAuthoritativeSupportedMoleculeCIPConformance mol :=
    { discovery := discovery
      conformance := certifiedAuthoritativeSupportedMoleculeCIPConforms_blueBookP92
        discovery admitted known }
  refine ⟨execution, ?_⟩
  unfold executableCertifiedAuthoritativeSupportedMoleculeCIPConformance?
  rw [discovered]






theorem analyzeCertifiedNormalized_member_exists_totalAuthoritativeConformance_and_judged_of_chemical_applicability
    (certified : CertifiedChemistryNormalizationResult) (assignment : StereoAssignment)
    (member : assignment ∈ analyzeCertifiedNormalized certified)
    (kekule : LocalizedMancudeKekuleAdmissible certified.result.parsed) :
    ∃ execution,
      executableCertifiedAuthoritativeSupportedMoleculeCIPConformanceOfCertified? certified =
          some execution ∧
        IndependentlyJudgedAuthorityFacingStereoAssignment certified.result assignment := by
  have expandedAdmitted :
      certified.result.parsed.withExplicitHydrogens.StereochemicalAdmissible :=
    certified.result.parsed.withExplicitHydrogens_preserves_stereochemicalAdmissible
      certified.stereochemicalAdmissible
  have expandedValence : certified.result.parsed.withExplicitHydrogens.ValenceOK :=
    certified.result.parsed.withExplicitHydrogens_preserves_valenceOK
      certified.admissible.1 certified.valenceOK
  have expandedKekule :
      LocalizedMancudeKekuleAdmissible certified.result.parsed.withExplicitHydrogens :=
    certified.result.parsed.withExplicitHydrogens_preserves_localizedMancudeKekuleAdmissible
      certified.stereochemicalAdmissible kekule
  obtain ⟨execution, executed⟩ :=
    executableCertifiedAuthoritativeSupportedMoleculeCIPConformance?_exists_of_chemical_applicability
      certified.result.parsed.withExplicitHydrogens expandedAdmitted expandedValence expandedKekule
      certified.expandedRule2MassesKnown
  refine ⟨execution, ?_, analyzeCertifiedNormalized_member_judged certified assignment member⟩
  simpa [executableCertifiedAuthoritativeSupportedMoleculeCIPConformanceOfCertified?] using executed

end


end TetraStereo.OneCenter
