import TetraStereo.OneCenter.CIPAuthoritativeLonePairDigraphConformance
import TetraStereo.OneCenter.CIPAuthoritativeConformance
import TetraStereo.OneCenter.CIPStereogenicPerceptionConformance

set_option autoImplicit false

namespace TetraStereo.OneCenter

open AuthoritativeCIPDiscovery

/-- Combined independent certificate for the width-unbounded primitive, molecule-digraph, and
supported stereogenic-perception layers. -/
structure AuthoritativeSupportedMoleculeCIPConformance
    (mol : RawMolecule) (discovery : AuthoritativeCIPDiscovery.Discovery mol) : Prop where
  primitiveRules : AuthoritativePrimitiveP92Conformance
  moleculeDigraph : BlueBookP92.Digraph.AuthoritativeMoleculeConformance mol discovery
  perception : SupportedPerceptionConformance

/-- Proof-carrying result of executing the authoritative molecule-wide discovery. -/
structure ExecutableAuthoritativeSupportedMoleculeCIPConformance (mol : RawMolecule) where
  discovery : AuthoritativeCIPDiscovery.Discovery mol
  conformance : AuthoritativeSupportedMoleculeCIPConformance mol discovery

/-- Strengthened authority bundle for mass-certified chemistry. Besides the existing primitive,
digraph, and perception certificates, it proves exact constitutional comparison of every ordered
pair of physical ligand hierarchies and, separately, the stronger all-slot theorem including
atomless lone-pair branches at every discovered center. -/
structure CertifiedAuthoritativeSupportedMoleculeCIPConformance
    (mol : RawMolecule) (discovery : AuthoritativeCIPDiscovery.Discovery mol) : Prop where
  supported : AuthoritativeSupportedMoleculeCIPConformance mol discovery
  exactConstitutionalMolecule :
    BlueBookP92.Digraph.AuthoritativeExactConstitutionalMoleculeConformance mol discovery
  exactAllSlotConstitutionalMolecule :
    BlueBookP92.Digraph.AuthoritativeExactAllSlotConstitutionalMoleculeConformance mol discovery

/-- Proof-carrying result of successful molecule-wide discovery at the strengthened certified
authority boundary. -/
structure ExecutableCertifiedAuthoritativeSupportedMoleculeCIPConformance
    (mol : RawMolecule) where
  discovery : AuthoritativeCIPDiscovery.Discovery mol
  conformance : CertifiedAuthoritativeSupportedMoleculeCIPConformance mol discovery

theorem authoritativeSupportedMoleculeCIPConforms_blueBookP92
    {mol : RawMolecule} (discovery : AuthoritativeCIPDiscovery.Discovery mol)
    (admitted : mol.StereochemicalAdmissible) :
    AuthoritativeSupportedMoleculeCIPConformance mol discovery where
  primitiveRules := authoritativePrimitiveRules_conform_blueBookP92
  moleculeDigraph := discovery.moleculeConformance_of_stereochemicalAdmissible admitted
  perception := supportedPerceptionConforms_blueBookP92

/-- The combined primitive/digraph/perception certificate strengthened by exact molecule-wide
Rules-1a--2 hierarchy conformance. -/
theorem certifiedAuthoritativeSupportedMoleculeCIPConforms_blueBookP92
    {mol : RawMolecule} (discovery : AuthoritativeCIPDiscovery.Discovery mol)
    (admitted : mol.StereochemicalAdmissible) (known : mol.Rule2MassesKnown) :
    CertifiedAuthoritativeSupportedMoleculeCIPConformance mol discovery where
  supported := authoritativeSupportedMoleculeCIPConforms_blueBookP92 discovery admitted
  exactConstitutionalMolecule :=
    discovery.exactConstitutionalMoleculeConformance_of_stereochemicalAdmissible admitted known
  exactAllSlotConstitutionalMolecule :=
    discovery.exactAllSlotConstitutionalMoleculeConformance_of_stereochemicalAdmissible
      admitted known

/-- Execute width-unbounded discovery and attach every currently connected independent P-92
certificate. The option retains operational refusal outside the chemical applicability domain;
`CIPAuthoritativeExecutableConformanceTotality` proves success inside that domain. -/
def executableAuthoritativeSupportedMoleculeCIPConformance?
    (mol : RawMolecule) (admitted : mol.StereochemicalAdmissible) :
    Option (ExecutableAuthoritativeSupportedMoleculeCIPConformance mol) :=
  match AuthoritativeCIPDiscovery.discoverAll? mol with
  | none => none
  | some discovery =>
      some ⟨discovery,
        authoritativeSupportedMoleculeCIPConforms_blueBookP92 discovery admitted⟩

/-- Execute authoritative molecule-wide discovery and attach the strengthened mass-certified
constitutional/perception bundle. -/
def executableCertifiedAuthoritativeSupportedMoleculeCIPConformance?
    (mol : RawMolecule) (admitted : mol.StereochemicalAdmissible)
    (known : mol.Rule2MassesKnown) :
    Option (ExecutableCertifiedAuthoritativeSupportedMoleculeCIPConformance mol) :=
  match AuthoritativeCIPDiscovery.discoverAll? mol with
  | none => none
  | some discovery =>
      some ⟨discovery,
        certifiedAuthoritativeSupportedMoleculeCIPConforms_blueBookP92
          discovery admitted known⟩

@[simp] theorem executableAuthoritativeSupportedMoleculeCIPConformance?_isSome
    (mol : RawMolecule) (admitted : mol.StereochemicalAdmissible) :
    (executableAuthoritativeSupportedMoleculeCIPConformance? mol admitted).isSome =
      AuthoritativeCIPDiscovery.allCentersSucceeded? mol := by
  unfold executableAuthoritativeSupportedMoleculeCIPConformance?
  cases discovered : AuthoritativeCIPDiscovery.discoverAll? mol <;>
    simp [← AuthoritativeCIPDiscovery.discoverAll?_isSome, discovered]

@[simp] theorem executableCertifiedAuthoritativeSupportedMoleculeCIPConformance?_isSome
    (mol : RawMolecule) (admitted : mol.StereochemicalAdmissible)
    (known : mol.Rule2MassesKnown) :
    (executableCertifiedAuthoritativeSupportedMoleculeCIPConformance?
      mol admitted known).isSome = AuthoritativeCIPDiscovery.allCentersSucceeded? mol := by
  unfold executableCertifiedAuthoritativeSupportedMoleculeCIPConformance?
  cases discovered : AuthoritativeCIPDiscovery.discoverAll? mol <;>
    simp [← AuthoritativeCIPDiscovery.discoverAll?_isSome, discovered]

/-- Execute the strengthened certificate on the exact hydrogen-expanded ranking molecule carried
by a certified chemistry-normalization result. -/
def executableCertifiedAuthoritativeSupportedMoleculeCIPConformanceOfCertified?
    (certified : CertifiedChemistryNormalizationResult) :
    Option (ExecutableCertifiedAuthoritativeSupportedMoleculeCIPConformance
      certified.result.parsed.withExplicitHydrogens) :=
  executableCertifiedAuthoritativeSupportedMoleculeCIPConformance?
    certified.result.parsed.withExplicitHydrogens
    (certified.result.parsed.withExplicitHydrogens_preserves_stereochemicalAdmissible
      certified.stereochemicalAdmissible)
    certified.expandedRule2MassesKnown

@[simp] theorem
    executableCertifiedAuthoritativeSupportedMoleculeCIPConformanceOfCertified?_isSome
    (certified : CertifiedChemistryNormalizationResult) :
    (executableCertifiedAuthoritativeSupportedMoleculeCIPConformanceOfCertified?
      certified).isSome =
        AuthoritativeCIPDiscovery.allCentersSucceeded?
          certified.result.parsed.withExplicitHydrogens := by
  exact executableCertifiedAuthoritativeSupportedMoleculeCIPConformance?_isSome _ _ _

/-- Every normalized-analyzer member can execute the authoritative proof-producing wrapper on the
exact admitted hydrogen-expanded ranking graph. -/
def executableAuthoritativeSupportedMoleculeCIPConformanceOfAnalyzeNormalizedMember?
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment)
    (member : assignment ∈ analyzeNormalized result) :
    Option (ExecutableAuthoritativeSupportedMoleculeCIPConformance
      result.parsed.withExplicitHydrogens) :=
  executableAuthoritativeSupportedMoleculeCIPConformance?
    result.parsed.withExplicitHydrogens
    (analyzeNormalized_member_expandedStereochemicalAdmissible result assignment member)

@[simp] theorem
    executableAuthoritativeSupportedMoleculeCIPConformanceOfAnalyzeNormalizedMember?_isSome
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment)
    (member : assignment ∈ analyzeNormalized result) :
    (executableAuthoritativeSupportedMoleculeCIPConformanceOfAnalyzeNormalizedMember?
      result assignment member).isSome =
        AuthoritativeCIPDiscovery.allCentersSucceeded?
          result.parsed.withExplicitHydrogens := by
  exact executableAuthoritativeSupportedMoleculeCIPConformance?_isSome _ _

end TetraStereo.OneCenter
