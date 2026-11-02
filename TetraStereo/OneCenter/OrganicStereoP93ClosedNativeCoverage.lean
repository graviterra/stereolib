import TetraStereo.OneCenter.OrganicStereoAllAuthorityEntries
import TetraStereo.OneCenter.OrganicStereoCertifiedSourceCoreCompletion
import TetraStereo.OneCenter.IUPACRemaining71P93ClosedProductionFamilies
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Closed native coverage of all 56 P-93 production rows

This module integrates the actual closed production family
`Remaining71P93ClosedProductionRow` (11 outer constructors, exactly 56 rows) with the actual
existing native union `OrganicStereoAllAuthorityEntries.NativeEntry` and the constructed certified
source core `OrganicStereoCertifiedSourceCoreCompletion.constructedCore`.

For an arbitrary certified source `certified`, an arbitrary row `row : Remaining71P93ClosedProductionRow`
and an arbitrary actual row observation together with its actual reviewed `Judged` certificate at
`certified.input`, the module

* constructs a row-indexed native payload `RowNativePayload policies certified row`,
* proves `decodeRow policies core enumeration row (encodeRow ... row observation judged) =
  some observation` for **all 56 actual constructors** by explicit case analysis (never by an
  enum count and never by assuming the input is already native); the decoder takes only the
  constructed core, the fixed enumeration, the policies and the native payload, never the
  original certified source,
* proves the same for an ordered heterogeneous list `List (Sigma row, judged observation)` whose
  tags are retained and whose order and multiplicity are literal,
* and displays the reconstructed common source
  `recoveredSource (fixedCore certified) (fixedEnumeration certified) = certified.input`.

All 56 rows are admitted into the actual existing `RawEntry` union and encoded by the actual
existing `encodeEntry`, so every family codec, the general and relational-variant codecs, and the
acyclic codec are reused, not duplicated.  The two bare acyclic rows (`acyclicCenters`,
`ordinaryDoubleBonds`) are carried by the actual `SourceAcyclicObservation.bareAssignment` /
`AcyclicObservation.bareAssignment` constructor, which holds exactly their
`P93AcyclicAuthorityAssignment` with its own `ValidFor` and no fabricated placement.

No caller core tie, no boundedness hypothesis, no inverse hypothesis and no "already native"
premise is assumed: every bound is derived from the row's own `Judged` certificate and the
certified source's structural certificate, and every inverse used is a proven upstream theorem.

Endpoint honesty: the theorems are universal over the declared 56 production rows and over
arbitrary certified sources carrying a row-specific `Judged` observation.  They do not assert
that any particular source satisfies any row, and they do not claim English organic-completeness
beyond this declared family.
-/

namespace TetraStereo.OneCenter

open IUPACNormativeProvision
open OrganicStereoMolecularEvidenceAssembly
open OrganicStereoAllAuthorityEntries
open OrganicStereoAuthorityMixedSourceAssembly
open OrganicStereoP93AcyclicIngress
open OrganicStereoNoncarbonTetrahedralIngress
open OrganicStereoMonocyclicRingAssemblyIngress
open OrganicStereoFusedVonBaeyerIngress
open OrganicStereoCyclophaneAuthorityIngress
open OrganicStereoSpiroAuthorityIngress
open OrganicStereoP93GeneralAuthorityIngress
open OrganicStereoRelationalFullereneVariantIngress

namespace OrganicStereoP93ClosedNativeCoverage

noncomputable section

/-! ## Policies and the constructed core -/

/-- The actual `AllAuthorityPolicies` assembled from the reviewed `Remaining71ReviewedPolicies`.
Every field is a projection; no policy is manufactured or weakened. -/
abbrev AllPolicies (policies : Remaining71ReviewedPolicies) : AllAuthorityPolicies where
  policy94 := policies.p94
  policy93 := policies.p93Acyclic
  noncarbonPolicy := policies.p93Noncarbon
  monocyclicPolicy := policies.p93Cyclic.monocyclic
  assemblyPolicy := policies.p93Cyclic.ringAssembly
  fusedPolicy := policies.p93Cyclic.fused
  vonBaeyerPolicy := policies.p93Cyclic.vonBaeyer
  cyclophanePolicy := policies.p93Cyclic.cyclophane
  spiroPolicy := policies.p93Cyclic.spiro
  generalPolicy := policies.p93General
  fullerenePolicy := policies.p93Cyclic.fullerene
  relationalPolicy := policies.p93Cyclic.relationalFullerene
  coupledPolicy := policies.p93Cyclic.coupledRingChain

/-- The actual constructed core of the certified source. -/
abbrev fixedCore (certified : CertifiedAuthoritativeChemicalInput) :
    OrganicMolecularEvidence (Fin certified.input.molecule.atomCount) :=
  OrganicStereoCertifiedSourceCoreCompletion.constructedCore certified

/-- The actual fixed atom enumeration of the constructed core. -/
abbrev fixedEnumeration (certified : CertifiedAuthoritativeChemicalInput) :
    Fin certified.input.molecule.atomCount ≃
      Fin (Fintype.card (Fin certified.input.molecule.atomCount)) :=
  OrganicStereoCertifiedSourceCoreCompletion.constructedEnumeration certified

/-- The reconstructed common source of the constructed core is exactly the certified input. -/
theorem fixedSource (certified : CertifiedAuthoritativeChemicalInput) :
    OrganicStereoAllAuthorityEntries.recoveredSource (fixedCore certified)
        (fixedEnumeration certified) = certified.input :=
  OrganicStereoCertifiedSourceCoreCompletion.recoveredSource_constructedCore certified

/-- The reconstructed common source is structurally well formed. -/
theorem fixedSource_wellFormed (certified : CertifiedAuthoritativeChemicalInput) :
    (OrganicStereoAllAuthorityEntries.recoveredSource (fixedCore certified)
      (fixedEnumeration certified)).StructurallyWellFormed :=
  OrganicStereoCertifiedSourceCoreCompletion.recoveredSource_constructedCore_structurallyWellFormed
    certified

/-- The actual acyclic source tie reconstructed from the constructed core. -/
def fixedTie (certified : CertifiedAuthoritativeChemicalInput) :
    AcyclicSourceTie (Fin certified.input.molecule.atomCount) (fixedEnumeration certified) :=
  decodedAcyclicTie (fixedCore certified) (fixedEnumeration certified)
    (fixedSource_wellFormed certified).2.1

/-- The reconstructed tie's source is the certified input. -/
theorem fixedTie_source (certified : CertifiedAuthoritativeChemicalInput) :
    (fixedTie certified).source = certified.input := by
  simpa only [fixedTie, decodedAcyclicTie] using fixedSource certified

/-! ## The actual raw and native unions at the constructed core -/

/-- The actual existing raw union at the constructed core, with all unrelated type parameters
instantiated at `PUnit`. -/
abbrev ClosedRaw (policies : Remaining71ReviewedPolicies)
    (certified : CertifiedAuthoritativeChemicalInput) : Type :=
  RawEntry (Fin certified.input.molecule.atomCount)
    PUnit PUnit PUnit PUnit PUnit PUnit PUnit PUnit PUnit PUnit
    (AllPolicies policies) (fixedCore certified) (fixedEnumeration certified)

/-- The actual existing native union at the constructed core. -/
abbrev ClosedNative (policies : Remaining71ReviewedPolicies)
    (certified : CertifiedAuthoritativeChemicalInput) : Type :=
  NativeEntry (Fin certified.input.molecule.atomCount)
    PUnit PUnit PUnit PUnit PUnit PUnit PUnit PUnit PUnit PUnit
    (AllPolicies policies) (fixedCore certified) (fixedEnumeration certified)

/-- The row-indexed native payload family.  All 56 rows use the same actual native union: the two
bare acyclic rows are carried by the actual `SourceAcyclicObservation.bareAssignment` /
`AcyclicObservation.bareAssignment` constructor, so there is no row-specific escape type. -/
abbrev RowNativePayload (policies : Remaining71ReviewedPolicies)
    (certified : CertifiedAuthoritativeChemicalInput)
    (_row : Remaining71P93ClosedProductionRow) : Type :=
  ClosedNative policies certified

/-- The raw-side payload family.  All 56 rows enter the same actual raw union. -/
abbrev RawRowPayload (policies : Remaining71ReviewedPolicies)
    (certified : CertifiedAuthoritativeChemicalInput)
    (_row : Remaining71P93ClosedProductionRow) : Type :=
  ClosedRaw policies certified

/-! ## The exact upstream entry inverse at the fixed core -/

/-- The exact `encodeEntry`/`decodeEntry` inverse specialised to the constructed core.  This is
the upstream theorem, not a new assumption. -/
theorem decodeEntry_encodeEntry_fixed (policies : Remaining71ReviewedPolicies)
    (certified : CertifiedAuthoritativeChemicalInput) (entry : ClosedRaw policies certified) :
    decodeEntry (fixedCore certified) (fixedEnumeration certified)
        (encodeEntry (fixedCore certified) (fixedEnumeration certified)
          (fixedSource_wellFormed certified) entry) = entry :=
  OrganicStereoAllAuthorityEntries.decodeEntry_encodeEntry
    (V := Fin certified.input.molecule.atomCount)
    (LigandId := PUnit) (LigandKind := PUnit) (FragmentId := PUnit) (FragmentKind := PUnit)
    (State := PUnit) (Framework := PUnit) (BaseName := PUnit) (Numbering := PUnit)
    (Locant := PUnit) (Prefix := PUnit)
    (policies := AllPolicies policies)
    (core := fixedCore certified) (enumeration := fixedEnumeration certified)
    (source_well_formed := fixedSource_wellFormed certified) (entry := entry)

/-- Exact raw admission of one tagged acyclic observation at the reconstructed tie.  The validity
is transported along the proven tie-source equality, not assumed. -/
def acyclicRaw (policies : Remaining71ReviewedPolicies)
    (certified : CertifiedAuthoritativeChemicalInput)
    (observation : SourceAcyclicObservation policies.p93Acyclic)
    (valid : observation.ValidFor certified.input) :
    ClosedRaw policies certified :=
  .acyclic (fixedTie certified) rfl rfl rfl observation (by
    rw [fixedTie_source certified]
    exact valid)

/-! ## Raw admission of all 56 rows -/

/-- Admit the actual row observation and its actual `Judged` certificate into the actual raw
union.  Every branch keeps its actual carrier tag; the two bare acyclic rows use the actual
`.bareAssignment` constructor with their own assignment validity. -/
def rawEncode (policies : Remaining71ReviewedPolicies)
    (certified : CertifiedAuthoritativeChemicalInput) :
    (row : Remaining71P93ClosedProductionRow) →
    (observation : (row.reference policies).Observation) →
    (row.reference policies).Judges certified.input observation →
      RawRowPayload policies certified row
  | .fullerene .generalMethodology, observation, judged =>
      .fullereneMethodology observation (by
        rw [fixedSource certified]
        exact judged)
  | .fullerene .inherentParentChirality, observation, judged =>
      .relationalVariants (.handed observation) (by
        rw [fixedSource certified]
        exact judged.2.1)
  | .fullerene .inherentSubstitutionChirality, observation, judged =>
      .relationalVariants (.handed observation) (by
        rw [fixedSource certified]
        exact judged.2.1)
  | .fullerene .noninherentSubstitutionChirality, observation, judged =>
      .relationalVariants (.handed observation) (by
        rw [fixedSource certified]
        exact judged.2.1)
  | .fullerene .chiralSubstituents, observation, judged =>
      .relationalVariants (.type4 observation) (by
        rw [fixedSource certified]
        exact judged)
  | .fullerene .superimposedStereogenicElements, observation, judged =>
      .relationalVariants (.superimposed observation) (by
        rw [fixedSource certified]
        exact judged)
  | .noncarbon .otherElementTetrahedra, observation, judged =>
      .noncarbon (.tetrahedral observation) (by
        rw [fixedSource certified]
        exact judged)
  | .noncarbon .otherElementGeneralMethodology, observation, judged =>
      .noncarbon (.citation observation) (by
        rw [fixedSource certified]
        exact judged)
  | .noncarbon .azaniumPhosphanium, observation, judged =>
      .noncarbon (.onic observation) (by
        rw [fixedSource certified]
        exact judged)
  | .noncarbon .aminePhosphaneOxides, observation, judged =>
      .noncarbon (.oxide observation) (by
        rw [fixedSource certified]
        exact judged.1)
  | .noncarbon .phosphatesPhosphonates, observation, judged =>
      .noncarbon (.phosphorusOxo observation) (by
        rw [fixedSource certified]
        exact judged.1)
  | .noncarbon .sulfatesSulfonates, observation, judged =>
      .noncarbon (.chalcogenOxo observation) (by
        rw [fixedSource certified]
        exact judged.1)
  | .noncarbon .group14Noncarbon, observation, judged =>
      .noncarbon (.group14 observation) (by
        rw [fixedSource certified]
        exact judged.1)
  | .general .absoluteConfiguration, observation, judged =>
      .general (.absolute observation) (by
        rw [fixedSource certified]
        exact judged)
  | .general .relativeConfiguration, observation, judged =>
      .general (.relative observation) (by
        rw [fixedSource certified]
        exact judged)
  | .general .mixedAbsoluteRelativeConfiguration, observation, judged =>
      .general (.mixedAbsoluteRelative observation) (by
        rw [fixedSource certified]
        exact judged)
  | .general .racemates, observation, judged =>
      .general (.racemate observation) (by
        rw [fixedSource certified]
        exact judged)
  | .general .ambo, observation, judged =>
      .general (.ambo observation) (by
        rw [fixedSource certified]
        exact judged)
  | .monocyclic .cyclicConfigurations, observation, judged =>
      .cyclic (.monocyclicGeneral observation) (by
        rw [fixedSource certified]
        exact judged)
  | .monocyclic .monocyclicAbsoluteCenters, observation, judged =>
      .cyclic (.monocyclicCenter observation) (by
        rw [fixedSource certified]
        exact judged.1)
  | .monocyclic .monocyclicAchiralCenters, observation, judged =>
      .cyclic (.monocyclicCenter observation) (by
        rw [fixedSource certified]
        exact judged.1)
  | .monocyclic .monocyclicCisTrans, observation, judged =>
      .cyclic (.monocyclicCisTrans observation) (by
        rw [fixedSource certified]
        exact judged)
  | .monocyclic .monocyclicRCT, observation, judged =>
      .cyclic (.monocyclicRCT observation) (by
        rw [fixedSource certified]
        exact judged)
  | .monocyclic .unsaturatedMonocycles, observation, judged =>
      .cyclic (.monocyclicUnsaturation observation) (by
        rw [fixedSource certified]
        exact judged.1)
  | .monocyclic .cyclicDoubleBonds, observation, judged =>
      .cyclic (.monocyclicDoubleBond observation) (by
        rw [fixedSource certified]
        exact judged)
  | .monocyclic .exocyclicDoubleBondEZ, observation, judged =>
      .cyclic (.monocyclicExocyclic observation) (by
        rw [fixedSource certified]
        exact judged.1)
  | .monocyclic .exocyclicDoubleBondOther, observation, judged =>
      .cyclic (.monocyclicExocyclic observation) (by
        rw [fixedSource certified]
        exact judged.1)
  | .vonBaeyer .vonBaeyerCIPCenters, observation, judged =>
      .fused (.vonBaeyerCenter observation) (by
        rw [fixedSource certified]
        exact judged.1)
  | .vonBaeyer .vonBaeyerEndoExoSynAnti, observation, judged =>
      .fused (.vonBaeyerBridgeOrientation observation) (by
        rw [fixedSource certified]
        exact judged)
  | .vonBaeyer .vonBaeyerCisTrans, observation, judged =>
      .fused (.vonBaeyerBridgeheadRelative observation) (by
        rw [fixedSource certified]
        exact judged)
  | .vonBaeyer .vonBaeyerDoubleBonds, observation, judged =>
      .fused (.vonBaeyerUnsaturation observation) (by
        rw [fixedSource certified]
        exact judged)
  | .ringAssembly .axes, observation, judged =>
      .cyclic (.ringAssemblyAxes observation) (by
        rw [fixedSource certified]
        exact judged)
  | .ringAssembly .centers, observation, judged =>
      .cyclic (.ringAssemblyCenters observation) (by
        rw [fixedSource certified]
        exact judged)
  | .ringAssembly .doubleBonds, observation, judged =>
      .cyclic (.ringAssemblyDoubleBonds observation) (by
        rw [fixedSource certified]
        exact judged)
  | .acyclic .acyclicCenters, observation, judged =>
      acyclicRaw policies certified (.bareAssignment observation) judged.1
  | .acyclic .singleAcyclicCenter, observation, judged =>
      acyclicRaw policies certified (.singleCenter observation) judged
  | .acyclic .multipleDescriptorsOneCenter, observation, judged =>
      acyclicRaw policies certified (.multipleCenterDescriptors observation) judged
  | .acyclic .prefixComponentCenters, observation, judged =>
      acyclicRaw policies certified (.prefixComponent observation) judged.1
  | .acyclic .ordinaryDoubleBonds, observation, judged =>
      acyclicRaw policies certified (.bareAssignment observation) judged.1
  | .acyclic .doubleBondEZCisTrans, observation, judged =>
      acyclicRaw policies certified (.doubleBond observation) judged
  | .acyclic .multipleDoubleBonds, observation, judged =>
      acyclicRaw policies certified (.multipleDoubleBond observation) judged
  | .acyclic .heteroatomDoubleBonds, observation, judged =>
      acyclicRaw policies certified (.heteroDoubleBond observation) judged.1
  | .acyclic .evenCumulenes, observation, judged =>
      acyclicRaw policies certified (.evenCumulene observation) judged
  | .acyclic .oddCumulenes, observation, judged =>
      acyclicRaw policies certified (.oddCumulene observation) judged
  | .acyclic .multipleAcyclicStereogenicUnits, observation, judged =>
      acyclicRaw policies certified (.multipleUnits observation) judged
  | .spiro .spiroXabcd, observation, judged =>
      .spiro (.xabcd observation) (by
        rw [fixedSource certified]
        exact judged)
  | .spiro .spiroXabab, observation, judged =>
      .spiro (.xabab observation) (by
        rw [fixedSource certified]
        exact judged)
  | .spiro .spiroDoubleBonds, observation, judged =>
      .spiro (.doubleBond observation) (by
        rw [fixedSource certified]
        exact judged)
  | .spiro .spiroAxialChirality, observation, judged =>
      .spiro (.axial observation) (by
        rw [fixedSource certified]
        exact judged)
  | .spiroNontetrahedral, observation, judged =>
      .spiro (.polyhedral observation) (by
        rw [fixedSource certified]
        exact judged)
  | .fusedCyclophane .fusedBridgedCIP, observation, judged =>
      .fused (.fusedCIP observation) (by
        rw [fixedSource certified]
        exact judged)
  | .fusedCyclophane .cisoidTransoid, observation, judged =>
      .fused (.fusedRelation observation) (by
        rw [fixedSource certified]
        exact judged)
  | .fusedCyclophane .cyclophanePlanes, observation, judged =>
      .cyclophane (.plane observation) (by
        rw [fixedSource certified]
        exact judged)
  | .fusedCyclophane .cyclophaneCenters, observation, judged =>
      .cyclophane (.center observation) (by
        rw [fixedSource certified]
        exact judged)
  | .fusedCyclophane .cyclophaneDoubleBonds, observation, judged =>
      .cyclophane (.doubleBond observation) (by
        rw [fixedSource certified]
        exact judged)
  | .coupledRingChain .configurations, observation, judged =>
      .coupled observation (by
        rw [fixedSource certified]
        exact judged)

/-! ## Encoding all 56 rows -/

/-- Encode one judged row into its row-indexed native payload at the constructed core.  Every one
of the 56 rows enters the same actual raw union through the 56-case `rawEncode` and is encoded by
the actual `encodeEntry`; the two bare acyclic rows are admitted as `.bareAssignment`. -/
def encodeRow (policies : Remaining71ReviewedPolicies)
    (certified : CertifiedAuthoritativeChemicalInput) :
    (row : Remaining71P93ClosedProductionRow) →
    (observation : (row.reference policies).Observation) →
    (row.reference policies).Judges certified.input observation →
      RowNativePayload policies certified row
  | row, observation, judged =>
      encodeEntry (fixedCore certified) (fixedEnumeration certified)
        (fixedSource_wellFormed certified)
        (rawEncode policies certified row observation judged)

/-! ## Decoding all 56 rows -/

/-- Decode one row-indexed native payload.  The row tag is an explicit input.  Every branch first
decodes the actual native payload through the actual `decodeEntry`, then checks the inner carrier
tag expected by this row. Incompatible carrier tags yield `none`; distinct rows can share a
carrier. This is readback using the retained row tag, not a validator of the row's `Judges`.

The decoder is source-independent: it is parameterised by the constructed core and the fixed atom
enumeration only (both of which are indices of the native union type), never by the original
`CertifiedAuthoritativeChemicalInput`. -/
def decodeRow (policies : Remaining71ReviewedPolicies)
    {V : Type} [DecidableEq V] [Fintype V]
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (row : Remaining71P93ClosedProductionRow) →
      NativeEntry V PUnit PUnit PUnit PUnit PUnit PUnit PUnit PUnit PUnit PUnit
        (AllPolicies policies) core enumeration →
        Option ((row.reference policies).Observation)
  | .fullerene .generalMethodology, payload =>
      match decodeEntry core enumeration payload with
      | .fullereneMethodology observation _ => some observation
      | _ => none
  | .fullerene .inherentParentChirality, payload =>
      match decodeEntry core enumeration payload with
      | .relationalVariants observations _ =>
          match observations with
          | .handed observation =>
              if observation.base.assignment.chiralityType =
                  .inherentlyChiralParent then some observation else none
          | _ => none
      | _ => none
  | .fullerene .inherentSubstitutionChirality, payload =>
      match decodeEntry core enumeration payload with
      | .relationalVariants observations _ =>
          match observations with
          | .handed observation =>
              if observation.base.assignment.chiralityType =
                  .inherentlyChiralSubstitutionPattern then some observation else none
          | _ => none
      | _ => none
  | .fullerene .noninherentSubstitutionChirality, payload =>
      match decodeEntry core enumeration payload with
      | .relationalVariants observations _ =>
          match observations with
          | .handed observation =>
              if observation.base.assignment.chiralityType =
                  .noninherentlyChiralSubstitutionPattern then some observation else none
          | _ => none
      | _ => none
  | .fullerene .chiralSubstituents, payload =>
      match decodeEntry core enumeration payload with
      | .relationalVariants observations _ =>
          match observations with
          | .type4 observation => some observation
          | _ => none
      | _ => none
  | .fullerene .superimposedStereogenicElements, payload =>
      match decodeEntry core enumeration payload with
      | .relationalVariants observations _ =>
          match observations with
          | .superimposed observation => some observation
          | _ => none
      | _ => none
  | .noncarbon .otherElementTetrahedra, payload =>
      match decodeEntry core enumeration payload with
      | .noncarbon observations _ =>
          match observations with
          | .tetrahedral observation => some observation
          | _ => none
      | _ => none
  | .noncarbon .otherElementGeneralMethodology, payload =>
      match decodeEntry core enumeration payload with
      | .noncarbon observations _ =>
          match observations with
          | .citation observation => some observation
          | _ => none
      | _ => none
  | .noncarbon .azaniumPhosphanium, payload =>
      match decodeEntry core enumeration payload with
      | .noncarbon observations _ =>
          match observations with
          | .onic observation => some observation
          | _ => none
      | _ => none
  | .noncarbon .aminePhosphaneOxides, payload =>
      match decodeEntry core enumeration payload with
      | .noncarbon observations _ =>
          match observations with
          | .oxide observation => some observation
          | _ => none
      | _ => none
  | .noncarbon .phosphatesPhosphonates, payload =>
      match decodeEntry core enumeration payload with
      | .noncarbon observations _ =>
          match observations with
          | .phosphorusOxo observation => some observation
          | _ => none
      | _ => none
  | .noncarbon .sulfatesSulfonates, payload =>
      match decodeEntry core enumeration payload with
      | .noncarbon observations _ =>
          match observations with
          | .chalcogenOxo observation => some observation
          | _ => none
      | _ => none
  | .noncarbon .group14Noncarbon, payload =>
      match decodeEntry core enumeration payload with
      | .noncarbon observations _ =>
          match observations with
          | .group14 observation => some observation
          | _ => none
      | _ => none
  | .general .absoluteConfiguration, payload =>
      match decodeEntry core enumeration payload with
      | .general observations _ =>
          match observations with
          | .absolute observation => some observation
          | _ => none
      | _ => none
  | .general .relativeConfiguration, payload =>
      match decodeEntry core enumeration payload with
      | .general observations _ =>
          match observations with
          | .relative observation => some observation
          | _ => none
      | _ => none
  | .general .mixedAbsoluteRelativeConfiguration, payload =>
      match decodeEntry core enumeration payload with
      | .general observations _ =>
          match observations with
          | .mixedAbsoluteRelative observation => some observation
          | _ => none
      | _ => none
  | .general .racemates, payload =>
      match decodeEntry core enumeration payload with
      | .general observations _ =>
          match observations with
          | .racemate observation => some observation
          | _ => none
      | _ => none
  | .general .ambo, payload =>
      match decodeEntry core enumeration payload with
      | .general observations _ =>
          match observations with
          | .ambo observation => some observation
          | _ => none
      | _ => none
  | .monocyclic .cyclicConfigurations, payload =>
      match decodeEntry core enumeration payload with
      | .cyclic observations _ =>
          match observations with
          | .monocyclicGeneral observation => some observation
          | _ => none
      | _ => none
  | .monocyclic .monocyclicAbsoluteCenters, payload =>
      match decodeEntry core enumeration payload with
      | .cyclic observations _ =>
          match observations with
          | .monocyclicCenter observation => some observation
          | _ => none
      | _ => none
  | .monocyclic .monocyclicAchiralCenters, payload =>
      match decodeEntry core enumeration payload with
      | .cyclic observations _ =>
          match observations with
          | .monocyclicCenter observation => some observation
          | _ => none
      | _ => none
  | .monocyclic .monocyclicCisTrans, payload =>
      match decodeEntry core enumeration payload with
      | .cyclic observations _ =>
          match observations with
          | .monocyclicCisTrans observation => some observation
          | _ => none
      | _ => none
  | .monocyclic .monocyclicRCT, payload =>
      match decodeEntry core enumeration payload with
      | .cyclic observations _ =>
          match observations with
          | .monocyclicRCT observation => some observation
          | _ => none
      | _ => none
  | .monocyclic .unsaturatedMonocycles, payload =>
      match decodeEntry core enumeration payload with
      | .cyclic observations _ =>
          match observations with
          | .monocyclicUnsaturation observation => some observation
          | _ => none
      | _ => none
  | .monocyclic .cyclicDoubleBonds, payload =>
      match decodeEntry core enumeration payload with
      | .cyclic observations _ =>
          match observations with
          | .monocyclicDoubleBond observation => some observation
          | _ => none
      | _ => none
  | .monocyclic .exocyclicDoubleBondEZ, payload =>
      match decodeEntry core enumeration payload with
      | .cyclic observations _ =>
          match observations with
          | .monocyclicExocyclic observation => some observation
          | _ => none
      | _ => none
  | .monocyclic .exocyclicDoubleBondOther, payload =>
      match decodeEntry core enumeration payload with
      | .cyclic observations _ =>
          match observations with
          | .monocyclicExocyclic observation => some observation
          | _ => none
      | _ => none
  | .vonBaeyer .vonBaeyerCIPCenters, payload =>
      match decodeEntry core enumeration payload with
      | .fused observations _ =>
          match observations with
          | .vonBaeyerCenter observation => some observation
          | _ => none
      | _ => none
  | .vonBaeyer .vonBaeyerEndoExoSynAnti, payload =>
      match decodeEntry core enumeration payload with
      | .fused observations _ =>
          match observations with
          | .vonBaeyerBridgeOrientation observation => some observation
          | _ => none
      | _ => none
  | .vonBaeyer .vonBaeyerCisTrans, payload =>
      match decodeEntry core enumeration payload with
      | .fused observations _ =>
          match observations with
          | .vonBaeyerBridgeheadRelative observation => some observation
          | _ => none
      | _ => none
  | .vonBaeyer .vonBaeyerDoubleBonds, payload =>
      match decodeEntry core enumeration payload with
      | .fused observations _ =>
          match observations with
          | .vonBaeyerUnsaturation observation => some observation
          | _ => none
      | _ => none
  | .ringAssembly .axes, payload =>
      match decodeEntry core enumeration payload with
      | .cyclic observations _ =>
          match observations with
          | .ringAssemblyAxes observation => some observation
          | _ => none
      | _ => none
  | .ringAssembly .centers, payload =>
      match decodeEntry core enumeration payload with
      | .cyclic observations _ =>
          match observations with
          | .ringAssemblyCenters observation => some observation
          | _ => none
      | _ => none
  | .ringAssembly .doubleBonds, payload =>
      match decodeEntry core enumeration payload with
      | .cyclic observations _ =>
          match observations with
          | .ringAssemblyDoubleBonds observation => some observation
          | _ => none
      | _ => none
  | .acyclic .acyclicCenters, payload =>
      match decodeEntry core enumeration payload with
      | .acyclic _ _ _ _ observations _ =>
          match observations with
          | .bareAssignment assignment => some assignment
          | _ => none
      | _ => none
  | .acyclic .singleAcyclicCenter, payload =>
      match decodeEntry core enumeration payload with
      | .acyclic _ _ _ _ observations _ =>
          match observations with
          | .singleCenter observation => some observation
          | _ => none
      | _ => none
  | .acyclic .multipleDescriptorsOneCenter, payload =>
      match decodeEntry core enumeration payload with
      | .acyclic _ _ _ _ observations _ =>
          match observations with
          | .multipleCenterDescriptors observation => some observation
          | _ => none
      | _ => none
  | .acyclic .prefixComponentCenters, payload =>
      match decodeEntry core enumeration payload with
      | .acyclic _ _ _ _ observations _ =>
          match observations with
          | .prefixComponent observation => some observation
          | _ => none
      | _ => none
  | .acyclic .ordinaryDoubleBonds, payload =>
      match decodeEntry core enumeration payload with
      | .acyclic _ _ _ _ observations _ =>
          match observations with
          | .bareAssignment assignment => some assignment
          | _ => none
      | _ => none
  | .acyclic .doubleBondEZCisTrans, payload =>
      match decodeEntry core enumeration payload with
      | .acyclic _ _ _ _ observations _ =>
          match observations with
          | .doubleBond observation => some observation
          | _ => none
      | _ => none
  | .acyclic .multipleDoubleBonds, payload =>
      match decodeEntry core enumeration payload with
      | .acyclic _ _ _ _ observations _ =>
          match observations with
          | .multipleDoubleBond observation => some observation
          | _ => none
      | _ => none
  | .acyclic .heteroatomDoubleBonds, payload =>
      match decodeEntry core enumeration payload with
      | .acyclic _ _ _ _ observations _ =>
          match observations with
          | .heteroDoubleBond observation => some observation
          | _ => none
      | _ => none
  | .acyclic .evenCumulenes, payload =>
      match decodeEntry core enumeration payload with
      | .acyclic _ _ _ _ observations _ =>
          match observations with
          | .evenCumulene observation => some observation
          | _ => none
      | _ => none
  | .acyclic .oddCumulenes, payload =>
      match decodeEntry core enumeration payload with
      | .acyclic _ _ _ _ observations _ =>
          match observations with
          | .oddCumulene observation => some observation
          | _ => none
      | _ => none
  | .acyclic .multipleAcyclicStereogenicUnits, payload =>
      match decodeEntry core enumeration payload with
      | .acyclic _ _ _ _ observations _ =>
          match observations with
          | .multipleUnits observation => some observation
          | _ => none
      | _ => none
  | .spiro .spiroXabcd, payload =>
      match decodeEntry core enumeration payload with
      | .spiro observations _ =>
          match observations with
          | .xabcd observation => some observation
          | _ => none
      | _ => none
  | .spiro .spiroXabab, payload =>
      match decodeEntry core enumeration payload with
      | .spiro observations _ =>
          match observations with
          | .xabab observation => some observation
          | _ => none
      | _ => none
  | .spiro .spiroDoubleBonds, payload =>
      match decodeEntry core enumeration payload with
      | .spiro observations _ =>
          match observations with
          | .doubleBond observation => some observation
          | _ => none
      | _ => none
  | .spiro .spiroAxialChirality, payload =>
      match decodeEntry core enumeration payload with
      | .spiro observations _ =>
          match observations with
          | .axial observation => some observation
          | _ => none
      | _ => none
  | .spiroNontetrahedral, payload =>
      match decodeEntry core enumeration payload with
      | .spiro observations _ =>
          match observations with
          | .polyhedral observation => some observation
          | _ => none
      | _ => none
  | .fusedCyclophane .fusedBridgedCIP, payload =>
      match decodeEntry core enumeration payload with
      | .fused observations _ =>
          match observations with
          | .fusedCIP observation => some observation
          | _ => none
      | _ => none
  | .fusedCyclophane .cisoidTransoid, payload =>
      match decodeEntry core enumeration payload with
      | .fused observations _ =>
          match observations with
          | .fusedRelation observation => some observation
          | _ => none
      | _ => none
  | .fusedCyclophane .cyclophanePlanes, payload =>
      match decodeEntry core enumeration payload with
      | .cyclophane observations _ =>
          match observations with
          | .plane observation => some observation
          | _ => none
      | _ => none
  | .fusedCyclophane .cyclophaneCenters, payload =>
      match decodeEntry core enumeration payload with
      | .cyclophane observations _ =>
          match observations with
          | .center observation => some observation
          | _ => none
      | _ => none
  | .fusedCyclophane .cyclophaneDoubleBonds, payload =>
      match decodeEntry core enumeration payload with
      | .cyclophane observations _ =>
          match observations with
          | .doubleBond observation => some observation
          | _ => none
      | _ => none
  | .coupledRingChain .configurations, payload =>
      match decodeEntry core enumeration payload with
      | .coupled observation _ => some observation
      | _ => none

/-! ## Per-row readback for all 56 actual constructors -/

/-- **Per-row readback.**  For every one of the 56 actual closed production rows, every actual
row observation and every actual `Judged` certificate at the certified input, encoding into the
row-indexed native payload and decoding with the retained row tag returns the original
observation.  The proof is an explicit 56-way case analysis over the actual constructors. -/
theorem decodeRow_encodeRow (policies : Remaining71ReviewedPolicies)
    (certified : CertifiedAuthoritativeChemicalInput) :
    (row : Remaining71P93ClosedProductionRow) →
    (observation : (row.reference policies).Observation) →
    (judged : (row.reference policies).Judges certified.input observation) →
      decodeRow policies (fixedCore certified) (fixedEnumeration certified) row
        (encodeRow policies certified row observation judged) = some observation := by
  intro row
  cases row with
  | fullerene child =>
      cases child with
      | generalMethodology =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | inherentParentChirality =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
          rw [judged.2.2]
          simp
      | inherentSubstitutionChirality =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
          rw [judged.2.2]
          simp
      | noninherentSubstitutionChirality =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
          rw [judged.2.2]
          simp
      | chiralSubstituents =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | superimposedStereogenicElements =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
  | noncarbon child =>
      cases child with
      | otherElementTetrahedra =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | otherElementGeneralMethodology =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | azaniumPhosphanium =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | aminePhosphaneOxides =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | phosphatesPhosphonates =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | sulfatesSulfonates =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | group14Noncarbon =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
  | general child =>
      cases child with
      | absoluteConfiguration =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | relativeConfiguration =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | mixedAbsoluteRelativeConfiguration =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | racemates =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | ambo =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
  | monocyclic child =>
      cases child with
      | cyclicConfigurations =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | monocyclicAbsoluteCenters =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | monocyclicAchiralCenters =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | monocyclicCisTrans =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | monocyclicRCT =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | unsaturatedMonocycles =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | cyclicDoubleBonds =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | exocyclicDoubleBondEZ =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | exocyclicDoubleBondOther =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
  | vonBaeyer child =>
      cases child with
      | vonBaeyerCIPCenters =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | vonBaeyerEndoExoSynAnti =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | vonBaeyerCisTrans =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | vonBaeyerDoubleBonds =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
  | ringAssembly child =>
      cases child with
      | axes =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | centers =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | doubleBonds =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
  | acyclic child =>
      cases child with
      | acyclicCenters =>
          intro observation judged
          simp only [encodeRow, rawEncode, acyclicRaw, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | singleAcyclicCenter =>
          intro observation judged
          simp only [encodeRow, rawEncode, acyclicRaw, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | multipleDescriptorsOneCenter =>
          intro observation judged
          simp only [encodeRow, rawEncode, acyclicRaw, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | prefixComponentCenters =>
          intro observation judged
          simp only [encodeRow, rawEncode, acyclicRaw, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | ordinaryDoubleBonds =>
          intro observation judged
          simp only [encodeRow, rawEncode, acyclicRaw, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | doubleBondEZCisTrans =>
          intro observation judged
          simp only [encodeRow, rawEncode, acyclicRaw, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | multipleDoubleBonds =>
          intro observation judged
          simp only [encodeRow, rawEncode, acyclicRaw, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | heteroatomDoubleBonds =>
          intro observation judged
          simp only [encodeRow, rawEncode, acyclicRaw, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | evenCumulenes =>
          intro observation judged
          simp only [encodeRow, rawEncode, acyclicRaw, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | oddCumulenes =>
          intro observation judged
          simp only [encodeRow, rawEncode, acyclicRaw, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | multipleAcyclicStereogenicUnits =>
          intro observation judged
          simp only [encodeRow, rawEncode, acyclicRaw, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
  | spiro child =>
      cases child with
      | spiroXabcd =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | spiroXabab =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | spiroDoubleBonds =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | spiroAxialChirality =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
  | spiroNontetrahedral =>
      intro observation judged
      simp only [encodeRow, rawEncode, decodeRow,
        decodeEntry_encodeEntry_fixed policies certified]
  | fusedCyclophane child =>
      cases child with
      | fusedBridgedCIP =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | cisoidTransoid =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | cyclophanePlanes =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | cyclophaneCenters =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
      | cyclophaneDoubleBonds =>
          intro observation judged
          simp only [encodeRow, rawEncode, decodeRow,
            decodeEntry_encodeEntry_fixed policies certified]
  | coupledRingChain child =>
      cases child
      intro observation judged
      simp only [encodeRow, rawEncode, decodeRow,
        decodeEntry_encodeEntry_fixed policies certified]

/-! ## The two decisive row endpoints -/

/-- **Single-row native recovery at the constructed core.**  For an arbitrary certified source,
an arbitrary declared row, an arbitrary actual row observation and an arbitrary actual `Judged`
certificate, some row-indexed native payload decodes back to exactly that observation, and the
constructed common source is exactly the certified input. -/
theorem closed_native_constructedCore_recovery
    (policies : Remaining71ReviewedPolicies)
    (certified : CertifiedAuthoritativeChemicalInput)
    (row : Remaining71P93ClosedProductionRow)
    (observation : (row.reference policies).Observation)
    (judged : (row.reference policies).Judges certified.input observation) :
    OrganicStereoAllAuthorityEntries.recoveredSource (fixedCore certified)
        (fixedEnumeration certified) = certified.input ∧
      ∃ payload : RowNativePayload policies certified row,
        decodeRow policies (fixedCore certified) (fixedEnumeration certified) row payload =
          some observation :=
  ⟨fixedSource certified,
    ⟨encodeRow policies certified row observation judged,
      decodeRow_encodeRow policies certified row observation judged⟩⟩

/-! ## Ordered heterogeneous judged row lists -/

/-- One retained row tag together with the row's actual observation. -/
abbrev RowObservation (policies : Remaining71ReviewedPolicies) : Type :=
  Sigma fun row : Remaining71P93ClosedProductionRow => (row.reference policies).Observation

/-- An ordered heterogeneous list of judged rows with their retained tags. -/
abbrev JudgedRowList (policies : Remaining71ReviewedPolicies)
    (certified : CertifiedAuthoritativeChemicalInput) : Type :=
  List (Sigma fun row : Remaining71P93ClosedProductionRow =>
    { observation : (row.reference policies).Observation //
      (row.reference policies).Judges certified.input observation })

/-- Encode an ordered heterogeneous judged row list.  Order, multiplicity and every row tag are
retained; each row uses its own payload family. -/
def encodeRows (policies : Remaining71ReviewedPolicies)
    (certified : CertifiedAuthoritativeChemicalInput) :
    JudgedRowList policies certified →
      List (Sigma fun row : Remaining71P93ClosedProductionRow =>
        RowNativePayload policies certified row)
  | [] => []
  | ⟨row, ⟨observation, judged⟩⟩ :: rest =>
      ⟨row, encodeRow policies certified row observation judged⟩ ::
        encodeRows policies certified rest

/-- Decode an ordered heterogeneous native row list. Decoding is all-or-nothing: an incompatible
carrier tag makes the whole list decode to `none`. Rows sharing a carrier are not distinguished
by a separate judgment check. Like `decodeRow`, the decoder is
source-independent: it is parameterised by the constructed core and the fixed enumeration only. -/
def decodeRows (policies : Remaining71ReviewedPolicies)
    {V : Type} [DecidableEq V] [Fintype V]
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    List (Sigma fun row : Remaining71P93ClosedProductionRow =>
      NativeEntry V PUnit PUnit PUnit PUnit PUnit PUnit PUnit PUnit PUnit PUnit
        (AllPolicies policies) core enumeration) →
      Option (List (RowObservation policies))
  | [] => some []
  | ⟨row, payload⟩ :: rest =>
      match decodeRow policies core enumeration row payload with
      | some observation =>
          match decodeRows policies core enumeration rest with
          | some decoded => some (⟨row, observation⟩ :: decoded)
          | none => none
      | none => none

/-- **Ordered heterogeneous list recovery.**  For every ordered list of judged rows with retained
tags, arbitrary mixtures of rows and arbitrary multiplicity, encoding and then decoding returns
exactly the original tag/observation list. -/
theorem decodeRows_encodeRows (policies : Remaining71ReviewedPolicies)
    (certified : CertifiedAuthoritativeChemicalInput) :
    (rows : JudgedRowList policies certified) →
      decodeRows policies (fixedCore certified) (fixedEnumeration certified)
          (encodeRows policies certified rows) =
        some (rows.map fun entry => ⟨entry.1, entry.2.1⟩)
  | [] => rfl
  | ⟨row, ⟨observation, judged⟩⟩ :: rest => by
      simp only [encodeRows, decodeRows, decodeRow_encodeRow, List.map_cons]
      rw [decodeRows_encodeRows policies certified rest]

/-- **List endpoint with common-source recovery.**  The whole ordered heterogeneous list is
recovered, and the one common constructed source is exactly the certified input. -/
theorem closed_native_rowList_recovery (policies : Remaining71ReviewedPolicies)
    (certified : CertifiedAuthoritativeChemicalInput)
    (rows : JudgedRowList policies certified) :
    OrganicStereoAllAuthorityEntries.recoveredSource (fixedCore certified)
        (fixedEnumeration certified) = certified.input ∧
      decodeRows policies (fixedCore certified) (fixedEnumeration certified)
          (encodeRows policies certified rows) =
        some (rows.map fun entry => ⟨entry.1, entry.2.1⟩) :=
  ⟨fixedSource certified, decodeRows_encodeRows policies certified rows⟩

/-! ## Kernel-authority assertions -/

assert_kernel_only decodeRow_encodeRow
assert_kernel_only decodeRows_encodeRows
assert_kernel_only closed_native_constructedCore_recovery
assert_kernel_only closed_native_rowList_recovery

end

end OrganicStereoP93ClosedNativeCoverage

end TetraStereo.OneCenter
