import TetraStereo.OneCenter.IUPACP94CanonicalSourceProgram
import TetraStereo.OneCenter.IUPACP94NormalizationReadiness

set_option autoImplicit false

/-!
# Generic frozen P-94 source programs

This module closes the arbitrary-policy and normalization-totality boundaries for any finite,
proof-carrying P-94 package program.  It deliberately does not provide a canonical program: the
irreducible claim that particular package records are exact transcriptions of the frozen Blue
Book artifact remains an external controlled-issuance boundary and is not modeled by metadata
strings in this module.

Every policy predicate below is restricted to a record in the same finite program and to the
record's exact `(source, molecule)` key.  In particular, an interior witness is not the old
unrestricted graph predicate: it must be one of the two observations in a listed coordinate pair,
with every field visible at the policy boundary equal to the requested field.
-/

namespace TetraStereo.OneCenter

open BlueBookP94
open BlueBookP94.CoordinateTwistInOut
open BlueBookP94.P94MolecularBicyclicFramework
open IUPACNormativeProvision

/-- One finite source-package record, including the policy-free fact needed by the fixed
normalizer.  This record says nothing about whether the package was transcribed from the intended
normative artifact. -/
structure P94FrozenPackageRecord where
  source : AuthoritativeChemicalInput
  molecule : RawMolecule
  package : P94SourcePackageSchema source molecule
  normalizationReady : molecule.P94NormalizationReady

/-- A homogeneous bundle for one distinguished source entry despite the entry's dependence on
its package ledger. -/
structure P94FrozenDistinguishedEntry where
  record : P94FrozenPackageRecord
  entry : P94SourcePackageEvidenceEntry record.molecule record.package.lonePairLedger

/-- A finite P-94 program.  Package keys are unique, and the distinguished entries cover exactly
the twelve clauses, once each and in source order.  Other compatible evidence entries may remain
inside a package because the package schema itself enforces claim closure. -/
structure P94FrozenSourceProgram where
  packages : List P94FrozenPackageRecord
  packageKeyUnique :
    ∀ first ∈ packages, ∀ second ∈ packages,
      first.source = second.source → first.molecule = second.molecule → first = second
  distinguishedEntries : List P94FrozenDistinguishedEntry
  distinguishedEntriesListed :
    ∀ distinguished ∈ distinguishedEntries,
      distinguished.record ∈ packages ∧
        distinguished.entry ∈ distinguished.record.package.evidenceEntries
  distinguishedClausesExact :
    distinguishedEntries.map (fun distinguished => distinguished.entry.claim.clause) =
      P94Clause.all

namespace P94FrozenSourceProgram

/-- Exact membership at one source/molecule key.  All four policy projections factor through
this single predicate. -/
def PackageAt (program : P94FrozenSourceProgram)
    (source : AuthoritativeChemicalInput) (molecule : RawMolecule)
    (record : P94FrozenPackageRecord) : Prop :=
  record ∈ program.packages ∧ record.source = source ∧ record.molecule = molecule

/-- Key uniqueness makes the finite program a partial function from exact source/molecule keys
to proof-carrying packages. -/
theorem packageAt_unique (program : P94FrozenSourceProgram)
    {source : AuthoritativeChemicalInput} {molecule : RawMolecule}
    {first second : P94FrozenPackageRecord}
    (firstAt : program.PackageAt source molecule first)
    (secondAt : program.PackageAt source molecule second) :
    first = second := by
  exact program.packageKeyUnique first firstAt.1 second secondAt.1
    (firstAt.2.1.trans secondAt.2.1.symm)
    (firstAt.2.2.trans secondAt.2.2.symm)

@[simp] theorem distinguishedEntries_length (program : P94FrozenSourceProgram) :
    program.distinguishedEntries.length = 12 := by
  rw [← P94Clause.all_length, ← program.distinguishedClausesExact, List.length_map]

/-- The exact ordered clause equation yields a concrete listed package entry for every P-94
clause. -/
theorem distinguishedClause_covered (program : P94FrozenSourceProgram)
    (clause : P94Clause) :
    ∃ distinguished ∈ program.distinguishedEntries,
      distinguished.entry.claim.clause = clause ∧
        distinguished.record ∈ program.packages ∧
        distinguished.entry ∈ distinguished.record.package.evidenceEntries := by
  have clauseMember : clause ∈ P94Clause.all := by
    cases clause <;> simp [P94Clause.all]
  rw [← program.distinguishedClausesExact] at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨distinguished, distinguishedMember, clauseExact⟩
  have listed := program.distinguishedEntriesListed distinguished distinguishedMember
  exact ⟨distinguished, distinguishedMember, clauseExact, listed.1, listed.2⟩

/-- Evidence provenance is restricted to an entry of a package at the exact requested key. -/
def EvidenceObserved (program : P94FrozenSourceProgram)
    (source : AuthoritativeChemicalInput) (molecule : RawMolecule)
    (evidence : P94ReviewedEvidence) : Prop :=
  ∃ record : P94FrozenPackageRecord,
    program.PackageAt source molecule record ∧
      ∃ entry ∈ record.package.evidenceEntries, entry.evidence = evidence

/-- Coordinate-pair provenance is restricted to an exact pair stored in a package at the exact
requested key. -/
def InOutCoordinatePairObserved (program : P94FrozenSourceProgram)
    (source : AuthoritativeChemicalInput) (molecule : RawMolecule)
    (first second : P94InOutCoordinateObservation) : Prop :=
  ∃ record : P94FrozenPackageRecord,
    program.PackageAt source molecule record ∧
      ∃ pair ∈ record.package.inOutCoordinatePairs,
        pair.first = first ∧ pair.second = second

/-- Exact policy-visible fields of one listed coordinate observation. -/
def CoordinateObservationFieldsExact
    (observation : P94InOutCoordinateObservation)
    (framework : ThetaFramework) (bridgehead : Nat)
    (spatial : SpatialConfiguration) (interior : CartesianPoint3) : Prop :=
  observation.framework = framework ∧ observation.bridgehead = bridgehead ∧
    observation.spatial = spatial ∧ observation.interior = interior

/-- Interior provenance is tied to one endpoint of one listed pair.  Unlike the earlier schema
projection, this relation cannot accept an unrelated graph-valid point, framework, or spatial
configuration. -/
def InOutInteriorWitness (program : P94FrozenSourceProgram)
    (source : AuthoritativeChemicalInput) (molecule : RawMolecule)
    (unit : P94ConformationUnit) (framework : ThetaFramework) (bridgehead : Nat)
    (spatial : SpatialConfiguration) (interior : CartesianPoint3) : Prop :=
  ∃ record : P94FrozenPackageRecord,
    program.PackageAt source molecule record ∧
      ∃ pair ∈ record.package.inOutCoordinatePairs,
        pair.unit = unit ∧
          (CoordinateObservationFieldsExact pair.first framework bridgehead spatial interior ∨
            CoordinateObservationFieldsExact pair.second framework bridgehead spatial interior)

/-- Electronic provenance is a positive lookup in the ledger of a package at the exact key. -/
def LonePairObserved (program : P94FrozenSourceProgram)
    (source : AuthoritativeChemicalInput) (molecule : RawMolecule) (atom : Nat) : Prop :=
  ∃ record : P94FrozenPackageRecord,
    program.PackageAt source molecule record ∧
      record.package.lonePairLedger.HasLonePairAt atom

/-- Policy compiled solely from one finite frozen program. -/
def policy (program : P94FrozenSourceProgram) : P94AuthorityPolicy where
  EvidenceObserved := program.EvidenceObserved
  InOutCoordinatePairObserved := program.InOutCoordinatePairObserved
  InOutInteriorWitness := program.InOutInteriorWitness
  LonePairObserved := program.LonePairObserved

@[simp] theorem policy_evidenceObserved_iff (program : P94FrozenSourceProgram)
    (source : AuthoritativeChemicalInput) (molecule : RawMolecule)
    (evidence : P94ReviewedEvidence) :
    program.policy.EvidenceObserved source molecule evidence ↔
      ∃ record : P94FrozenPackageRecord,
        program.PackageAt source molecule record ∧
          ∃ entry ∈ record.package.evidenceEntries, entry.evidence = evidence :=
  Iff.rfl

@[simp] theorem policy_coordinatePairObserved_iff (program : P94FrozenSourceProgram)
    (source : AuthoritativeChemicalInput) (molecule : RawMolecule)
    (first second : P94InOutCoordinateObservation) :
    program.policy.InOutCoordinatePairObserved source molecule first second ↔
      ∃ record : P94FrozenPackageRecord,
        program.PackageAt source molecule record ∧
          ∃ pair ∈ record.package.inOutCoordinatePairs,
            pair.first = first ∧ pair.second = second :=
  Iff.rfl

@[simp] theorem policy_interiorWitness_iff (program : P94FrozenSourceProgram)
    (source : AuthoritativeChemicalInput) (molecule : RawMolecule)
    (unit : P94ConformationUnit) (framework : ThetaFramework) (bridgehead : Nat)
    (spatial : SpatialConfiguration) (interior : CartesianPoint3) :
    program.policy.InOutInteriorWitness source molecule unit framework bridgehead spatial interior ↔
      ∃ record : P94FrozenPackageRecord,
        program.PackageAt source molecule record ∧
          ∃ pair ∈ record.package.inOutCoordinatePairs,
            pair.unit = unit ∧
              (CoordinateObservationFieldsExact pair.first framework bridgehead spatial interior ∨
                CoordinateObservationFieldsExact pair.second framework bridgehead spatial interior) :=
  Iff.rfl

@[simp] theorem policy_lonePairObserved_iff (program : P94FrozenSourceProgram)
    (source : AuthoritativeChemicalInput) (molecule : RawMolecule) (atom : Nat) :
    program.policy.LonePairObserved source molecule atom ↔
      ∃ record : P94FrozenPackageRecord,
        program.PackageAt source molecule record ∧
          record.package.lonePairLedger.HasLonePairAt atom :=
  Iff.rfl

/-- Every valid observation is backed by exactly one program package.  This prevents the four
policy projections from silently assembling one authority observation from different packages
sharing a source/molecule key. -/
theorem validFor_unique_package (program : P94FrozenSourceProgram)
    (source : AuthoritativeChemicalInput)
    (observation : P94AuthorityObservation program.policy)
    (valid : observation.ValidFor program.policy source) :
    ∃! record : P94FrozenPackageRecord,
      program.PackageAt source observation.molecule record ∧
        ∃ entry ∈ record.package.evidenceEntries,
          entry.evidence = observation.evidence := by
  rcases valid.2.1 with ⟨record, recordAt, entry, entryMember, evidenceExact⟩
  refine ⟨record, ⟨recordAt, entry, entryMember, evidenceExact⟩, ?_⟩
  intro other otherWitness
  exact program.packageAt_unique otherWitness.1 recordAt

/-- Normalization readiness is not an additional caller assumption: it follows from membership
in the same frozen record that made the observation valid. -/
theorem every_valid_normalizationReady (program : P94FrozenSourceProgram)
    (source : AuthoritativeChemicalInput)
    (observation : P94AuthorityObservation program.policy)
    (valid : observation.ValidFor program.policy source) :
    observation.molecule.P94NormalizationReady := by
  rcases validFor_unique_package program source observation valid with
    ⟨record, recordWitness, _unique⟩
  exact recordWitness.1.2.2 ▸ record.normalizationReady

/-- Strategic closure: every generic frozen program discharges the fixed P-94 normalization
frontier for its compiled policy. -/
theorem fixedNormalizationTotality (program : P94FrozenSourceProgram) :
    P94RemainingFixedNormalizationTotality program.policy := by
  exact p94RemainingFixedNormalizationTotality_of_every_valid_ready program.policy
    program.every_valid_normalizationReady

end P94FrozenSourceProgram

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.P94FrozenSourceProgram.packageAt_unique
assert_kernel_only TetraStereo.OneCenter.P94FrozenSourceProgram.distinguishedClause_covered
assert_kernel_only TetraStereo.OneCenter.P94FrozenSourceProgram.policy_interiorWitness_iff
assert_kernel_only TetraStereo.OneCenter.P94FrozenSourceProgram.validFor_unique_package
assert_kernel_only TetraStereo.OneCenter.P94FrozenSourceProgram.every_valid_normalizationReady
assert_kernel_only TetraStereo.OneCenter.P94FrozenSourceProgram.fixedNormalizationTotality
