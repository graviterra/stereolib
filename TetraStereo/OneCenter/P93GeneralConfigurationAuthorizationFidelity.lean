import TetraStereo.OneCenter.IUPACP93CanonicalObservationCompilerCore
import TetraStereo.OneCenter.IUPACP93CanonicalSourceProgram

set_option autoImplicit false

/-!
# Whole-configuration authorization fidelity for the actual P-93 canonical program

The canonical policy compiler authorizes a general configuration only when it occurs as a
**whole** configuration in the dependent payload of an actual general-clause entry of the frozen
source program:

```
ConfigurationAuthorized source configuration :=
  ∃ entry ∈ program.observations,
    entry.source = source ∧ entry.clause.family = .general ∧
      configuration ∈ P93CanonicalSourceProgram.P93CanonicalClauseObservationEntry.wholeConfigurations entry
```

`observationSourceUnique` makes the `(family, source)` key invert to the entire entry, so the
concrete sources below have exactly one general entry each.  This module states the resulting
authorization/rejection regressions directly against
`P93CanonicalSourceProgram.iupacP93CanonicalSourceProgram`; it does not introduce source grants,
payloads, or correctness hypotheses.

Results:

* generic: for a source with a unique general entry, whole-configuration authorization is exactly
  membership in that entry's typed `wholeConfigurations` list;
* exact absolute source `(2R)-butan-2-ol` rejects the single-center `S` configuration, although the
  weaker per-unit `DescriptorAuthorized` relation accepts `.S` (via the certified mirror action);
* the correlated `(R,R)`/`(S,S)` relative payload rejects both mixed configurations `(R,S)` and
  `(S,R)`;
* the legitimate whole configurations carried by the actual relative, racemate, and ambo payloads
  remain authorized.

All positive facts are obtained from the actual typed payload and actual program-entry membership,
not from an assumed authorization premise.
-/

namespace TetraStereo.OneCenter

open BlueBookP93
open IUPACNormativeProvision

namespace P93GeneralConfigurationAuthorizationFidelity

noncomputable abbrev actualProgram : P93CanonicalSourceProgram :=
  P93CanonicalSourceProgram.iupacP93CanonicalSourceProgram

/-! ## Generic whole-configuration authorization -/

/-- Definitional characterization of whole-configuration authorization: it is exactly occurrence
of the configuration in the `wholeConfigurations` projection of some general entry at the same
source.  No per-unit claim union occurs. -/
theorem configurationAuthorized_iff_wholeConfigurations
    (program : P93CanonicalSourceProgram)
    (source : AuthoritativeChemicalInput)
    (configuration : P93CanonicalGeneralConfiguration) :
    (program.generalPolicy .general).ConfigurationAuthorized source configuration ↔
      ∃ entry ∈ program.observations,
        entry.source = source ∧ entry.clause.family = .general ∧
          configuration ∈ P93CanonicalSourceProgram.P93CanonicalClauseObservationEntry.wholeConfigurations entry := by
  change
    (∃ entry ∈ program.observations,
        entry.source = source ∧ entry.clause.family = .general ∧
          configuration ∈ P93CanonicalSourceProgram.P93CanonicalClauseObservationEntry.wholeConfigurations entry) ↔
      ∃ entry ∈ program.observations,
        entry.source = source ∧ entry.clause.family = .general ∧
          configuration ∈ P93CanonicalSourceProgram.P93CanonicalClauseObservationEntry.wholeConfigurations entry
  exact Iff.rfl

/-- If one actual general entry is the unique general entry at a source, then whole-configuration
authorization at that source is equivalent to membership in the entry's own typed
`wholeConfigurations` list.  This is the generic form of the concrete regressions below. -/
theorem configurationAuthorized_iff_of_uniqueGeneralEntry
    (program : P93CanonicalSourceProgram)
    (source : AuthoritativeChemicalInput)
    (entry : P93CanonicalClauseObservationEntry)
    (entryMem : entry ∈ program.observations)
    (entrySource : entry.source = source)
    (entryFamily : entry.clause.family = .general)
    (unique : ∀ other ∈ program.observations, other.source = source →
      other.clause.family = .general → other = entry)
    (configuration : P93CanonicalGeneralConfiguration) :
    (program.generalPolicy .general).ConfigurationAuthorized source configuration ↔
      configuration ∈ P93CanonicalSourceProgram.P93CanonicalClauseObservationEntry.wholeConfigurations entry := by
  constructor
  · rintro ⟨other, otherMem, otherSource, otherFamily, mem⟩
    have otherEq : other = entry := unique other otherMem otherSource otherFamily
    subst other
    exact mem
  · intro mem
    exact ⟨entry, entryMem, entrySource, entryFamily, mem⟩

/-- Contrapositive form used by the concrete regressions. -/
theorem not_configurationAuthorized_of_uniqueGeneralEntry
    (program : P93CanonicalSourceProgram)
    (source : AuthoritativeChemicalInput)
    (entry : P93CanonicalClauseObservationEntry)
    (entryMem : entry ∈ program.observations)
    (entrySource : entry.source = source)
    (entryFamily : entry.clause.family = .general)
    (unique : ∀ other ∈ program.observations, other.source = source →
      other.clause.family = .general → other = entry)
    {configuration : P93CanonicalGeneralConfiguration}
    (notMem : configuration ∉ P93CanonicalSourceProgram.P93CanonicalClauseObservationEntry.wholeConfigurations entry) :
    ¬ (program.generalPolicy .general).ConfigurationAuthorized source configuration := by
  intro authorized
  exact notMem ((configurationAuthorized_iff_of_uniqueGeneralEntry program source entry
    entryMem entrySource entryFamily unique configuration).1 authorized)

/-- A value distinct from both members of a two-element list is not a member. -/
theorem not_mem_cons_cons_of_ne {α : Type*} {first second value : α}
    (neFirst : value ≠ first) (neSecond : value ≠ second) :
    value ∉ [first, second] := by
  simp [neFirst, neSecond]

/-! ## Actual-program entry membership

`iupacP93CanonicalSourceProgram.observations` is definitionally the audited entry ledger, so the
concrete entries transcribed in the frozen source modules are members of the actual program. -/

@[simp] theorem actualProgram_observations :
    actualProgram.observations = P93CanonicalProgramReadiness.sourceAuditedEntries := rfl

theorem mem_observations_of_mem_generalEntries
    {entry : P93CanonicalClauseObservationEntry}
    (mem : entry ∈ P93CanonicalProgramGeneralComplete.entries) :
    entry ∈ actualProgram.observations := by
  simp only [actualProgram_observations,
    P93CanonicalProgramReadiness.sourceAuditedEntries,
    P93CanonicalProgramReadiness.nonFullereneEntries, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl mem))))

theorem absoluteEntry_mem_observations :
    P93CanonicalProgramGeneral.absoluteEntry ∈ actualProgram.observations := by
  refine mem_observations_of_mem_generalEntries ?_
  simp [P93CanonicalProgramGeneralComplete.entries, P93CanonicalProgramGeneral.entries]

theorem relativeEntry_mem_observations :
    P93CanonicalProgramGeneral.relativeEntry ∈ actualProgram.observations := by
  refine mem_observations_of_mem_generalEntries ?_
  simp [P93CanonicalProgramGeneralComplete.entries, P93CanonicalProgramGeneral.entries]

theorem racemateEntry_mem_observations :
    P93CanonicalProgramGeneral.racemateEntry ∈ actualProgram.observations := by
  refine mem_observations_of_mem_generalEntries ?_
  simp [P93CanonicalProgramGeneralComplete.entries, P93CanonicalProgramGeneral.entries]

theorem amboEntry_mem_observations :
    P93CanonicalProgramGeneralComplete.amboEntry ∈ actualProgram.observations := by
  refine mem_observations_of_mem_generalEntries ?_
  simp [P93CanonicalProgramGeneralComplete.entries, P93CanonicalProgramGeneral.entries]

/-! ## The actual typed payloads and their whole-configuration projections -/

@[simp] theorem absoluteEntry_payload :
    P93CanonicalProgramGeneral.absoluteEntry.observation.payload =
      .general P93CanonicalProgramGeneral.absolutePayload := rfl

@[simp] theorem relativeEntry_payload :
    P93CanonicalProgramGeneral.relativeEntry.observation.payload =
      .general P93CanonicalProgramGeneral.relativePayload := rfl

@[simp] theorem racemateEntry_payload :
    P93CanonicalProgramGeneral.racemateEntry.observation.payload =
      .general P93CanonicalProgramGeneral.racematePayload := rfl

@[simp] theorem amboEntry_payload :
    P93CanonicalProgramGeneralComplete.amboEntry.observation.payload =
      .general P93CanonicalProgramGeneralComplete.amboPayload := rfl

@[simp] theorem wholeConfigurations_absoluteEntry :
    P93CanonicalSourceProgram.P93CanonicalClauseObservationEntry.wholeConfigurations
        P93CanonicalProgramGeneral.absoluteEntry =
      [P93CanonicalProgramGeneral.absoluteConfiguration] := by
  simp [P93CanonicalSourceProgram.P93CanonicalClauseObservationEntry.wholeConfigurations,
    P93CanonicalProgramGeneral.absoluteEntry,
    P93CanonicalProgramGeneral.absoluteObservation,
    P93CanonicalProgramGeneral.absolutePayload,
    P93CanonicalSourceProgram.P93GeneralClausePayload.wholeConfigurations]

@[simp] theorem wholeConfigurations_relativeEntry :
    P93CanonicalSourceProgram.P93CanonicalClauseObservationEntry.wholeConfigurations
        P93CanonicalProgramGeneral.relativeEntry =
      [P93CanonicalProgramGeneral.relativeFirst,
        P93CanonicalProgramGeneral.relativeSecond] := by
  simp [P93CanonicalSourceProgram.P93CanonicalClauseObservationEntry.wholeConfigurations,
    P93CanonicalProgramGeneral.relativeEntry,
    P93CanonicalProgramGeneral.relativeObservation,
    P93CanonicalProgramGeneral.relativePayload,
    P93CanonicalSourceProgram.P93GeneralClausePayload.wholeConfigurations]

@[simp] theorem wholeConfigurations_racemateEntry :
    P93CanonicalSourceProgram.P93CanonicalClauseObservationEntry.wholeConfigurations
        P93CanonicalProgramGeneral.racemateEntry =
      [P93CanonicalProgramGeneral.racemateMixture.first,
        P93CanonicalProgramGeneral.racemateMixture.second] := by
  simp [P93CanonicalSourceProgram.P93CanonicalClauseObservationEntry.wholeConfigurations,
    P93CanonicalProgramGeneral.racemateEntry,
    P93CanonicalProgramGeneral.racemateObservation,
    P93CanonicalProgramGeneral.racematePayload,
    P93CanonicalProgramGeneral.racemateMixture,
    P93CanonicalSourceProgram.P93GeneralClausePayload.wholeConfigurations]

@[simp] theorem wholeConfigurations_amboEntry :
    P93CanonicalSourceProgram.P93CanonicalClauseObservationEntry.wholeConfigurations
        P93CanonicalProgramGeneralComplete.amboEntry =
      [P93CanonicalProgramGeneralComplete.amboMixture.first,
        P93CanonicalProgramGeneralComplete.amboMixture.second] := by
  simp [P93CanonicalSourceProgram.P93CanonicalClauseObservationEntry.wholeConfigurations,
    P93CanonicalProgramGeneralComplete.amboEntry,
    P93CanonicalProgramGeneralComplete.amboObservation,
    P93CanonicalProgramGeneralComplete.amboPayload,
    P93CanonicalProgramGeneralComplete.amboMixture,
    P93CanonicalSourceProgram.P93GeneralClausePayload.wholeConfigurations]

/-! ## Entry uniqueness at each concrete source

Each fact follows from `observationSourceUnique`: the named entry is already a member of the
program, so any other general entry at the same source must be equal to it.  No enumeration of the
remaining fifty-five entries is needed. -/

@[simp] theorem absoluteEntry_source :
    P93CanonicalProgramGeneral.absoluteEntry.source =
      P93CanonicalProgramGeneral.absoluteSource := rfl

@[simp] theorem absoluteEntry_family :
    P93CanonicalProgramGeneral.absoluteEntry.clause.family = .general := rfl

@[simp] theorem relativeEntry_source :
    P93CanonicalProgramGeneral.relativeEntry.source =
      P93CanonicalProgramGeneral.relativeSource := rfl

@[simp] theorem relativeEntry_family :
    P93CanonicalProgramGeneral.relativeEntry.clause.family = .general := rfl

@[simp] theorem racemateEntry_source :
    P93CanonicalProgramGeneral.racemateEntry.source =
      P93CanonicalProgramGeneral.racemateSource := rfl

@[simp] theorem racemateEntry_family :
    P93CanonicalProgramGeneral.racemateEntry.clause.family = .general := rfl

@[simp] theorem amboEntry_source :
    P93CanonicalProgramGeneralComplete.amboEntry.source =
      P93CanonicalProgramGeneralComplete.amboSource := rfl

@[simp] theorem amboEntry_family :
    P93CanonicalProgramGeneralComplete.amboEntry.clause.family = .general := rfl

theorem absoluteEntry_uniqueGeneral :
    ∀ other ∈ actualProgram.observations,
      other.source = P93CanonicalProgramGeneral.absoluteSource →
      other.clause.family = .general →
      other = P93CanonicalProgramGeneral.absoluteEntry := by
  intro other otherMem otherSource otherFamily
  exact actualProgram.entry_eq_of_source_eq otherMem absoluteEntry_mem_observations
    (otherSource.trans absoluteEntry_source.symm)
    (otherFamily.trans absoluteEntry_family.symm)

theorem relativeEntry_uniqueGeneral :
    ∀ other ∈ actualProgram.observations,
      other.source = P93CanonicalProgramGeneral.relativeSource →
      other.clause.family = .general →
      other = P93CanonicalProgramGeneral.relativeEntry := by
  intro other otherMem otherSource otherFamily
  exact actualProgram.entry_eq_of_source_eq otherMem relativeEntry_mem_observations
    (otherSource.trans relativeEntry_source.symm)
    (otherFamily.trans relativeEntry_family.symm)

theorem racemateEntry_uniqueGeneral :
    ∀ other ∈ actualProgram.observations,
      other.source = P93CanonicalProgramGeneral.racemateSource →
      other.clause.family = .general →
      other = P93CanonicalProgramGeneral.racemateEntry := by
  intro other otherMem otherSource otherFamily
  exact actualProgram.entry_eq_of_source_eq otherMem racemateEntry_mem_observations
    (otherSource.trans racemateEntry_source.symm)
    (otherFamily.trans racemateEntry_family.symm)

theorem amboEntry_uniqueGeneral :
    ∀ other ∈ actualProgram.observations,
      other.source = P93CanonicalProgramGeneralComplete.amboSource →
      other.clause.family = .general →
      other = P93CanonicalProgramGeneralComplete.amboEntry := by
  intro other otherMem otherSource otherFamily
  exact actualProgram.entry_eq_of_source_eq otherMem amboEntry_mem_observations
    (otherSource.trans amboEntry_source.symm)
    (otherFamily.trans amboEntry_family.symm)

/-! ## Negative regressions: exact-source and correlated-payload rejection -/

/-- The single-center `S` configuration at the exact absolute source. -/
def absoluteSConfiguration : P93CanonicalGeneralConfiguration where
  assignments := [P93CanonicalProgramGeneral.assignment 1 2 .S]

/-- The pointwise `(R,S)` combination of the two units of the relative source. -/
def relativeMixedRS : P93CanonicalGeneralConfiguration where
  assignments :=
    [ P93CanonicalProgramGeneral.assignment 1 2 .R
    , P93CanonicalProgramGeneral.assignment 2 3 .S ]

/-- The pointwise `(S,R)` combination of the two units of the relative source. -/
def relativeMixedSR : P93CanonicalGeneralConfiguration where
  assignments :=
    [ P93CanonicalProgramGeneral.assignment 1 2 .S
    , P93CanonicalProgramGeneral.assignment 2 3 .R ]

/-- Descriptor-map inequality proof of configuration inequality.  Mapping both configurations to
their descriptor lists avoids needing a `DecidableEq` instance on the configuration structure
itself; `decide` decides the resulting list equality because `P93CanonicalDescriptor` does have
decidable equality. -/
theorem absoluteSConfiguration_ne_absoluteConfiguration :
    absoluteSConfiguration ≠ P93CanonicalProgramGeneral.absoluteConfiguration := by
  intro h
  have mapEq :
      ([P93CanonicalDescriptor.acyclic BlueBookP93.Acyclic.Descriptor.S] :
          List P93CanonicalDescriptor) =
        [P93CanonicalDescriptor.acyclic BlueBookP93.Acyclic.Descriptor.R] :=
    congrArg
      (fun configuration : P93CanonicalGeneralConfiguration =>
        configuration.assignments.map fun (assignment :
          P93AuthorityLocatedAssignment P93CanonicalDescriptor) => assignment.descriptor) h
  exact absurd mapEq (by decide)

theorem relativeMixedRS_ne_relativeFirst :
    relativeMixedRS ≠ P93CanonicalProgramGeneral.relativeFirst := by
  intro h
  have mapEq :
      ([P93CanonicalDescriptor.acyclic BlueBookP93.Acyclic.Descriptor.R,
        P93CanonicalDescriptor.acyclic BlueBookP93.Acyclic.Descriptor.S] :
          List P93CanonicalDescriptor) =
        [P93CanonicalDescriptor.acyclic BlueBookP93.Acyclic.Descriptor.R,
          P93CanonicalDescriptor.acyclic BlueBookP93.Acyclic.Descriptor.R] :=
    congrArg
      (fun configuration : P93CanonicalGeneralConfiguration =>
        configuration.assignments.map fun (assignment :
          P93AuthorityLocatedAssignment P93CanonicalDescriptor) => assignment.descriptor) h
  exact absurd mapEq (by decide)

theorem relativeMixedRS_ne_relativeSecond :
    relativeMixedRS ≠ P93CanonicalProgramGeneral.relativeSecond := by
  intro h
  have mapEq :
      ([P93CanonicalDescriptor.acyclic BlueBookP93.Acyclic.Descriptor.R,
        P93CanonicalDescriptor.acyclic BlueBookP93.Acyclic.Descriptor.S] :
          List P93CanonicalDescriptor) =
        [P93CanonicalDescriptor.acyclic BlueBookP93.Acyclic.Descriptor.S,
          P93CanonicalDescriptor.acyclic BlueBookP93.Acyclic.Descriptor.S] :=
    congrArg
      (fun configuration : P93CanonicalGeneralConfiguration =>
        configuration.assignments.map fun (assignment :
          P93AuthorityLocatedAssignment P93CanonicalDescriptor) => assignment.descriptor) h
  exact absurd mapEq (by decide)

theorem relativeMixedSR_ne_relativeFirst :
    relativeMixedSR ≠ P93CanonicalProgramGeneral.relativeFirst := by
  intro h
  have mapEq :
      ([P93CanonicalDescriptor.acyclic BlueBookP93.Acyclic.Descriptor.S,
        P93CanonicalDescriptor.acyclic BlueBookP93.Acyclic.Descriptor.R] :
          List P93CanonicalDescriptor) =
        [P93CanonicalDescriptor.acyclic BlueBookP93.Acyclic.Descriptor.R,
          P93CanonicalDescriptor.acyclic BlueBookP93.Acyclic.Descriptor.R] :=
    congrArg
      (fun configuration : P93CanonicalGeneralConfiguration =>
        configuration.assignments.map fun (assignment :
          P93AuthorityLocatedAssignment P93CanonicalDescriptor) => assignment.descriptor) h
  exact absurd mapEq (by decide)

theorem relativeMixedSR_ne_relativeSecond :
    relativeMixedSR ≠ P93CanonicalProgramGeneral.relativeSecond := by
  intro h
  have mapEq :
      ([P93CanonicalDescriptor.acyclic BlueBookP93.Acyclic.Descriptor.S,
        P93CanonicalDescriptor.acyclic BlueBookP93.Acyclic.Descriptor.R] :
          List P93CanonicalDescriptor) =
        [P93CanonicalDescriptor.acyclic BlueBookP93.Acyclic.Descriptor.S,
          P93CanonicalDescriptor.acyclic BlueBookP93.Acyclic.Descriptor.S] :=
    congrArg
      (fun configuration : P93CanonicalGeneralConfiguration =>
        configuration.assignments.map fun (assignment :
          P93AuthorityLocatedAssignment P93CanonicalDescriptor) => assignment.descriptor) h
  exact absurd mapEq (by decide)

@[simp] theorem absoluteSConfiguration_not_mem :
    absoluteSConfiguration ∉ P93CanonicalSourceProgram.P93CanonicalClauseObservationEntry.wholeConfigurations
      P93CanonicalProgramGeneral.absoluteEntry := by
  rw [wholeConfigurations_absoluteEntry]
  simpa using absoluteSConfiguration_ne_absoluteConfiguration

@[simp] theorem relativeMixedRS_not_mem :
    relativeMixedRS ∉ P93CanonicalSourceProgram.P93CanonicalClauseObservationEntry.wholeConfigurations
      P93CanonicalProgramGeneral.relativeEntry := by
  rw [wholeConfigurations_relativeEntry]
  exact not_mem_cons_cons_of_ne relativeMixedRS_ne_relativeFirst
    relativeMixedRS_ne_relativeSecond

@[simp] theorem relativeMixedSR_not_mem :
    relativeMixedSR ∉ P93CanonicalSourceProgram.P93CanonicalClauseObservationEntry.wholeConfigurations
      P93CanonicalProgramGeneral.relativeEntry := by
  rw [wholeConfigurations_relativeEntry]
  exact not_mem_cons_cons_of_ne relativeMixedSR_ne_relativeFirst
    relativeMixedSR_ne_relativeSecond

/-- Exact source `(2R)-butan-2-ol` rejects the single-center `S` configuration. -/
theorem absoluteSConfiguration_not_authorized :
    ¬ (actualProgram.generalPolicy .general).ConfigurationAuthorized
        P93CanonicalProgramGeneral.absoluteSource absoluteSConfiguration := by
  refine not_configurationAuthorized_of_uniqueGeneralEntry actualProgram
    P93CanonicalProgramGeneral.absoluteSource P93CanonicalProgramGeneral.absoluteEntry
    absoluteEntry_mem_observations rfl rfl absoluteEntry_uniqueGeneral ?_
  exact absoluteSConfiguration_not_mem

/-- The correlated `(R,R)`/`(S,S)` relative payload rejects the pointwise `(R,S)` configuration. -/
theorem relativeMixedRS_not_authorized :
    ¬ (actualProgram.generalPolicy .general).ConfigurationAuthorized
        P93CanonicalProgramGeneral.relativeSource relativeMixedRS := by
  refine not_configurationAuthorized_of_uniqueGeneralEntry actualProgram
    P93CanonicalProgramGeneral.relativeSource P93CanonicalProgramGeneral.relativeEntry
    relativeEntry_mem_observations rfl rfl relativeEntry_uniqueGeneral ?_
  exact relativeMixedRS_not_mem

/-- The correlated `(R,R)`/`(S,S)` relative payload rejects the pointwise `(S,R)` configuration. -/
theorem relativeMixedSR_not_authorized :
    ¬ (actualProgram.generalPolicy .general).ConfigurationAuthorized
        P93CanonicalProgramGeneral.relativeSource relativeMixedSR := by
  refine not_configurationAuthorized_of_uniqueGeneralEntry actualProgram
    P93CanonicalProgramGeneral.relativeSource P93CanonicalProgramGeneral.relativeEntry
    relativeEntry_mem_observations rfl rfl relativeEntry_uniqueGeneral ?_
  exact relativeMixedSR_not_mem

/-- The per-unit descriptor relation is strictly weaker than whole-configuration authorization:
at the exact absolute source, `.S` is descriptor-authorized (through the certified mirror action)
while the single-center `S` configuration is not configuration-authorized. -/
theorem absoluteDescriptorS_authorized :
    (actualProgram.generalPolicy .general).DescriptorAuthorized
      P93CanonicalProgramGeneral.absoluteSource (.atomCenter 1)
      (P93CanonicalDescriptor.acyclic BlueBookP93.Acyclic.Descriptor.S) := by
  change
    actualProgram.HasClaim .general P93CanonicalProgramGeneral.absoluteSource
        (.general (.descriptor (.atomCenter 1)
          (P93CanonicalDescriptor.acyclic BlueBookP93.Acyclic.Descriptor.S))) ∨
      actualProgram.HasClaim .general P93CanonicalProgramGeneral.absoluteSource
        (.general (.descriptor (.atomCenter 1)
          (P93CanonicalDescriptor.mirror
            (P93CanonicalDescriptor.acyclic BlueBookP93.Acyclic.Descriptor.S))))
  right
  rw [← absoluteEntry_source, ← absoluteEntry_family]
  refine actualProgram.hasClaim_of_mem
    (entry := P93CanonicalProgramGeneral.absoluteEntry)
    (claim := .general (.descriptor (.atomCenter 1)
      (P93CanonicalDescriptor.mirror
        (P93CanonicalDescriptor.acyclic BlueBookP93.Acyclic.Descriptor.S))))
    absoluteEntry_mem_observations ?_
  simp [P93CanonicalProgramGeneral.absoluteEntry,
    P93CanonicalProgramGeneral.absoluteObservation,
    P93ClauseObservation.auditClaims, P93ClausePayloadData.toClaims,
    P93GeneralClausePayload.toClaims,
    P93CanonicalProgramGeneral.absolutePayload,
    P93CanonicalProgramGeneral.absoluteConfiguration,
    P93CanonicalGeneralConfiguration.toClaims,
    P93CanonicalProgramGeneral.assignment,
    P93CanonicalDescriptor.mirror]

theorem descriptorAuthorization_does_not_imply_configurationAuthorization :
    (actualProgram.generalPolicy .general).DescriptorAuthorized
        P93CanonicalProgramGeneral.absoluteSource (.atomCenter 1)
        (P93CanonicalDescriptor.acyclic BlueBookP93.Acyclic.Descriptor.S) ∧
      ¬ (actualProgram.generalPolicy .general).ConfigurationAuthorized
        P93CanonicalProgramGeneral.absoluteSource absoluteSConfiguration :=
  ⟨absoluteDescriptorS_authorized, absoluteSConfiguration_not_authorized⟩

/-! ## Positive regressions: legitimate whole configurations from the actual typed payloads -/

theorem absoluteConfiguration_mem_wholeConfigurations :
    P93CanonicalProgramGeneral.absoluteConfiguration ∈
      P93CanonicalSourceProgram.P93GeneralClausePayload.wholeConfigurations
        P93CanonicalProgramGeneral.absolutePayload := by
  simp [P93CanonicalProgramGeneral.absolutePayload,
    P93CanonicalSourceProgram.P93GeneralClausePayload.wholeConfigurations]

theorem relativeFirst_mem_wholeConfigurations :
    P93CanonicalProgramGeneral.relativeFirst ∈
      P93CanonicalSourceProgram.P93GeneralClausePayload.wholeConfigurations
        P93CanonicalProgramGeneral.relativePayload := by
  simp [P93CanonicalProgramGeneral.relativePayload,
    P93CanonicalSourceProgram.P93GeneralClausePayload.wholeConfigurations]

theorem relativeSecond_mem_wholeConfigurations :
    P93CanonicalProgramGeneral.relativeSecond ∈
      P93CanonicalSourceProgram.P93GeneralClausePayload.wholeConfigurations
        P93CanonicalProgramGeneral.relativePayload := by
  simp [P93CanonicalProgramGeneral.relativePayload,
    P93CanonicalSourceProgram.P93GeneralClausePayload.wholeConfigurations]

theorem racemateFirst_mem_wholeConfigurations :
    P93CanonicalProgramGeneral.racemateFirst ∈
      P93CanonicalSourceProgram.P93GeneralClausePayload.wholeConfigurations
        P93CanonicalProgramGeneral.racematePayload := by
  simp [P93CanonicalProgramGeneral.racematePayload,
    P93CanonicalProgramGeneral.racemateMixture,
    P93CanonicalSourceProgram.P93GeneralClausePayload.wholeConfigurations]

theorem racemateSecond_mem_wholeConfigurations :
    P93CanonicalProgramGeneral.racemateSecond ∈
      P93CanonicalSourceProgram.P93GeneralClausePayload.wholeConfigurations
        P93CanonicalProgramGeneral.racematePayload := by
  simp [P93CanonicalProgramGeneral.racematePayload,
    P93CanonicalProgramGeneral.racemateMixture,
    P93CanonicalSourceProgram.P93GeneralClausePayload.wholeConfigurations]

theorem amboFirst_mem_wholeConfigurations :
    P93CanonicalProgramGeneralComplete.amboFirst ∈
      P93CanonicalSourceProgram.P93GeneralClausePayload.wholeConfigurations
        P93CanonicalProgramGeneralComplete.amboPayload := by
  simp [P93CanonicalProgramGeneralComplete.amboPayload,
    P93CanonicalProgramGeneralComplete.amboMixture,
    P93CanonicalSourceProgram.P93GeneralClausePayload.wholeConfigurations]

theorem amboSecond_mem_wholeConfigurations :
    P93CanonicalProgramGeneralComplete.amboSecond ∈
      P93CanonicalSourceProgram.P93GeneralClausePayload.wholeConfigurations
        P93CanonicalProgramGeneralComplete.amboPayload := by
  simp [P93CanonicalProgramGeneralComplete.amboPayload,
    P93CanonicalProgramGeneralComplete.amboMixture,
    P93CanonicalSourceProgram.P93GeneralClausePayload.wholeConfigurations]

theorem absoluteConfiguration_authorized :
    (actualProgram.generalPolicy .general).ConfigurationAuthorized
      P93CanonicalProgramGeneral.absoluteSource
      P93CanonicalProgramGeneral.absoluteConfiguration := by
  refine actualProgram.generalConfigurationAuthorized_of_generalPayload
    P93CanonicalProgramGeneral.absoluteSource
    P93CanonicalProgramGeneral.absoluteSource_structurallyWellFormed
    Remaining71P93GeneralAuthorityRow.absoluteConfiguration
    P93CanonicalProgramGeneral.absoluteEntry.clauseListed
    P93CanonicalProgramGeneral.absoluteObservation
    P93CanonicalProgramGeneral.absoluteTranscription
    P93CanonicalProgramGeneral.absolutePayload rfl absoluteEntry_mem_observations ?_
  exact absoluteConfiguration_mem_wholeConfigurations

theorem relativeFirst_authorized :
    (actualProgram.generalPolicy .general).ConfigurationAuthorized
      P93CanonicalProgramGeneral.relativeSource
      P93CanonicalProgramGeneral.relativeFirst := by
  refine actualProgram.generalConfigurationAuthorized_of_generalPayload
    P93CanonicalProgramGeneral.relativeSource
    P93CanonicalProgramGeneral.relativeSource_structurallyWellFormed
    Remaining71P93GeneralAuthorityRow.relativeConfiguration
    P93CanonicalProgramGeneral.relativeEntry.clauseListed
    P93CanonicalProgramGeneral.relativeObservation
    P93CanonicalProgramGeneral.relativeTranscription
    P93CanonicalProgramGeneral.relativePayload rfl relativeEntry_mem_observations ?_
  exact relativeFirst_mem_wholeConfigurations

theorem relativeSecond_authorized :
    (actualProgram.generalPolicy .general).ConfigurationAuthorized
      P93CanonicalProgramGeneral.relativeSource
      P93CanonicalProgramGeneral.relativeSecond := by
  refine actualProgram.generalConfigurationAuthorized_of_generalPayload
    P93CanonicalProgramGeneral.relativeSource
    P93CanonicalProgramGeneral.relativeSource_structurallyWellFormed
    Remaining71P93GeneralAuthorityRow.relativeConfiguration
    P93CanonicalProgramGeneral.relativeEntry.clauseListed
    P93CanonicalProgramGeneral.relativeObservation
    P93CanonicalProgramGeneral.relativeTranscription
    P93CanonicalProgramGeneral.relativePayload rfl relativeEntry_mem_observations ?_
  exact relativeSecond_mem_wholeConfigurations

theorem racemateFirst_authorized :
    (actualProgram.generalPolicy .general).ConfigurationAuthorized
      P93CanonicalProgramGeneral.racemateSource
      P93CanonicalProgramGeneral.racemateFirst := by
  refine actualProgram.generalConfigurationAuthorized_of_generalPayload
    P93CanonicalProgramGeneral.racemateSource
    P93CanonicalProgramGeneral.racemateSource_structurallyWellFormed
    Remaining71P93GeneralAuthorityRow.racemates
    P93CanonicalProgramGeneral.racemateEntry.clauseListed
    P93CanonicalProgramGeneral.racemateObservation
    P93CanonicalProgramGeneral.racemateTranscription
    P93CanonicalProgramGeneral.racematePayload rfl racemateEntry_mem_observations ?_
  exact racemateFirst_mem_wholeConfigurations

theorem racemateSecond_authorized :
    (actualProgram.generalPolicy .general).ConfigurationAuthorized
      P93CanonicalProgramGeneral.racemateSource
      P93CanonicalProgramGeneral.racemateSecond := by
  refine actualProgram.generalConfigurationAuthorized_of_generalPayload
    P93CanonicalProgramGeneral.racemateSource
    P93CanonicalProgramGeneral.racemateSource_structurallyWellFormed
    Remaining71P93GeneralAuthorityRow.racemates
    P93CanonicalProgramGeneral.racemateEntry.clauseListed
    P93CanonicalProgramGeneral.racemateObservation
    P93CanonicalProgramGeneral.racemateTranscription
    P93CanonicalProgramGeneral.racematePayload rfl racemateEntry_mem_observations ?_
  exact racemateSecond_mem_wholeConfigurations

theorem amboFirst_authorized :
    (actualProgram.generalPolicy .general).ConfigurationAuthorized
      P93CanonicalProgramGeneralComplete.amboSource
      P93CanonicalProgramGeneralComplete.amboFirst := by
  refine actualProgram.generalConfigurationAuthorized_of_generalPayload
    P93CanonicalProgramGeneralComplete.amboSource
    P93CanonicalProgramGeneralComplete.amboSource_structurallyWellFormed
    Remaining71P93GeneralAuthorityRow.ambo
    P93CanonicalProgramGeneralComplete.amboEntry.clauseListed
    P93CanonicalProgramGeneralComplete.amboObservation
    P93CanonicalProgramGeneralComplete.amboTranscription
    P93CanonicalProgramGeneralComplete.amboPayload rfl amboEntry_mem_observations ?_
  exact amboFirst_mem_wholeConfigurations

theorem amboSecond_authorized :
    (actualProgram.generalPolicy .general).ConfigurationAuthorized
      P93CanonicalProgramGeneralComplete.amboSource
      P93CanonicalProgramGeneralComplete.amboSecond := by
  refine actualProgram.generalConfigurationAuthorized_of_generalPayload
    P93CanonicalProgramGeneralComplete.amboSource
    P93CanonicalProgramGeneralComplete.amboSource_structurallyWellFormed
    Remaining71P93GeneralAuthorityRow.ambo
    P93CanonicalProgramGeneralComplete.amboEntry.clauseListed
    P93CanonicalProgramGeneralComplete.amboObservation
    P93CanonicalProgramGeneralComplete.amboTranscription
    P93CanonicalProgramGeneralComplete.amboPayload rfl amboEntry_mem_observations ?_
  exact amboSecond_mem_wholeConfigurations

/-! ## Kernel guards -/

assert_kernel_only
  TetraStereo.OneCenter.P93GeneralConfigurationAuthorizationFidelity.configurationAuthorized_iff_of_uniqueGeneralEntry
assert_kernel_only
  TetraStereo.OneCenter.P93GeneralConfigurationAuthorizationFidelity.not_configurationAuthorized_of_uniqueGeneralEntry
assert_kernel_only
  TetraStereo.OneCenter.P93GeneralConfigurationAuthorizationFidelity.absoluteSConfiguration_not_authorized
assert_kernel_only
  TetraStereo.OneCenter.P93GeneralConfigurationAuthorizationFidelity.relativeMixedRS_not_authorized
assert_kernel_only
  TetraStereo.OneCenter.P93GeneralConfigurationAuthorizationFidelity.relativeMixedSR_not_authorized
assert_kernel_only
  TetraStereo.OneCenter.P93GeneralConfigurationAuthorizationFidelity.absoluteDescriptorS_authorized
assert_kernel_only
  TetraStereo.OneCenter.P93GeneralConfigurationAuthorizationFidelity.absoluteConfiguration_authorized
assert_kernel_only
  TetraStereo.OneCenter.P93GeneralConfigurationAuthorizationFidelity.relativeFirst_authorized
assert_kernel_only
  TetraStereo.OneCenter.P93GeneralConfigurationAuthorizationFidelity.relativeSecond_authorized
assert_kernel_only
  TetraStereo.OneCenter.P93GeneralConfigurationAuthorizationFidelity.racemateFirst_authorized
assert_kernel_only
  TetraStereo.OneCenter.P93GeneralConfigurationAuthorizationFidelity.racemateSecond_authorized
assert_kernel_only
  TetraStereo.OneCenter.P93GeneralConfigurationAuthorizationFidelity.amboFirst_authorized
assert_kernel_only
  TetraStereo.OneCenter.P93GeneralConfigurationAuthorizationFidelity.amboSecond_authorized

end P93GeneralConfigurationAuthorizationFidelity

end TetraStereo.OneCenter
