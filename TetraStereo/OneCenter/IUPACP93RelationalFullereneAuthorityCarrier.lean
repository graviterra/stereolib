import TetraStereo.OneCenter.IUPACP93FullereneAuthorityCarrier
import TetraStereo.OneCenter.P93MolecularFullereneRelationalSourceOrientation
import TetraStereo.OneCenter.P93MolecularFullereneTopologySourceAdapter

set_option autoImplicit false

/-!
# Source-truthful relational authority for P-93 fullerene derivatives

This is the release-facing ownership boundary for the five molecular fullerene derivative rows.
It deliberately does not project an addend to one of its cage attachment sites: a multiport
addend is one constitutional owner, and every substituent stereogenic unit is owned by that whole
addend.  The older site-rooted fullerene authority structures remain available only as
compatibility carriers for already-compiled rows; they are not used by any definition below.

The source family is the molecule-indexed relational source-orientation family.  Consequently the
assignment analyzer has the already-proved exact no-invention/no-omission semantics, while this
module adds exact source authorization and complete whole-addend CIP ownership.
-/

namespace TetraStereo.OneCenter

open BlueBookP93.Cyclic

noncomputable section

/-! ## Whole-addend-owned substituent assignments -/

/-- Every atom participating in a typed stereogenic unit.  Traversal order remains in the unit;
this finite set is used only for the constitutional ownership proof. -/
def P93RelationalFullereneSubstituentAtomCarrier :
    P93FullereneSubstituentStereogenicUnit → Finset Nat
  | .center atom => {atom}
  | .doubleBond first second => {first, second}
  | .cumuleneAxis path => path.toFinset
  | .bondAxis first second => {first, second}
  | .plane members => members
  | .helix path => path.toFinset
  | .polyhedron center positions => insert center positions

/-- One CIP result whose owner is the complete graph-backed addend, not one attachment site.
This retains the hyperedge grouping needed by bidentate fullerene derivatives. -/
structure P93RelationalFullereneSubstituentCIPAssignment where
  owner : MolecularFullereneAddend
  unit : P93FullereneSubstituentStereogenicUnit
  citation : P93AuthorityCitationToken
  descriptor : P93FullereneSubstituentCIPDescriptor
  deriving DecidableEq

/-- Audited source relations for the relational fullerene boundary.  Each relation is indexed by
the exact molecule and exact relational input; source authorization therefore cannot silently
substitute a site projection or evidence family from another derivative. -/
structure P93RelationalFullereneAuthorityPolicy where
  physicalObservation : P93AuthorityPhysicalObservationPolicy
  RawMoleculeObserved : AuthoritativeChemicalInput → RawMolecule → Prop
  InputFamilyObserved :
    (source : AuthoritativeChemicalInput) → (molecule : RawMolecule) →
      (spatial? : Option SpatialConfiguration) →
      List (RelationalSourceOrientedMolecularFullereneConfigurationInput molecule) → Prop
  InputObserved :
    (source : AuthoritativeChemicalInput) → (molecule : RawMolecule) →
      (spatial? : Option SpatialConfiguration) →
      RelationalSourceOrientedMolecularFullereneConfigurationInput molecule → Prop
  /-- The handed direction of an oriented face list when viewed from outside is a source fact
  unless exact spatial geometry supplies it.  Requiring this relation prevents selecting the
  opposite exterior sense merely to manufacture the desired `C/A` result. -/
  ExteriorFaceSenseObserved :
    (source : AuthoritativeChemicalInput) → (molecule : RawMolecule) →
      RelationalSourceOrientedMolecularFullereneConfigurationInput molecule →
      FullereneExteriorFaceSense → Prop
  /-- Whole-derivative chirality is independent chemical evidence, not a consequence of the
  induced cage graph alone.  It is therefore authorized explicitly at the exact molecule and
  relational input instead of being hidden inside the general input-observation relation. -/
  OriginalDerivativeChiralityObserved :
    (source : AuthoritativeChemicalInput) → (molecule : RawMolecule) →
      RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule → Bool → Prop
  /-- Exact intrinsic-chirality partition of the whole constitutional addends.  The template
  compiler computes this finite set, but source authority must still validate the scientific
  chirality classification carried by the templates. -/
  ChiralAddendsObserved :
    (source : AuthoritativeChemicalInput) → (molecule : RawMolecule) →
      RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule →
      Finset MolecularFullereneAddend → Prop
  /-- Type 4 has no printed cage numbering or turn; it is observed at the relational symmetry
  boundary without manufacturing an unused orientation record. -/
  Type4InputObserved :
    (source : AuthoritativeChemicalInput) → (molecule : RawMolecule) →
      RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule → Prop
  PrintedCageHandednessObserved :
    (source : AuthoritativeChemicalInput) → (molecule : RawMolecule) →
      RelationalSourceOrientedMolecularFullereneConfigurationInput molecule →
      FullereneNumberingKind → FullereneHandedness → Prop
  SubstituentUnitInAddendEligible :
    (source : AuthoritativeChemicalInput) → (molecule : RawMolecule) →
      RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule →
      MolecularFullereneAddend → P93FullereneSubstituentStereogenicUnit → Prop
  SubstituentCitationAuthorized :
    (source : AuthoritativeChemicalInput) → (molecule : RawMolecule) →
      RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule →
      MolecularFullereneAddend → P93AuthorityCitationToken →
        P93FullereneSubstituentStereogenicUnit → Prop
  SubstituentDescriptorAuthorized :
    (source : AuthoritativeChemicalInput) → (molecule : RawMolecule) →
      RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule →
      MolecularFullereneAddend → P93FullereneSubstituentStereogenicUnit →
        P93FullereneSubstituentCIPDescriptor → Prop

/-- Physical, constitutional, typed, and source-authorized validity of one whole-addend-owned
assignment. -/
structure P93RelationalFullereneSubstituentCIPAssignment.ValidFor
    (policy : P93RelationalFullereneAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (molecule : RawMolecule)
    (input : RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule)
    (assignment : P93RelationalFullereneSubstituentCIPAssignment) : Prop where
  ownerChiral : assignment.owner ∈ input.evidence.chiralAddends
  unitOwned : P93RelationalFullereneSubstituentAtomCarrier assignment.unit ⊆
    assignment.owner.externalAtoms
  physicalValid : assignment.unit.toPhysicalUnit.ValidFor
    policy.physicalObservation source
  unitAuthorized : policy.SubstituentUnitInAddendEligible source molecule input
    assignment.owner assignment.unit
  descriptorMatches : P93FullereneSubstituentDescriptorMatchesUnit
    assignment.descriptor assignment.unit
  citationValid : assignment.citation.Valid
  citationAuthorized : policy.SubstituentCitationAuthorized source molecule input
    assignment.owner assignment.citation assignment.unit
  descriptorAuthorized : policy.SubstituentDescriptorAuthorized source molecule input
    assignment.owner assignment.unit assignment.descriptor

namespace P93RelationalFullereneSubstituentCIPAssignment.ValidFor

/-- Chirality ownership is ownership by the exact complete addend family. -/
theorem ownerInAddends
    {policy : P93RelationalFullereneAuthorityPolicy}
    {source : AuthoritativeChemicalInput} {molecule : RawMolecule}
    {input : RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule}
    {assignment : P93RelationalFullereneSubstituentCIPAssignment}
    (valid : assignment.ValidFor policy source molecule input) :
    assignment.owner ∈ input.evidence.addends :=
  input.evidence.chiralAddendsOwned assignment.owner valid.ownerChiral

end P93RelationalFullereneSubstituentCIPAssignment.ValidFor

/-- Exact whole-addend corpus: `(owner, unit)` pairs are duplicate-free; every carried result is
valid; every chiral owner occurs; and every independently eligible unit of every chiral owner
occurs.  Citation validity and authorization remain assignment-local.  Citations are deliberately
not globally unique: distinct physical units, including the two repeated `(1S)` arms of one
bidentate addend, may truthfully carry the same printed local citation. -/
structure P93RelationalFullereneSubstituentCIPAssignmentsComplete
    (policy : P93RelationalFullereneAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (molecule : RawMolecule)
    (input : RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule)
    (assignments : List P93RelationalFullereneSubstituentCIPAssignment) : Prop where
  pairNodup : (assignments.map fun assignment =>
    (assignment.owner, assignment.unit)).Nodup
  assignmentsValid : ∀ assignment ∈ assignments,
    assignment.ValidFor policy source molecule input
  chiralOwnersCovered : ∀ owner ∈ input.evidence.chiralAddends,
    ∃ assignment ∈ assignments, assignment.owner = owner
  eligibleUnitsComplete : ∀ owner ∈ input.evidence.chiralAddends, ∀ unit,
    policy.SubstituentUnitInAddendEligible source molecule input owner unit →
      ∃ assignment ∈ assignments,
        assignment.owner = owner ∧ assignment.unit = unit

namespace P93RelationalFullereneSubstituentCIPAssignmentsComplete

theorem assignments_nonempty_of_chiralAddends_nonempty
    {policy : P93RelationalFullereneAuthorityPolicy}
    {source : AuthoritativeChemicalInput} {molecule : RawMolecule}
    {input : RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule}
    {assignments : List P93RelationalFullereneSubstituentCIPAssignment}
    (complete : P93RelationalFullereneSubstituentCIPAssignmentsComplete
      policy source molecule input assignments)
    (chiral : input.evidence.chiralAddends.Nonempty) :
    assignments ≠ [] := by
  rintro rfl
  obtain ⟨owner, ownerChiral⟩ := chiral
  simpa using complete.chiralOwnersCovered owner ownerChiral

/-- Exact unit enumeration: the corpus carries an `(owner, unit)` pair if and only if that owner
is one of the exact chiral addends and the source authorizes that unit for that whole addend. -/
theorem assignment_exists_iff
    {policy : P93RelationalFullereneAuthorityPolicy}
    {source : AuthoritativeChemicalInput} {molecule : RawMolecule}
    {input : RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule}
    {assignments : List P93RelationalFullereneSubstituentCIPAssignment}
    (complete : P93RelationalFullereneSubstituentCIPAssignmentsComplete
      policy source molecule input assignments)
    (owner : MolecularFullereneAddend)
    (unit : P93FullereneSubstituentStereogenicUnit) :
    (∃ assignment ∈ assignments,
        assignment.owner = owner ∧ assignment.unit = unit) ↔
      owner ∈ input.evidence.chiralAddends ∧
        policy.SubstituentUnitInAddendEligible source molecule input owner unit := by
  constructor
  · rintro ⟨assignment, assignmentMem, ownerEq, unitEq⟩
    have valid := complete.assignmentsValid assignment assignmentMem
    subst owner
    subst unit
    exact ⟨valid.ownerChiral, valid.unitAuthorized⟩
  · rintro ⟨ownerChiral, eligible⟩
    exact complete.eligibleUnitsComplete owner ownerChiral unit eligible

end P93RelationalFullereneSubstituentCIPAssignmentsComplete

/-! ## Exact relational analyzer/reference boundary -/

/-- Independent complete assignment meaning inherited without weakening from the relational
source-orientation kernel. -/
abbrev P93RelationalFullereneAuthorityAssignmentJudgment
    (molecule : RawMolecule) (spatial? : Option SpatialConfiguration)
    (inputs : List (RelationalSourceOrientedMolecularFullereneConfigurationInput molecule))
    (assignment : FullereneConfigurationAssignment) : Prop :=
  RelationalSourceOrientedMolecularFullereneConfigurationAssignmentJudgment
    molecule spatial? inputs assignment

/-- The authority analyzer is exactly the relational source analyzer, not a second handwritten
classifier. -/
noncomputable abbrev analyzeP93RelationalFullereneAuthorityAssignments
    (molecule : RawMolecule) (spatial? : Option SpatialConfiguration)
    (inputs : List (RelationalSourceOrientedMolecularFullereneConfigurationInput molecule)) :
    List FullereneConfigurationAssignment :=
  analyzeRelationalSourceOrientedMolecularFullereneConfigurations molecule spatial? inputs

/-- Exact analyzer/reference equivalence: no invented result and no omitted judged result. -/
theorem mem_analyzeP93RelationalFullereneAuthorityAssignments_iff
    (molecule : RawMolecule) (spatial? : Option SpatialConfiguration)
    (inputs : List (RelationalSourceOrientedMolecularFullereneConfigurationInput molecule))
    (assignment : FullereneConfigurationAssignment) :
    assignment ∈ analyzeP93RelationalFullereneAuthorityAssignments molecule spatial? inputs ↔
      P93RelationalFullereneAuthorityAssignmentJudgment
        molecule spatial? inputs assignment :=
  mem_analyzeRelationalSourceOrientedMolecularFullereneConfigurations_iff
    molecule spatial? inputs assignment

theorem p93RelationalFullereneAuthorityAnalyzer_noInvention
    {molecule : RawMolecule} {spatial? : Option SpatialConfiguration}
    {inputs : List (RelationalSourceOrientedMolecularFullereneConfigurationInput molecule)}
    {assignment : FullereneConfigurationAssignment}
    (emitted : assignment ∈
      analyzeP93RelationalFullereneAuthorityAssignments molecule spatial? inputs) :
    P93RelationalFullereneAuthorityAssignmentJudgment molecule spatial? inputs assignment :=
  (mem_analyzeP93RelationalFullereneAuthorityAssignments_iff
    molecule spatial? inputs assignment).1 emitted

theorem p93RelationalFullereneAuthorityAnalyzer_noOmission
    {molecule : RawMolecule} {spatial? : Option SpatialConfiguration}
    {inputs : List (RelationalSourceOrientedMolecularFullereneConfigurationInput molecule)}
    {assignment : FullereneConfigurationAssignment}
    (judged : P93RelationalFullereneAuthorityAssignmentJudgment
      molecule spatial? inputs assignment) :
    assignment ∈ analyzeP93RelationalFullereneAuthorityAssignments molecule spatial? inputs :=
  (mem_analyzeP93RelationalFullereneAuthorityAssignments_iff
    molecule spatial? inputs assignment).2 judged

/-! ## Complete authority observations -/

/-- Shared exact observation.  The duplicate `addends` and `chiralAddends` fields are intentional
printed data, and `ValidFor` below requires literal equality with the selected graph-backed source
record so neither family can be projected, regrouped, or silently replaced. -/
structure P93RelationalFullereneAuthorityObservation
    (_policy : P93RelationalFullereneAuthorityPolicy) where
  molecule : RawMolecule
  spatial? : Option SpatialConfiguration
  inputs : List (RelationalSourceOrientedMolecularFullereneConfigurationInput molecule)
  selectedInput : RelationalSourceOrientedMolecularFullereneConfigurationInput molecule
  addends : List MolecularFullereneAddend
  chiralAddends : Finset MolecularFullereneAddend
  assignment : FullereneConfigurationAssignment
  substituentAssignments : List P93RelationalFullereneSubstituentCIPAssignment

/-- Complete source, ownership, local-classification, family-agreement, and substituent corpus
judgment for one relational fullerene observation. -/
structure P93RelationalFullereneAuthorityObservation.ValidFor
    (policy : P93RelationalFullereneAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93RelationalFullereneAuthorityObservation policy) : Prop where
  structureAgreement :
    observation.molecule.MolecularFullereneTopologyRepresentationAgreement
      observation.selectedInput.symmetryInput.cage.carrier observation.spatial? source
  moleculeObserved : policy.RawMoleculeObserved source observation.molecule
  inputsNonempty : observation.inputs ≠ []
  inputFamilyObserved : policy.InputFamilyObserved source observation.molecule
    observation.spatial? observation.inputs
  inputsObserved : ∀ input ∈ observation.inputs,
    policy.InputObserved source observation.molecule observation.spatial? input
  inputsExteriorFaceSenseObserved : ∀ input ∈ observation.inputs,
    match input.turnSource with
    | .supportingSpatial => True
    | .exterior sense =>
        policy.ExteriorFaceSenseObserved source observation.molecule input sense
  inputsOriginalDerivativeChiralityObserved : ∀ input ∈ observation.inputs,
    policy.OriginalDerivativeChiralityObserved source observation.molecule
      input.symmetryInput input.symmetryInput.evidence.originalDerivativeChiral
  inputsChiralAddendsObserved : ∀ input ∈ observation.inputs,
    policy.ChiralAddendsObserved source observation.molecule input.symmetryInput
      input.symmetryInput.evidence.chiralAddends
  selectedInputPresent : observation.selectedInput ∈ observation.inputs
  selectedInputJudged :
    RelationalSourceOrientedMolecularFullereneConfigurationInputJudgment
      observation.molecule observation.spatial? observation.selectedInput
  exteriorFaceSenseObserved :
    match observation.selectedInput.turnSource with
    | .supportingSpatial => True
    | .exterior sense => policy.ExteriorFaceSenseObserved source observation.molecule
        observation.selectedInput sense
  originalDerivativeChiralityObserved :
    policy.OriginalDerivativeChiralityObserved source observation.molecule
      observation.selectedInput.symmetryInput
      observation.selectedInput.symmetryInput.evidence.originalDerivativeChiral
  chiralAddendsObserved :
    policy.ChiralAddendsObserved source observation.molecule
      observation.selectedInput.symmetryInput
      observation.selectedInput.symmetryInput.evidence.chiralAddends
  addendsExact : observation.addends = observation.selectedInput.symmetryInput.evidence.addends
  chiralAddendsExact : observation.chiralAddends =
    observation.selectedInput.symmetryInput.evidence.chiralAddends
  localAssignmentJudged : FullereneConfigurationAssignmentJudgment
    observation.selectedInput.symmetryInput.cage.toFullereneConfigurationInput
      observation.assignment
  assignmentComplete : P93RelationalFullereneAuthorityAssignmentJudgment
    observation.molecule observation.spatial? observation.inputs observation.assignment
  substituentCorpusComplete : P93RelationalFullereneSubstituentCIPAssignmentsComplete
    policy source observation.molecule observation.selectedInput.symmetryInput
      observation.substituentAssignments

namespace P93RelationalFullereneAuthorityObservation.ValidFor

/-- The complete corpus theorem collapses the public pair-uniqueness obligation. -/
theorem substituentAssignmentsPairNodup
    {policy : P93RelationalFullereneAuthorityPolicy}
    {source : AuthoritativeChemicalInput}
    {observation : P93RelationalFullereneAuthorityObservation policy}
    (valid : observation.ValidFor policy source) :
    (observation.substituentAssignments.map fun assignment =>
      (assignment.owner, assignment.unit)).Nodup :=
  valid.substituentCorpusComplete.pairNodup

/-- The complete corpus theorem collapses per-assignment ownership and authorization. -/
theorem substituentAssignmentsValid
    {policy : P93RelationalFullereneAuthorityPolicy}
    {source : AuthoritativeChemicalInput}
    {observation : P93RelationalFullereneAuthorityObservation policy}
    (valid : observation.ValidFor policy source) :
    ∀ assignment ∈ observation.substituentAssignments,
      assignment.ValidFor policy source observation.molecule
        observation.selectedInput.symmetryInput :=
  valid.substituentCorpusComplete.assignmentsValid

/-- The complete corpus theorem collapses exact no-omission for every eligible unit. -/
theorem substituentAssignmentsComplete
    {policy : P93RelationalFullereneAuthorityPolicy}
    {source : AuthoritativeChemicalInput}
    {observation : P93RelationalFullereneAuthorityObservation policy}
    (valid : observation.ValidFor policy source) :
    ∀ owner ∈ observation.selectedInput.symmetryInput.evidence.chiralAddends, ∀ unit,
      policy.SubstituentUnitInAddendEligible source observation.molecule
          observation.selectedInput.symmetryInput owner unit →
        ∃ assignment ∈ observation.substituentAssignments,
          assignment.owner = owner ∧ assignment.unit = unit :=
  valid.substituentCorpusComplete.eligibleUnitsComplete

end P93RelationalFullereneAuthorityObservation.ValidFor

/-- Types 1--3 add exactly one source-authorized cage-handedness claim to the common relational
observation. -/
structure P93RelationalFullereneHandedAuthorityObservation
    (policy : P93RelationalFullereneAuthorityPolicy) where
  base : P93RelationalFullereneAuthorityObservation policy
  numberingKind : FullereneNumberingKind
  handedness : FullereneHandedness

structure P93RelationalFullereneHandedAuthorityObservation.ValidFor
    (policy : P93RelationalFullereneAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93RelationalFullereneHandedAuthorityObservation policy) : Prop where
  baseValid : observation.base.ValidFor policy source
  handedClass : observation.base.assignment.chiralityType = .inherentlyChiralParent ∨
    observation.base.assignment.chiralityType = .inherentlyChiralSubstitutionPattern ∨
    observation.base.assignment.chiralityType = .noninherentlyChiralSubstitutionPattern
  payloadPresent : FullereneDescriptorPayload.cageHandedness
    observation.numberingKind observation.handedness ∈ observation.base.assignment.payloads
  printedObserved : policy.PrintedCageHandednessObserved source observation.base.molecule
    observation.base.selectedInput observation.numberingKind observation.handedness

/-- Type 4 stops at the relational symmetry boundary.  It deliberately carries neither a
numbering record nor a turn source, because the printed Type-4 row reports only substituent CIP. -/
structure P93RelationalFullereneType4AuthorityObservation
    (policy : P93RelationalFullereneAuthorityPolicy) where
  molecule : RawMolecule
  spatial? : Option SpatialConfiguration
  input : RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule
  assignment : FullereneConfigurationAssignment
  substituentAssignments : List P93RelationalFullereneSubstituentCIPAssignment

structure P93RelationalFullereneType4AuthorityObservation.ValidFor
    (policy : P93RelationalFullereneAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93RelationalFullereneType4AuthorityObservation policy) : Prop where
  structureAgreement :
    observation.molecule.MolecularFullereneTopologyRepresentationAgreement
      observation.input.cage.carrier observation.spatial? source
  moleculeObserved : policy.RawMoleculeObserved source observation.molecule
  inputObserved : policy.Type4InputObserved source observation.molecule observation.input
  inputJudged : RelationalSymmetryDerivedMolecularFullereneConfigurationInputJudgment
    observation.molecule observation.input
  originalDerivativeChiralityObserved :
    policy.OriginalDerivativeChiralityObserved source observation.molecule observation.input
      observation.input.evidence.originalDerivativeChiral
  chiralAddendsObserved :
    policy.ChiralAddendsObserved source observation.molecule observation.input
      observation.input.evidence.chiralAddends
  localAssignmentJudged : FullereneConfigurationAssignmentJudgment
    observation.input.cage.toFullereneConfigurationInput observation.assignment
  typeFour : observation.assignment.chiralityType = .chiralSubstituentsOnly
  cipPayloadPresent : .substituentCIPComplete ∈ observation.assignment.payloads
  numberingAbsent : observation.input.cage.descriptorEvidence.cageNumberingKind = none
  turnAbsent : observation.input.cage.descriptorEvidence.cageTurn = none
  chiralAddendsNonempty :
    observation.input.evidence.chiralAddends.Nonempty
  substituentCorpusComplete : P93RelationalFullereneSubstituentCIPAssignmentsComplete
    policy source observation.molecule observation.input observation.substituentAssignments

theorem P93RelationalFullereneType4AuthorityObservation.ValidFor.assignmentsNonempty
    {policy : P93RelationalFullereneAuthorityPolicy}
    {source : AuthoritativeChemicalInput}
    {observation : P93RelationalFullereneType4AuthorityObservation policy}
    (valid : observation.ValidFor policy source) :
    observation.substituentAssignments ≠ [] :=
  valid.substituentCorpusComplete.assignments_nonempty_of_chiralAddends_nonempty
    valid.chiralAddendsNonempty

/-- The superimposed row combines a Type 2/3 cage-handedness result with the independently
complete whole-addend-owned CIP corpus. -/
structure P93RelationalFullereneSuperimposedAuthorityObservation
    (policy : P93RelationalFullereneAuthorityPolicy) where
  handed : P93RelationalFullereneHandedAuthorityObservation policy

structure P93RelationalFullereneSuperimposedAuthorityObservation.ValidFor
    (policy : P93RelationalFullereneAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93RelationalFullereneSuperimposedAuthorityObservation policy) : Prop where
  handedValid : observation.handed.ValidFor policy source
  substitutionPatternClass :
    observation.handed.base.assignment.chiralityType =
        .inherentlyChiralSubstitutionPattern ∨
      observation.handed.base.assignment.chiralityType =
        .noninherentlyChiralSubstitutionPattern
  chiralAddendsNonempty :
    observation.handed.base.selectedInput.symmetryInput.evidence.chiralAddends.Nonempty
  complete : SuperimposedFullereneConfigurationComplete true true

theorem P93RelationalFullereneSuperimposedAuthorityObservation.ValidFor.assignmentsNonempty
    {policy : P93RelationalFullereneAuthorityPolicy}
    {source : AuthoritativeChemicalInput}
    {observation : P93RelationalFullereneSuperimposedAuthorityObservation policy}
    (valid : observation.ValidFor policy source) :
    observation.handed.base.substituentAssignments ≠ [] :=
  valid.handedValid.baseValid.substituentCorpusComplete
    |>.assignments_nonempty_of_chiralAddends_nonempty valid.chiralAddendsNonempty

end

end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.P93RelationalFullereneSubstituentCIPAssignmentsComplete
assert_kernel_only
  TetraStereo.OneCenter.mem_analyzeP93RelationalFullereneAuthorityAssignments_iff
assert_kernel_only
  TetraStereo.OneCenter.p93RelationalFullereneAuthorityAnalyzer_noInvention
assert_kernel_only
  TetraStereo.OneCenter.p93RelationalFullereneAuthorityAnalyzer_noOmission
assert_kernel_only
  TetraStereo.OneCenter.P93RelationalFullereneAuthorityObservation.ValidFor
assert_kernel_only
  TetraStereo.OneCenter.P93RelationalFullereneHandedAuthorityObservation.ValidFor
assert_kernel_only
  TetraStereo.OneCenter.P93RelationalFullereneType4AuthorityObservation.ValidFor
assert_kernel_only
  TetraStereo.OneCenter.P93RelationalFullereneSuperimposedAuthorityObservation.ValidFor
