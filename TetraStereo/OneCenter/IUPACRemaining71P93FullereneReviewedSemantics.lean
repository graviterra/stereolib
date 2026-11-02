import TetraStereo.OneCenter.IUPACRemaining71P93CyclicFamilyPartition
import TetraStereo.OneCenter.IUPACP93FullereneAuthorityCarrier
import TetraStereo.OneCenter.IUPACP93RelationalFullereneSourceAuditSchema

set_option autoImplicit false

/-!
# Reviewed six-row fullerene P-93 authority family

The general-methodology row records the printed four-way decision rule without pretending that
the printed rule supplies a molecule-specific spatial model.  Types 1--3 and superimposition use
the independently derived cage assignment together with the printed numbering handedness.  Type
4 has no cage handedness and instead requires the complete, all-and-only substituent CIP corpus.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

open BlueBookP93.Cyclic

def P93FullereneGeneralMethodologyApplicable
    (policy : P93FullereneAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93FullereneMethodologyAuthorityObservation,
    observation.ValidFor policy source

/-- Exactly the three fullerene classes whose descriptor is cage-numbering handedness. -/
def P93FullereneCageHandednessType : FullereneChiralityType → Prop
  | .inherentlyChiralParent
  | .inherentlyChiralSubstitutionPattern
  | .noninherentlyChiralSubstitutionPattern => True
  | .chiralSubstituentsOnly => False

def P93FullereneTypeApplicable
    (policy : P93FullereneAuthorityPolicy)
    (chiralityType : FullereneChiralityType)
    (source : AuthoritativeChemicalInput) : Prop :=
  P93FullereneCageHandednessType chiralityType ∧
    ∃ observation : P93FullereneAuthorityObservation policy,
      observation.CageHandednessValidFor policy source ∧
        observation.assignment.chiralityType = chiralityType

def P93FullereneType4Applicable
    (policy : P93FullereneAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93FullereneType4AuthorityObservation policy,
    observation.ValidFor policy source

def P93FullereneSuperimposedApplicable
    (policy : P93FullereneAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93FullereneSuperimposedAuthorityObservation policy,
    observation.ValidFor policy source

def p93FullereneGeneralMethodologyReference
    (policy : P93FullereneAuthorityPolicy) : ProvisionReference where
  Observation := P93FullereneMethodologyAuthorityObservation
  Applicable := P93FullereneGeneralMethodologyApplicable policy
  Judges := fun source observation => observation.ValidFor policy source

def p93FullereneTypeReference
    (policy : P93FullereneAuthorityPolicy)
    (chiralityType : FullereneChiralityType) : ProvisionReference where
  Observation := P93FullereneAuthorityObservation policy
  Applicable := P93FullereneTypeApplicable policy chiralityType
  Judges := fun source observation =>
    P93FullereneCageHandednessType chiralityType ∧
      observation.CageHandednessValidFor policy source ∧
        observation.assignment.chiralityType = chiralityType

def p93FullereneType4Reference
    (policy : P93FullereneAuthorityPolicy) : ProvisionReference where
  Observation := P93FullereneType4AuthorityObservation policy
  Applicable := P93FullereneType4Applicable policy
  Judges := fun source observation => observation.ValidFor policy source

def p93FullereneSuperimposedReference
    (policy : P93FullereneAuthorityPolicy) : ProvisionReference where
  Observation := P93FullereneSuperimposedAuthorityObservation policy
  Applicable := P93FullereneSuperimposedApplicable policy
  Judges := fun source observation => observation.ValidFor policy source

/-! The five molecule-specific release rows use the whole-addend relational carrier.  The
site-rooted references above remain compatibility definitions only; projecting a multiport
addend to one attachment site would lose constitutional ownership information. -/

def P93RelationalFullereneTypeApplicable
    (policy : P93RelationalFullereneAuthorityPolicy)
    (chiralityType : FullereneChiralityType)
    (source : AuthoritativeChemicalInput) : Prop :=
  P93FullereneCageHandednessType chiralityType ∧
    ∃ observation : P93RelationalFullereneHandedAuthorityObservation policy,
      observation.ValidFor policy source ∧
        observation.base.assignment.chiralityType = chiralityType

def P93RelationalFullereneType4Applicable
    (policy : P93RelationalFullereneAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93RelationalFullereneType4AuthorityObservation policy,
    observation.ValidFor policy source

def P93RelationalFullereneSuperimposedApplicable
    (policy : P93RelationalFullereneAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93RelationalFullereneSuperimposedAuthorityObservation policy,
    observation.ValidFor policy source

def p93RelationalFullereneTypeReference
    (policy : P93RelationalFullereneAuthorityPolicy)
    (chiralityType : FullereneChiralityType) : ProvisionReference where
  Observation := P93RelationalFullereneHandedAuthorityObservation policy
  Applicable := P93RelationalFullereneTypeApplicable policy chiralityType
  Judges := fun source observation =>
    P93FullereneCageHandednessType chiralityType ∧
      observation.ValidFor policy source ∧
        observation.base.assignment.chiralityType = chiralityType

def p93RelationalFullereneType4Reference
    (policy : P93RelationalFullereneAuthorityPolicy) : ProvisionReference where
  Observation := P93RelationalFullereneType4AuthorityObservation policy
  Applicable := P93RelationalFullereneType4Applicable policy
  Judges := fun source observation => observation.ValidFor policy source

def p93RelationalFullereneSuperimposedReference
    (policy : P93RelationalFullereneAuthorityPolicy) : ProvisionReference where
  Observation := P93RelationalFullereneSuperimposedAuthorityObservation policy
  Applicable := P93RelationalFullereneSuperimposedApplicable policy
  Judges := fun source observation => observation.ValidFor policy source

inductive Remaining71P93FullereneAuthorityRow where
  | generalMethodology
  | inherentParentChirality
  | inherentSubstitutionChirality
  | noninherentSubstitutionChirality
  | chiralSubstituents
  | superimposedStereogenicElements
  deriving DecidableEq, Repr

namespace P93RelationalFullereneReleaseRow


def authorityRow : P93RelationalFullereneReleaseRow → Remaining71P93FullereneAuthorityRow
  | .inherentParent => .inherentParentChirality
  | .inherentSubstitution => .inherentSubstitutionChirality
  | .noninherentSubstitution => .noninherentSubstitutionChirality
  | .chiralSubstituents => .chiralSubstituents
  | .superimposed => .superimposedStereogenicElements

theorem authorityRow_injective : Function.Injective authorityRow := by
  intro left right equal
  cases left <;> cases right <;> simp_all [authorityRow]

end P93RelationalFullereneReleaseRow

namespace Remaining71P93FullereneAuthorityRow

def all : List Remaining71P93FullereneAuthorityRow :=
  [ .generalMethodology
  , .inherentParentChirality
  , .inherentSubstitutionChirality
  , .noninherentSubstitutionChirality
  , .chiralSubstituents
  , .superimposedStereogenicElements
  ]

def provision : Remaining71P93FullereneAuthorityRow → IUPACNormativeProvision
  | .generalMethodology => .p93FullereneGeneralMethodology
  | .inherentParentChirality => .p93FullereneInherentParentChirality
  | .inherentSubstitutionChirality => .p93FullereneInherentSubstitutionChirality
  | .noninherentSubstitutionChirality => .p93FullereneNoninherentSubstitutionChirality
  | .chiralSubstituents => .p93FullereneChiralSubstituents
  | .superimposedStereogenicElements => .p93FullereneSuperimposedStereogenicElements

def kind (_row : Remaining71P93FullereneAuthorityRow) : ProvisionKind :=
  .spatialDescriptor

def reference
    (legacy : P93FullereneAuthorityPolicy)
    (relational : P93RelationalFullereneAuthorityPolicy) :
    Remaining71P93FullereneAuthorityRow → ProvisionReference
  | .generalMethodology => p93FullereneGeneralMethodologyReference legacy
  | .inherentParentChirality =>
      p93RelationalFullereneTypeReference relational .inherentlyChiralParent
  | .inherentSubstitutionChirality =>
      p93RelationalFullereneTypeReference relational .inherentlyChiralSubstitutionPattern
  | .noninherentSubstitutionChirality =>
      p93RelationalFullereneTypeReference relational .noninherentlyChiralSubstitutionPattern
  | .chiralSubstituents =>
      p93RelationalFullereneType4Reference relational
  | .superimposedStereogenicElements =>
      p93RelationalFullereneSuperimposedReference relational

def semantics
    (legacy : P93FullereneAuthorityPolicy)
    (relational : P93RelationalFullereneAuthorityPolicy)
    (row : Remaining71P93FullereneAuthorityRow) : ReviewedProvisionSemantics where
  kind := row.kind
  sourceSuppliesRule := true
  reference := row.reference legacy relational

@[simp] theorem all_length : all.length = 6 := by
  rfl

theorem all_nodup : all.Nodup := by
  decide

@[simp] theorem all_provisions_exact :
    all.map provision =
      Remaining71P93CyclicAuthorityRow.fullereneRows.map
        Remaining71P93CyclicAuthorityRow.provision := by
  rfl

set_option maxRecDepth 16384 in
@[simp] theorem classifier_exact
    (row : Remaining71P93FullereneAuthorityRow) :
    globalProvisionKind row.provision = row.kind := by
  cases row <;> decide

end Remaining71P93FullereneAuthorityRow

def p93FullereneSemanticsSlice : List IUPACNormativeProvision :=
  Remaining71P93FullereneAuthorityRow.all.map
    Remaining71P93FullereneAuthorityRow.provision

@[simp] theorem p93FullereneSemanticsSlice_length :
    p93FullereneSemanticsSlice.length = 6 := by
  rfl

@[simp] theorem p93FullereneSemanticsSlice_exact :
    p93FullereneSemanticsSlice =
      Remaining71P93CyclicAuthorityRow.fullereneRows.map
        Remaining71P93CyclicAuthorityRow.provision := by
  rfl

theorem remaining71P93Fullerene_sourceAuditComplete
    {provision : IUPACNormativeProvision}
    (member : provision ∈ p93FullereneSemanticsSlice) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  have sourceNotIncomplete :
      provision.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources := by
    have everySourceClosed : p93FullereneSemanticsSlice.Forall (fun row =>
        row.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources) := by
      decide
    exact (List.forall_iff_forall_mem.mp everySourceClosed) provision member
  apply Classical.byContradiction
  intro auditIncomplete
  exact sourceNotIncomplete
    ((IUPACNormativeSource.mem_currentIncompleteProvisionAuditSources_iff
      provision.source).2 auditIncomplete)

theorem exists_remaining71P93FullereneAuthorityRow
    {provision : IUPACNormativeProvision}
    (member : provision ∈ p93FullereneSemanticsSlice) :
    ∃ row, row ∈ Remaining71P93FullereneAuthorityRow.all ∧
      row.provision = provision := by
  change provision ∈
    Remaining71P93FullereneAuthorityRow.all.map
      Remaining71P93FullereneAuthorityRow.provision at member
  simpa only [List.mem_map] using member

noncomputable def remaining71P93FullereneAuthorityRowOf
    (provision : IUPACNormativeProvision)
    (member : provision ∈ p93FullereneSemanticsSlice) :
    Remaining71P93FullereneAuthorityRow :=
  Classical.choose (exists_remaining71P93FullereneAuthorityRow member)

theorem remaining71P93FullereneAuthorityRowOf_provision
    (provision : IUPACNormativeProvision)
    (member : provision ∈ p93FullereneSemanticsSlice) :
    (remaining71P93FullereneAuthorityRowOf provision member).provision = provision :=
  (Classical.choose_spec
    (exists_remaining71P93FullereneAuthorityRow member)).2

structure Remaining71P93FullereneReviewedSemanticsTable where
  reviewed : ReviewedProvisionBatch p93FullereneSemanticsSlice.toFinset
  classifier_exact : ∀ {provision : IUPACNormativeProvision}
    (member : provision ∈ p93FullereneSemanticsSlice.toFinset),
      (reviewed.row provision member).kind = globalProvisionKind provision

noncomputable def remaining71P93FullereneReviewedSemantics
    (legacy : P93FullereneAuthorityPolicy)
    (relational : P93RelationalFullereneAuthorityPolicy) :
    Remaining71P93FullereneReviewedSemanticsTable where
  reviewed :=
    { ChemicallyAdmitted := AuthoritativeChemicalInput.StructurallyWellFormed
      row := fun provision member =>
        Remaining71P93FullereneAuthorityRow.semantics legacy relational
          (remaining71P93FullereneAuthorityRowOf provision (by simpa using member))
      sourceAudited := by
        intro provision member
        exact remaining71P93Fullerene_sourceAuditComplete (by simpa using member) }
  classifier_exact := by
    intro provision member
    let row := remaining71P93FullereneAuthorityRowOf provision (by simpa using member)
    have rowProvision : row.provision = provision :=
      remaining71P93FullereneAuthorityRowOf_provision provision (by simpa using member)
    have classified := Remaining71P93FullereneAuthorityRow.classifier_exact row
    change row.kind = globalProvisionKind provision
    simpa [rowProvision] using classified.symm

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93FullereneAuthorityRow.all_length
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93FullereneAuthorityRow.all_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.remaining71P93Fullerene_sourceAuditComplete
