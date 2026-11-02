import TetraStereo.OneCenter.IUPACDescriptorBearingReviewedSemantics

set_option autoImplicit false

/-!
# Exact production-family partition for the positive next-54 scope

The reviewed next-54 batch contains 54 provisions, but exactly eight depiction, nomenclature, and
source-ownership rows are outside descriptor assignment.  This module gives the remaining 46 rows
one proof-relevant four-way ownership type:

* 21 foundational P-92 rows;
* 11 digraph and Rule-1a P-92 rows;
* 3 residual P-93 rows; and
* 11 descriptor-bearing IR-9 rows.

This is only a routing theorem.  It does not manufacture a production interpreter or equate
production with the reviewed reference.  Concrete family adapters must discharge those theorems.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

/-! ## The exact descriptor-bearing IR-9 restriction -/

inductive Next54DescriptorBearingIR9Row where
  | geometryChoice
  | diastereoisomerGeneral
  | configurationIndex
  | absoluteConfigurationGeneral
  | rsTetrahedral
  | caTrigonalPrismatic
  | skewLines
  | skewLinesTrisBidentate
  | skewLinesBisBidentate
  | skewLinesChelateConformations
  | ligandPriorityGeneral
  deriving DecidableEq, Repr

namespace Next54DescriptorBearingIR9Row

def all : List Next54DescriptorBearingIR9Row :=
  [ .geometryChoice
  , .diastereoisomerGeneral
  , .configurationIndex
  , .absoluteConfigurationGeneral
  , .rsTetrahedral
  , .caTrigonalPrismatic
  , .skewLines
  , .skewLinesTrisBidentate
  , .skewLinesBisBidentate
  , .skewLinesChelateConformations
  , .ligandPriorityGeneral
  ]

def toAuthorityRow : Next54DescriptorBearingIR9Row → Next54IR9AuthorityRow
  | .geometryChoice => .geometryChoice
  | .diastereoisomerGeneral => .diastereoisomerGeneral
  | .configurationIndex => .configurationIndex
  | .absoluteConfigurationGeneral => .absoluteConfigurationGeneral
  | .rsTetrahedral => .rsTetrahedral
  | .caTrigonalPrismatic => .caTrigonalPrismatic
  | .skewLines => .skewLines
  | .skewLinesTrisBidentate => .skewLinesTrisBidentate
  | .skewLinesBisBidentate => .skewLinesBisBidentate
  | .skewLinesChelateConformations => .skewLinesChelateConformations
  | .ligandPriorityGeneral => .ligandPriorityGeneral

def provision (row : Next54DescriptorBearingIR9Row) : IUPACNormativeProvision :=
  row.toAuthorityRow.provision

@[simp] theorem all_length : all.length = 11 := by rfl

theorem mem_all (row : Next54DescriptorBearingIR9Row) : row ∈ all := by
  cases row <;> decide

end Next54DescriptorBearingIR9Row

/-! ## The four-way positive production partition -/

inductive Next54ProductionFamilyRow where
  | p92Foundational (row : Next54P92FoundationalAuthorityRow)
  | p92DigraphRule1a (row : Next54P92DigraphRule1aAuthorityRow)
  | p93Residual (row : Next54P93ResidualAuthorityRow)
  | ir9Residual (row : Next54DescriptorBearingIR9Row)
  deriving DecidableEq, Repr

namespace Next54ProductionFamilyRow

def all : List Next54ProductionFamilyRow :=
  Next54P92FoundationalAuthorityRow.all.map .p92Foundational ++
    Next54P92DigraphRule1aAuthorityRow.all.map .p92DigraphRule1a ++
      Next54P93ResidualAuthorityRow.all.map .p93Residual ++
        Next54DescriptorBearingIR9Row.all.map .ir9Residual

def provision : Next54ProductionFamilyRow → IUPACNormativeProvision
  | .p92Foundational row => row.provision
  | .p92DigraphRule1a row => row.provision
  | .p93Residual row => row.provision
  | .ir9Residual row => row.provision

@[simp] theorem all_length : all.length = 46 := by
  simp [all, Next54P92FoundationalAuthorityRow.all,
    Next54P92DigraphRule1aAuthorityRow.all, Next54P93ResidualAuthorityRow.all,
    Next54DescriptorBearingIR9Row.all]

theorem mem_all (row : Next54ProductionFamilyRow) : row ∈ all := by
  cases row with
  | p92Foundational child =>
      cases child <;>
        simp [all, Next54P92FoundationalAuthorityRow.all]
  | p92DigraphRule1a child =>
      cases child <;>
        simp [all, Next54P92DigraphRule1aAuthorityRow.all]
  | p93Residual child =>
      cases child <;>
        simp [all, Next54P93ResidualAuthorityRow.all]
  | ir9Residual child =>
      cases child <;>
        simp [all, Next54DescriptorBearingIR9Row.all]

set_option maxRecDepth 16384 in
theorem all_nodup : all.Nodup := by decide

set_option maxRecDepth 16384 in
theorem all_provisions_nodup : (all.map provision).Nodup := by decide

set_option maxRecDepth 16384 in
/-- The proof-relevant four-family sum is exactly the 46-row descriptor-bearing next-54 scope. -/
theorem all_provisions_exact :
    (all.map provision).toFinset = next54DescriptorBearingProvisions.toFinset := by
  decide

/-- Every reviewed positive next-54 row has one owner in the four-family production partition. -/
theorem exists_familyRow (row : Next54DescriptorBearingReviewedRow) :
    ∃ familyRow, familyRow ∈ all ∧ familyRow.provision = row.provision := by
  have reviewedMember : row.provision ∈ next54DescriptorBearingProvisions.toFinset := by
    simpa using row.2
  have familyMember : row.provision ∈ (all.map provision).toFinset := by
    rw [all_provisions_exact]
    exact reviewedMember
  simpa only [List.mem_toFinset, List.mem_map] using familyMember

noncomputable def familyRowOf
    (row : Next54DescriptorBearingReviewedRow) : Next54ProductionFamilyRow :=
  Classical.choose (exists_familyRow row)

theorem familyRowOf_mem_all (row : Next54DescriptorBearingReviewedRow) :
    familyRowOf row ∈ all :=
  (Classical.choose_spec (exists_familyRow row)).1

@[simp] theorem familyRowOf_provision (row : Next54DescriptorBearingReviewedRow) :
    (familyRowOf row).provision = row.provision :=
  (Classical.choose_spec (exists_familyRow row)).2

end Next54ProductionFamilyRow

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54ProductionFamilyRow.all_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54ProductionFamilyRow.familyRowOf_provision
