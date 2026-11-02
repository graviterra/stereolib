import TetraStereo.OneCenter.IUPACPrimitive35ReviewedSemantics
import TetraStereo.OneCenter.IUPACNext54ReviewedSemantics

set_option autoImplicit false

/-!
# Exhaustive semantic-family classification of the 2,452-row manifest

This module supplies the global *kind* layer required before a complete reviewed reference table
can be compiled.  It preserves the 35-row and 54-row reviewed classifiers exactly, then classifies
the remaining frozen source inventories by their audited role:

* P-93/P-94 configuration and conformation rows are spatial-descriptor rows;
* graphical and carbohydrate-image artifacts are depiction rows;
* Appendix-3 structures and the three atomic-data rows are authority data;
* P-90 and the IR-9.3 umbrella are source-scope rows; and
* the organic/delegated recommendation corpora are nomenclature rows.

This is deliberately not a `ReviewedProvisionSemanticsTable`: a semantic family is not a
substitute for a source-faithful dependent applicability/judgment relation.  The latter remains
the next global transcription boundary.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

/-- Source-role classifier used only after the exact reviewed and P-93/P-94 branches have been
removed.  The explicit constructor cases prevent image artifacts and authority data from falling
through to nomenclature merely because they are carried by a delegated source. -/
def residualGlobalProvisionKind : IUPACNormativeProvision → ProvisionKind
  | .p90ScopeAndTerminology => .sourceOnly
  | .ir9PolyhedralConfiguration => .sourceOnly
  | .appendix3 _ => .authorityData
  | .periodicAtomicNumbers => .authorityData
  | .standardAtomicWeights => .authorityData
  | .isotopeAtomicMasses => .authorityData
  | .carbohydrate1996ImageArtifact _ => .depiction
  | provision =>
      match provision.source with
      | .graphicalRepresentation2006 => .depiction
      | .blueBook2013Appendix3 => .authorityData
      | .periodicTable2022 | .atomicWeights2021 | .atomicMasses2020 => .authorityData
      | _ => .nomenclature

/-- Total global family classifier.  The two reviewed work units have precedence, so later broad
source classes cannot silently reroute any of their 89 dependent rows. -/
def globalProvisionKind (provision : IUPACNormativeProvision) : ProvisionKind :=
  match primitive35Kind? provision with
  | some kind => kind
  | none =>
      match next54Kind? provision with
      | some kind => kind
      | none =>
          if provision ∈ p93SourceProvisions then .spatialDescriptor
          else if provision ∈ p94SemanticsSlice then .spatialDescriptor
          else residualGlobalProvisionKind provision

/-! ## Frozen-inventory coverage guards -/

set_option maxRecDepth 16384 in
/-- Every Blue Book P-9 row is owned by one of the explicit P-90--P-94 branches above.  This
guard makes the residual P-9 fallback unreachable for the current 130-row source inventory. -/
theorem blueBookP9_globalKindRouting_exact
    {provision : IUPACNormativeProvision}
    (member : provision ∈ sourceProvisions .blueBook2013P9) :
    provision = .p90ScopeAndTerminology ∨
      provision ∈ primitive35Provisions ∨
      provision ∈ next54Provisions ∨
      provision ∈ p93SourceProvisions ∨
      provision ∈ p94SemanticsSlice := by
  have routed : (sourceProvisions .blueBook2013P9).Forall (fun row =>
      row = .p90ScopeAndTerminology ∨
        row ∈ primitive35Provisions ∨
        row ∈ next54Provisions ∨
        row ∈ p93SourceProvisions ∨
        row ∈ p94SemanticsSlice) := by
    decide
  exact (List.forall_iff_forall_mem.mp routed) provision member

/-- The first reviewed compiler family retains its exact reviewed semantic kind globally. -/
theorem globalProvisionKind_eq_primitive35Reviewed
    {provision : IUPACNormativeProvision}
    (member : provision ∈ primitive35Provisions) :
    globalProvisionKind provision =
      (primitive35ReviewedSemantics.row provision member).kind := by
  have classified := primitive35ReviewedSemantics.classifier_exact member
  simp [globalProvisionKind, classified]

/-- The second reviewed compiler family also retains its exact reviewed semantic kind globally. -/
theorem globalProvisionKind_eq_next54Reviewed
    {provision : IUPACNormativeProvision}
    (member : provision ∈ next54Provisions.toFinset) :
    globalProvisionKind provision =
      (next54ReviewedSemantics.reviewed.row provision member).kind := by
  have nextMember : provision ∈ next54Provisions := by simpa using member
  have notPrimitive : provision ∉ primitive35Provisions := by
    intro primitiveMember
    exact (List.disjoint_left.mp next54Provisions_disjoint_primitive35)
      nextMember primitiveMember
  have primitiveNone : primitive35Kind? provision = none := by
    cases primitiveEq : primitive35Kind? provision with
    | none => rfl
    | some kind =>
        have present : (primitive35Kind? provision).isSome = true := by
          simp [primitiveEq]
        exact False.elim (notPrimitive ((primitive35Kind?_isSome_iff provision).mp present))
  have classified := next54ReviewedSemantics.classifier_exact member
  have nextClassified : next54Kind? provision =
      some (next54ReviewedSemantics.reviewed.row provision member).kind := by
    calc
      next54Kind? provision = some (next54Kind provision nextMember) :=
        next54Kind?_eq_some provision nextMember
      _ = some (next54ReviewedSemantics.reviewed.row provision member).kind :=
        congrArg some classified.symm
  simp [globalProvisionKind, primitiveNone, nextClassified]

/-! ## Exhaustive, disjoint 2,452-row partition -/

def globalProvisionsOfKind (kind : ProvisionKind) : List IUPACNormativeProvision :=
  all.filter fun provision => decide (globalProvisionKind provision = kind)

theorem mem_globalProvisionsOfKind_iff
    (provision : IUPACNormativeProvision) (kind : ProvisionKind) :
    provision ∈ globalProvisionsOfKind kind ↔ globalProvisionKind provision = kind := by
  simp [globalProvisionsOfKind, mem_all]

/-- Every manifest row belongs to its generated family partition. -/
theorem globalKindPartition_exhaustive (provision : IUPACNormativeProvision) :
    provision ∈ globalProvisionsOfKind (globalProvisionKind provision) :=
  (mem_globalProvisionsOfKind_iff provision _).2 rfl

/-- Distinct generated semantic-family partitions share no manifest row. -/
theorem globalKindPartitions_disjoint
    (left right : ProvisionKind) (different : left ≠ right) :
    List.Disjoint (globalProvisionsOfKind left) (globalProvisionsOfKind right) := by
  rw [List.disjoint_left]
  intro provision leftMember rightMember
  have leftKind := (mem_globalProvisionsOfKind_iff provision left).1 leftMember
  have rightKind := (mem_globalProvisionsOfKind_iff provision right).1 rightMember
  exact different (leftKind.symm.trans rightKind)

/-- Every one of the 2,452 manifest rows has exactly one generated semantic family. -/
theorem globalKindPartition_existsUnique (provision : IUPACNormativeProvision) :
    ∃! kind, provision ∈ globalProvisionsOfKind kind := by
  refine ⟨globalProvisionKind provision, globalKindPartition_exhaustive provision, ?_⟩
  intro kind member
  exact ((mem_globalProvisionsOfKind_iff provision kind).1 member).symm

@[simp] theorem globalKindPartitionManifestCount : all.length = 2452 :=
  length_all

/-! ## Descriptor-assignment applicability partition -/

/-- The only authority-data rows consumed directly by descriptor assignment.  Appendix-3 retained
parent structures remain authority data at the source level but are outside this operation. -/
def descriptorAssignmentAuthorityDataProvisions : List IUPACNormativeProvision :=
  [ .periodicAtomicNumbers
  , .standardAtomicWeights
  , .isotopeAtomicMasses
  ]

/-- Computable operation-level applicability derived from the global family classification plus
the exact three-row authority-data input set. -/
def descriptorAssignmentBearing? (provision : IUPACNormativeProvision) : Bool :=
  match globalProvisionKind provision with
  | .sequenceRule | .perception | .spatialDescriptor => true
  | .authorityData => decide (provision ∈ descriptorAssignmentAuthorityDataProvisions)
  | .depiction | .nomenclature | .sourceOnly => false

/-- Propositional view of the exact computable descriptor-assignment partition. -/
def DescriptorAssignmentBearing (provision : IUPACNormativeProvision) : Prop :=
  descriptorAssignmentBearing? provision = true

def descriptorAssignmentBearingProvisions : List IUPACNormativeProvision :=
  all.filter descriptorAssignmentBearing?

def descriptorAssignmentNegativeProvisions : List IUPACNormativeProvision :=
  all.filter fun provision => !descriptorAssignmentBearing? provision

private theorem length_filter_add_length_filter_not
    {Alpha : Type} (predicate : Alpha → Bool) (items : List Alpha) :
    (items.filter predicate).length +
      (items.filter fun item => !predicate item).length = items.length := by
  induction items with
  | nil => rfl
  | cons item items inductionHypothesis =>
      cases predicateEq : predicate item <;> simp [predicateEq] <;> omega

private theorem descriptorAssignmentBearing?_eq_false_of_isParameterized
    (provision : IUPACNormativeProvision)
    (parameterized : isParameterizedProvision provision = true) :
    descriptorAssignmentBearing? provision = false :=
  match provision with
  | .p10 _ | .appendix3 _ | .retinoid1981 _ | .carotenoid1974 _ | .steroid1989 _
  | .cyclitol1973 _ | .nucleicAcid1970 _ | .lipid1976 _ | .glycolipid1997 _
  | .aminoAcidPeptide1983 _ | .carbohydrate1996Foundation _
  | .carbohydrate1996NamedParents _ | .carbohydrate1996ScopeParent _
  | .carbohydrate1996Derivatives _ | .carbohydrate1996UnsaturatedBranched _
  | .carbohydrate1996AlditolsAcids _ | .carbohydrate1996HeteroSubstitutionAnhydride _
  | .carbohydrate1996Acetals _ | .carbohydrate1996ResiduesIons _
  | .carbohydrate1996GlycosidesRings _
  | .carbohydrate1996OligosaccharidesPolysaccharides _
  | .carbohydrate1996AppendixErrataGlossary _ | .carbohydrate1996ImageArtifact _ => by
      rfl
  | other => by
      cases other <;> simp_all [isParameterizedProvision] <;> rfl

private theorem parameterizedProvisions_descriptorAssignmentBearing?_eq_false :
    parameterizedProvisions.Forall
      (fun provision => descriptorAssignmentBearing? provision = false) := by
  rw [List.forall_iff_forall_mem]
  intro provision member
  exact descriptorAssignmentBearing?_eq_false_of_isParameterized provision
    (parameterizedProvisions_are_parameterized provision member)

private theorem filter_eq_nil_of_forall_bool_false
    {Alpha : Type} (predicate : Alpha → Bool) {items : List Alpha}
    (allFalse : items.Forall (fun item => predicate item = false)) :
    items.filter predicate = [] := by
  induction items with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      have allMem := List.forall_iff_forall_mem.mp allFalse
      have headFalse := allMem head (by simp)
      have tailFalse : tail.Forall (fun item => predicate item = false) :=
        List.forall_iff_forall_mem.mpr fun item member => allMem item (by simp [member])
      simp [headFalse, inductionHypothesis tailFalse]

private theorem filter_not_eq_self_of_forall_bool_false
    {Alpha : Type} (predicate : Alpha → Bool) {items : List Alpha}
    (allFalse : items.Forall (fun item => predicate item = false)) :
    items.filter (fun item => !predicate item) = items := by
  induction items with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      have allMem := List.forall_iff_forall_mem.mp allFalse
      have headFalse := allMem head (by simp)
      have tailFalse : tail.Forall (fun item => predicate item = false) :=
        List.forall_iff_forall_mem.mpr fun item member => allMem item (by simp [member])
      simp [headFalse, inductionHypothesis tailFalse]

set_option maxRecDepth 32768 in
@[simp] theorem descriptorAssignmentBearingProvisionCount :
    descriptorAssignmentBearingProvisions.length = 152 := by
  rw [descriptorAssignmentBearingProvisions, all_eq_core_append_parameterized,
    List.filter_append, List.length_append]
  have coreCount : (coreProvisions.filter descriptorAssignmentBearing?).length = 152 := by
    decide
  have parameterizedCount :
      (parameterizedProvisions.filter descriptorAssignmentBearing?).length = 0 := by
    simp [filter_eq_nil_of_forall_bool_false descriptorAssignmentBearing?
      parameterizedProvisions_descriptorAssignmentBearing?_eq_false]
  omega

set_option maxRecDepth 16384 in
@[simp] theorem descriptorAssignmentNegativeProvisionCount :
    descriptorAssignmentNegativeProvisions.length = 2300 := by
  rw [descriptorAssignmentNegativeProvisions, all_eq_core_append_parameterized,
    List.filter_append, List.length_append]
  have coreLength : coreProvisions.length = 244 := by decide
  have coreBearingLength :
      (coreProvisions.filter descriptorAssignmentBearing?).length = 152 := by decide
  have corePartitionLength :
      (coreProvisions.filter descriptorAssignmentBearing?).length +
        (coreProvisions.filter fun provision => !descriptorAssignmentBearing? provision).length =
          coreProvisions.length :=
    length_filter_add_length_filter_not descriptorAssignmentBearing? coreProvisions
  have parameterizedNegative :
      parameterizedProvisions.filter (fun provision => !descriptorAssignmentBearing? provision) =
        parameterizedProvisions :=
    filter_not_eq_self_of_forall_bool_false descriptorAssignmentBearing?
      parameterizedProvisions_descriptorAssignmentBearing?_eq_false
  have parameterizedLength : parameterizedProvisions.length = 2208 := by
    have totalLength : coreProvisions.length + parameterizedProvisions.length = 2452 := by
      rw [← List.length_append, ← all_eq_core_append_parameterized]
      exact length_all
    omega
  rw [parameterizedNegative]
  omega

theorem descriptorAssignmentBearingProvisions_nodup :
    descriptorAssignmentBearingProvisions.Nodup :=
  all_nodup.filter _

theorem descriptorAssignmentNegativeProvisions_nodup :
    descriptorAssignmentNegativeProvisions.Nodup :=
  all_nodup.filter _

theorem mem_descriptorAssignmentBearingProvisions_iff
  (provision : IUPACNormativeProvision) :
    provision ∈ descriptorAssignmentBearingProvisions ↔
      DescriptorAssignmentBearing provision := by
  simp [descriptorAssignmentBearingProvisions, DescriptorAssignmentBearing, mem_all]

theorem mem_descriptorAssignmentNegativeProvisions_iff
  (provision : IUPACNormativeProvision) :
    provision ∈ descriptorAssignmentNegativeProvisions ↔
      ¬DescriptorAssignmentBearing provision := by
  simp [descriptorAssignmentNegativeProvisions, DescriptorAssignmentBearing, mem_all]

theorem descriptorAssignmentPartitions_disjoint :
    List.Disjoint descriptorAssignmentBearingProvisions
      descriptorAssignmentNegativeProvisions := by
  rw [List.disjoint_left]
  intro provision bearingMember negativeMember
  exact (mem_descriptorAssignmentNegativeProvisions_iff provision).1 negativeMember
    ((mem_descriptorAssignmentBearingProvisions_iff provision).1 bearingMember)

/-- Every manifest row is classified exactly once as operationally descriptor-bearing or
negative, and the two exact counts sum to all 2,452 rows. -/
theorem descriptorAssignmentPartition_exact (provision : IUPACNormativeProvision) :
    (provision ∈ descriptorAssignmentBearingProvisions ∨
      provision ∈ descriptorAssignmentNegativeProvisions) ∧
    ¬(provision ∈ descriptorAssignmentBearingProvisions ∧
      provision ∈ descriptorAssignmentNegativeProvisions) := by
  by_cases bearing : DescriptorAssignmentBearing provision
  · exact ⟨Or.inl ((mem_descriptorAssignmentBearingProvisions_iff provision).2 bearing),
      fun overlap =>
        (mem_descriptorAssignmentNegativeProvisions_iff provision).1 overlap.2 bearing⟩
  · exact ⟨Or.inr ((mem_descriptorAssignmentNegativeProvisions_iff provision).2 bearing),
      fun overlap => bearing
        ((mem_descriptorAssignmentBearingProvisions_iff provision).1 overlap.1)⟩

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.blueBookP9_globalKindRouting_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.globalProvisionKind_eq_primitive35Reviewed
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.globalProvisionKind_eq_next54Reviewed
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.globalKindPartition_exhaustive
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.globalKindPartitions_disjoint
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.globalKindPartition_existsUnique
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.globalKindPartitionManifestCount
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.descriptorAssignmentBearingProvisionCount
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.descriptorAssignmentNegativeProvisionCount
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.descriptorAssignmentPartitions_disjoint
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.descriptorAssignmentPartition_exact
