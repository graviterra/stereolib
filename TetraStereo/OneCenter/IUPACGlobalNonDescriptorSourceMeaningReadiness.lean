import TetraStereo.OneCenter.IUPACGlobalNegativeClosure
import TetraStereo.OneCenter.IUPACNormativeSemanticsPartition
import TetraStereo.OneCenter.IUPACRemaining71AuthorityDataReviewedSemantics
import TetraStereo.KernelOnly

set_option autoImplicit false


















namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

/-- The exact non-descriptor rows whose independent source meaning is not yet transcribed. -/
def globalNonDescriptorMissingSourceMeaningProvisions : List IUPACNormativeProvision :=
  sourceProvisions .blueBook2013Appendix3 ++
    carbohydrate1996UntranscribedImageSourceSlice

/-- The complementary non-descriptor rows.  `partiallyFormalized` is a maturity statement, not a
claim that a complete reviewed reference already exists. -/
def globalNonDescriptorPartiallyFormalizedSourceMeaningProvisions :
    List IUPACNormativeProvision :=
  globalNonDescriptorProvisions.filter fun provision =>
    !(decide (provision ∈ globalNonDescriptorMissingSourceMeaningProvisions))

/-- Manifest-level source presence.  This is deliberately independent of any caller-supplied
`GlobalNonDescriptorSourceReferenceProgram`. -/
def ManifestFrozenSourcePresent (provision : IUPACNormativeProvision) : Prop :=
  provision ∈ sourceProvisions provision.source

/-- Manifest-level source absence, kept distinct from missing semantic transcription. -/
def ManifestFrozenSourceAbsent (provision : IUPACNormativeProvision) : Prop :=
  ¬ ManifestFrozenSourcePresent provision

@[simp] theorem globalNonDescriptorMissingSourceMeaningProvisionCount :
    globalNonDescriptorMissingSourceMeaningProvisions.length = 595 := by
  simp [globalNonDescriptorMissingSourceMeaningProvisions]

theorem globalNonDescriptorMissingSourceMeaningComponentCounts :
    (sourceProvisions .blueBook2013Appendix3).length = 171 ∧
      carbohydrate1996UntranscribedImageSourceSlice.length = 424 := by
  simp

@[simp] theorem mem_globalNonDescriptorMissingSourceMeaningProvisions_iff
    (provision : IUPACNormativeProvision) :
    provision ∈ globalNonDescriptorMissingSourceMeaningProvisions ↔
      provision ∈ sourceProvisions .blueBook2013Appendix3 ∨
        provision ∈ carbohydrate1996UntranscribedImageSourceSlice := by
  rw [globalNonDescriptorMissingSourceMeaningProvisions, List.mem_append]

theorem globalNonDescriptorMissingSourceMeaningProvisions_nodup :
    globalNonDescriptorMissingSourceMeaningProvisions.Nodup := by
  simpa only [currentAbsentSemanticsProvisions,
    globalNonDescriptorMissingSourceMeaningProvisions] using currentAbsentSemanticsProvisions_nodup

theorem manifestFrozenSourcePresent (provision : IUPACNormativeProvision) :
    ManifestFrozenSourcePresent provision := by
  exact (mem_sourceProvisions_iff provision provision.source).2 rfl

theorem missingSourceMeaning_manifestFrozenSourcePresent
    {provision : IUPACNormativeProvision}
    (_member : provision ∈ globalNonDescriptorMissingSourceMeaningProvisions) :
    ManifestFrozenSourcePresent provision :=
  manifestFrozenSourcePresent provision

theorem missingSourceMeaning_not_manifestFrozenSourceAbsent
    {provision : IUPACNormativeProvision}
    (_member : provision ∈ globalNonDescriptorMissingSourceMeaningProvisions) :
    ¬ ManifestFrozenSourceAbsent provision := by
  exact fun absent => absent (manifestFrozenSourcePresent provision)

theorem mem_globalNonDescriptorMissingSourceMeaningProvisions_currentAbsent
    {provision : IUPACNormativeProvision}
    (member : provision ∈ globalNonDescriptorMissingSourceMeaningProvisions) :
    provision ∈ currentAbsentSemanticsProvisions := by
  simpa only [currentAbsentSemanticsProvisions,
    globalNonDescriptorMissingSourceMeaningProvisions] using member

theorem missingSourceMeaning_currentSemanticsMaturity_eq_absent
    {provision : IUPACNormativeProvision}
    (member : provision ∈ globalNonDescriptorMissingSourceMeaningProvisions) :
    currentSemanticsMaturity provision = .absent := by
  exact (currentSemanticsMaturity_eq_absent_iff provision).2
    (mem_globalNonDescriptorMissingSourceMeaningProvisions_currentAbsent member)

/-- Every parameterized manifest constructor is outside descriptor assignment.  This is a shape
lemma; it does not assign or erase that constructor's source meaning. -/
theorem descriptorAssignmentBearing?_eq_false_of_parameterizedShape
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

theorem globalNonDescriptorMissingSourceMeaning_mem_globalNonDescriptor
    {provision : IUPACNormativeProvision}
    (member : provision ∈ globalNonDescriptorMissingSourceMeaningProvisions) :
    provision ∈ globalNonDescriptorProvisions := by
  apply (mem_globalNonDescriptorProvisions_iff provision).2
  rw [globalNonDescriptorMissingSourceMeaningProvisions] at member
  rcases List.mem_append.mp member with appendixMember | imageMember
  · rw [sourceProvisions] at appendixMember
    obtain ⟨appendix, _, rfl⟩ := List.mem_map.mp appendixMember
    intro bearing
    have falseClassifier := descriptorAssignmentBearing?_eq_false_of_parameterizedShape
      (.appendix3 appendix) rfl
    simp [DescriptorAssignmentBearing, falseClassifier] at bearing
  · rw [carbohydrate1996UntranscribedImageSourceSlice] at imageMember
    obtain ⟨image, _, rfl⟩ := List.mem_map.mp imageMember
    intro bearing
    have falseClassifier := descriptorAssignmentBearing?_eq_false_of_parameterizedShape
      (.carbohydrate1996ImageArtifact image) rfl
    simp [DescriptorAssignmentBearing, falseClassifier] at bearing

@[simp] theorem mem_globalNonDescriptorPartiallyFormalizedSourceMeaningProvisions_iff
    (provision : IUPACNormativeProvision) :
    provision ∈ globalNonDescriptorPartiallyFormalizedSourceMeaningProvisions ↔
      provision ∈ globalNonDescriptorProvisions ∧
        provision ∉ globalNonDescriptorMissingSourceMeaningProvisions := by
  simp [globalNonDescriptorPartiallyFormalizedSourceMeaningProvisions]

theorem globalNonDescriptorPartiallyFormalizedSourceMeaningProvisions_nodup :
    globalNonDescriptorPartiallyFormalizedSourceMeaningProvisions.Nodup :=
  globalNonDescriptorProvisions_nodup.filter _

/-- The two readiness lists exhaust exactly the 2,300 non-descriptor provisions. -/
theorem globalNonDescriptorSourceMeaningReadinessPartition_exact
    (provision : IUPACNormativeProvision) :
    provision ∈ globalNonDescriptorProvisions ↔
      provision ∈ globalNonDescriptorMissingSourceMeaningProvisions ∨
        provision ∈ globalNonDescriptorPartiallyFormalizedSourceMeaningProvisions := by
  constructor
  · intro negativeMember
    by_cases missing :
        provision ∈ globalNonDescriptorMissingSourceMeaningProvisions
    · exact Or.inl missing
    · exact Or.inr
        ((mem_globalNonDescriptorPartiallyFormalizedSourceMeaningProvisions_iff provision).2
          ⟨negativeMember, missing⟩)
  · rintro (missing | partialMember)
    · exact globalNonDescriptorMissingSourceMeaning_mem_globalNonDescriptor missing
    · exact
        ((mem_globalNonDescriptorPartiallyFormalizedSourceMeaningProvisions_iff provision).1
          partialMember).1

theorem globalNonDescriptorSourceMeaningReadinessPartition_disjoint :
    List.Disjoint globalNonDescriptorMissingSourceMeaningProvisions
      globalNonDescriptorPartiallyFormalizedSourceMeaningProvisions := by
  rw [List.disjoint_left]
  intro provision missing partialMember
  exact
    ((mem_globalNonDescriptorPartiallyFormalizedSourceMeaningProvisions_iff provision).1
      partialMember).2 missing

private theorem globalNonDescriptorSourceMeaningReadinessPartition_perm :
    (globalNonDescriptorMissingSourceMeaningProvisions ++
      globalNonDescriptorPartiallyFormalizedSourceMeaningProvisions).Perm
        globalNonDescriptorProvisions := by
  apply (List.perm_ext_iff_of_nodup
    (globalNonDescriptorMissingSourceMeaningProvisions_nodup.append
      globalNonDescriptorPartiallyFormalizedSourceMeaningProvisions_nodup
      globalNonDescriptorSourceMeaningReadinessPartition_disjoint)
    globalNonDescriptorProvisions_nodup).2
  intro provision
  rw [List.mem_append]
  exact (globalNonDescriptorSourceMeaningReadinessPartition_exact provision).symm

@[simp] theorem globalNonDescriptorPartiallyFormalizedSourceMeaningProvisionCount :
    globalNonDescriptorPartiallyFormalizedSourceMeaningProvisions.length = 1705 := by
  have count := globalNonDescriptorSourceMeaningReadinessPartition_perm.length_eq
  rw [List.length_append, globalNonDescriptorMissingSourceMeaningProvisionCount,
    globalNonDescriptorProvisionCount] at count
  omega

private theorem authorityDataProvision_descriptorAssignmentBearing
    (row : Remaining71AuthorityDataRow) :
    DescriptorAssignmentBearing row.provision := by
  rw [DescriptorAssignmentBearing, descriptorAssignmentBearing?,
    Remaining71AuthorityDataRow.classifier_exact]
  cases row <;> rfl

/-- A complementary row has the existing partial formalization, not a completed reviewed source
reference. -/
theorem partiallyFormalizedSourceMeaning_currentSemanticsMaturity_eq
    {provision : IUPACNormativeProvision}
    (member :
      provision ∈ globalNonDescriptorPartiallyFormalizedSourceMeaningProvisions) :
    currentSemanticsMaturity provision = .partiallyFormalized := by
  have memberFacts :=
    (mem_globalNonDescriptorPartiallyFormalizedSourceMeaningProvisions_iff provision).1 member
  apply (currentSemanticsMaturity_eq_partiallyFormalized_iff provision).2
  intro absentMember
  exact memberFacts.2 (by
    simpa only [currentAbsentSemanticsProvisions,
      globalNonDescriptorMissingSourceMeaningProvisions] using absentMember)

theorem partiallyFormalizedSourceMeaning_not_provisionComplete
    {provision : IUPACNormativeProvision}
    (member :
      provision ∈ globalNonDescriptorPartiallyFormalizedSourceMeaningProvisions) :
    currentSemanticsMaturity provision ≠ .provisionComplete := by
  rw [partiallyFormalizedSourceMeaning_currentSemanticsMaturity_eq member]
  decide

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.globalNonDescriptorMissingSourceMeaningProvisionCount
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.missingSourceMeaning_not_manifestFrozenSourceAbsent
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.globalNonDescriptorSourceMeaningReadinessPartition_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.globalNonDescriptorSourceMeaningReadinessPartition_disjoint
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.globalNonDescriptorPartiallyFormalizedSourceMeaningProvisionCount
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.partiallyFormalizedSourceMeaning_currentSemanticsMaturity_eq
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.partiallyFormalizedSourceMeaning_not_provisionComplete
