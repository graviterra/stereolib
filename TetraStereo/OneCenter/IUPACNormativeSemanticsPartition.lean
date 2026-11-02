import TetraStereo.OneCenter.IUPACNormativeManifest
import TetraStereo.KernelOnly

set_option autoImplicit false


















namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision




def currentAbsentSemanticsProvisions : List IUPACNormativeProvision :=
  sourceProvisions .blueBook2013Appendix3 ++
    carbohydrate1996UntranscribedImageSourceSlice

@[simp] theorem currentAbsentSemanticsProvisionCount :
    currentAbsentSemanticsProvisions.length = 595 := by
  simp [currentAbsentSemanticsProvisions]

set_option maxRecDepth 4096 in
/-- The length theorem above counts distinct provisions, not merely list positions.  The proof is
structural: it reuses the source inventories' `Nodup` theorems and constructor disjointness rather
than reducing equality over all 595 rows. -/
theorem currentAbsentSemanticsProvisions_nodup :
    currentAbsentSemanticsProvisions.Nodup := by
  have appendixNodup :
      (sourceProvisions .blueBook2013Appendix3).Nodup := by
    simpa only [sourceProvisions] using
      BlueBookAppendix3Audit.Provision.all_nodup.map
        (by intro left right equal; cases equal; rfl)
  have untranscribedNodup :
      Carbohydrate1996ImageAudit.Provision.notTranscribed.Nodup := by
    exact Carbohydrate1996ImageAudit.Provision.all_nodup.filter _
  have imageNodup : carbohydrate1996UntranscribedImageSourceSlice.Nodup := by
    exact untranscribedNodup.map (by intro left right equal; cases equal; rfl)
  have appendixImageDisjoint :
      List.Disjoint (sourceProvisions .blueBook2013Appendix3)
        carbohydrate1996UntranscribedImageSourceSlice := by
    rw [List.disjoint_left]
    intro provision appendixMember imageMember
    change provision ∈
      BlueBookAppendix3Audit.Provision.all.map
        IUPACNormativeProvision.appendix3 at appendixMember
    obtain ⟨appendix, _, rfl⟩ := List.mem_map.mp appendixMember
    change IUPACNormativeProvision.appendix3 appendix ∈
      Carbohydrate1996ImageAudit.Provision.notTranscribed.map
        IUPACNormativeProvision.carbohydrate1996ImageArtifact at imageMember
    obtain ⟨image, _, equal⟩ := List.mem_map.mp imageMember
    cases equal
  exact appendixNodup.append imageNodup appendixImageDisjoint




private def isDirectAbsentShape : IUPACNormativeProvision → Bool
  | .appendix3 _ => true
  | _ => false

private theorem forall_map_not_directAbsentShape
    {α : Type} (rows : List α) (wrap : α → IUPACNormativeProvision)
    (wrapSafe : ∀ row, isDirectAbsentShape (wrap row) = false) :
    ∀ provision ∈ rows.map wrap, isDirectAbsentShape provision = false := by
  intro provision member
  obtain ⟨row, _, rfl⟩ := List.mem_map.mp member
  exact wrapSafe row

set_option maxRecDepth 16384 in
/-- No row of the partial-semantics inventory is an Appendix-3 structure. The literal chunks are
decided directly; every mapped chunk is discharged by its wrapping constructor, so the delegated
corpora are never normalized. -/
private theorem partiallyFormalized_has_no_directAbsentShape :
    ∀ provision ∈ partiallyFormalizedSemanticsProvisions,
      isDirectAbsentShape provision = false := by
  intro provision member
  simp only [partiallyFormalizedSemanticsProvisions, List.mem_append] at member
  rcases member with member | member | member | member | member | member | member | member |
      member | member | member | member | member | member
  · have safe : ∀ row ∈ independentPrimitiveSemanticsProvisions,
        isDirectAbsentShape row = false := by decide
    exact safe provision member
  · have safe : ∀ row ∈ directPartiallyFormalizedSemanticsProvisions,
        isDirectAbsentShape row = false := by
      set_option maxRecDepth 4096 in decide
    exact safe provision member
  · have safe : ∀ row ∈ ir9SemanticsSlice, isDirectAbsentShape row = false := by decide
    exact safe provision member
  · simp only [p10SemanticsSlice, List.mem_append, or_assoc] at member
    rcases member with member | member | member
    · exact forall_map_not_directAbsentShape _ _ (fun _ => rfl) provision
        (by simpa only [p101SemanticsSlice] using member)
    · exact forall_map_not_directAbsentShape _ _ (fun _ => rfl) provision
        (by simpa only [p102SemanticsSlice] using member)
    · exact forall_map_not_directAbsentShape _ _ (fun _ => rfl) provision
        (by simpa only [p103to107SemanticsSlice] using member)
  · exact forall_map_not_directAbsentShape _ _ (fun _ => rfl) provision
      (by simpa only [retinoid1981SemanticsSlice] using member)
  · exact forall_map_not_directAbsentShape _ _ (fun _ => rfl) provision
      (by simpa only [carotenoid1974SemanticsSlice] using member)
  · exact forall_map_not_directAbsentShape _ _ (fun _ => rfl) provision
      (by simpa only [steroid1989SemanticsSlice] using member)
  · exact forall_map_not_directAbsentShape _ _ (fun _ => rfl) provision
      (by simpa only [cyclitol1973SemanticsSlice] using member)
  · exact forall_map_not_directAbsentShape _ _ (fun _ => rfl) provision
      (by simpa only [nucleicAcid1970SemanticsSlice] using member)
  · exact forall_map_not_directAbsentShape _ _ (fun _ => rfl) provision
      (by simpa only [lipid1976SemanticsSlice] using member)
  · exact forall_map_not_directAbsentShape _ _ (fun _ => rfl) provision
      (by simpa only [glycolipid1997SemanticsSlice] using member)
  · exact forall_map_not_directAbsentShape _ _ (fun _ => rfl) provision
      (by simpa only [aminoAcidPeptide1983SemanticsSlice] using member)
  · simp only [carbohydrate1996SemanticsSlice, List.mem_append, or_assoc] at member
    rcases member with member | member | member | member | member | member | member | member |
        member | member | member | member
    · exact forall_map_not_directAbsentShape _ _ (fun _ => rfl) provision
        (by simpa only [carbohydrate1996ScopeParentSemanticsSlice] using member)
    · exact forall_map_not_directAbsentShape _ _ (fun _ => rfl) provision
        (by simpa only [carbohydrate1996FoundationSemanticsSlice] using member)
    · exact forall_map_not_directAbsentShape _ _ (fun _ => rfl) provision
        (by simpa only [carbohydrate1996NamedParentsSemanticsSlice] using member)
    · exact forall_map_not_directAbsentShape _ _ (fun _ => rfl) provision
        (by simpa only [carbohydrate1996DerivativesSemanticsSlice] using member)
    · exact forall_map_not_directAbsentShape _ _ (fun _ => rfl) provision
        (by simpa only [carbohydrate1996UnsaturatedBranchedSemanticsSlice] using member)
    · exact forall_map_not_directAbsentShape _ _ (fun _ => rfl) provision
        (by simpa only [carbohydrate1996AlditolsAcidsSemanticsSlice] using member)
    · exact forall_map_not_directAbsentShape _ _ (fun _ => rfl) provision
        (by simpa only [carbohydrate1996HeteroSubstitutionAnhydrideSemanticsSlice] using member)
    · exact forall_map_not_directAbsentShape _ _ (fun _ => rfl) provision
        (by simpa only [carbohydrate1996AcetalsSemanticsSlice] using member)
    · exact forall_map_not_directAbsentShape _ _ (fun _ => rfl) provision
        (by simpa only [carbohydrate1996ResiduesIonsSemanticsSlice] using member)
    · exact forall_map_not_directAbsentShape _ _ (fun _ => rfl) provision
        (by simpa only [carbohydrate1996GlycosidesRingsSemanticsSlice] using member)
    · exact forall_map_not_directAbsentShape _ _ (fun _ => rfl) provision
        (by simpa only [carbohydrate1996OligosaccharidesPolysaccharidesSemanticsSlice]
          using member)
    · exact forall_map_not_directAbsentShape _ _ (fun _ => rfl) provision
        (by simpa only [carbohydrate1996AppendixErrataGlossarySemanticsSlice] using member)
  · exact forall_map_not_directAbsentShape _ _ (fun _ => rfl) provision
      (by simpa only [carbohydrate1996TranscribedImageSemanticsSlice] using member)

set_option maxRecDepth 16384 in
/-- Soundness: every listed row really is semantics-absent. -/
theorem absent_of_mem_currentAbsentSemanticsProvisions :
    ∀ provision ∈ currentAbsentSemanticsProvisions,
      currentSemanticsMaturity provision = .absent := by
  intro provision member
  rcases List.mem_append.mp member with appendix | untranscribed
  · apply currentSemanticsMaturity_eq_absent_of_not_mem
    intro partialMember
    have shape := partiallyFormalized_has_no_directAbsentShape provision partialMember
    obtain ⟨row, _, rfl⟩ := List.mem_map.mp
      (show provision ∈
          BlueBookAppendix3Audit.Provision.all.map IUPACNormativeProvision.appendix3
        from appendix)
    exact Bool.noConfusion shape
  · exact every_untranscribed_carbohydrate1996_image_is_source_only provision untranscribed

set_option maxRecDepth 16384 in
/-- Completeness: a semantics-absent provision cannot fall outside the listed open set.  The
proof routes every provision through its source and reuses the existing per-source partial
coverage theorems, so no new whole-manifest normalization is introduced. -/
theorem mem_currentAbsentSemanticsProvisions_of_absent
    (provision : IUPACNormativeProvision)
    (absent : currentSemanticsMaturity provision = .absent) :
    provision ∈ currentAbsentSemanticsProvisions := by
  have sourceMember : provision ∈ sourceProvisions (source provision) :=
    (mem_sourceProvisions_iff provision (source provision)).mpr rfl
  cases hsource : source provision with
  | blueBook2013P9 =>
      rw [hsource] at sourceMember
      rw [every_blueBookP9_provision_has_partial_independent_semantics
        provision sourceMember] at absent
      exact absurd absent (by decide)
  | blueBook2013P10 =>
      rw [hsource] at sourceMember
      rw [every_p10_provision_has_partial_independent_semantics provision sourceMember] at absent
      exact absurd absent (by decide)
  | blueBook2013Appendix3 =>
      rw [hsource] at sourceMember
      exact List.mem_append_left _ sourceMember
  | graphicalRepresentation2006 =>
      rw [hsource] at sourceMember
      rw [← allDrawingSemanticsSlices_exact] at sourceMember
      obtain ⟨_, _, _, _, _, _, _, _, _, hST0, hST1Tetrahedral, hST1Special, hST2, hST3to6, _⟩ :=
        current_semantics_slices_are_honestly_partial
      simp only [allDrawingSemanticsSlices, List.mem_append, or_assoc] at sourceMember
      rcases sourceMember with member | member | member | member | member
      · rw [hST0 provision member] at absent
        exact absurd absent (by decide)
      · rw [hST1Tetrahedral provision member] at absent
        exact absurd absent (by decide)
      · rw [hST1Special provision member] at absent
        exact absurd absent (by decide)
      · rw [hST2 provision member] at absent
        exact absurd absent (by decide)
      · rw [hST3to6 provision member] at absent
        exact absurd absent (by decide)
  | redBook2005IR9 =>
      rw [hsource] at sourceMember
      rw [every_ir9_provision_has_partial_independent_semantics provision sourceMember] at absent
      exact absurd absent (by decide)
  | periodicTable2022 =>
      rw [hsource] at sourceMember
      simp only [sourceProvisions, List.mem_singleton] at sourceMember
      subst sourceMember
      rw [periodicAtomicNumbers_semantics_partiallyFormalized] at absent
      exact absurd absent (by decide)
  | atomicWeights2021 =>
      rw [hsource] at sourceMember
      simp only [sourceProvisions, List.mem_singleton] at sourceMember
      subst sourceMember
      rw [standardAtomicWeights_semantics_partiallyFormalized] at absent
      exact absurd absent (by decide)
  | atomicMasses2020 =>
      rw [hsource] at sourceMember
      simp only [sourceProvisions, List.mem_singleton] at sourceMember
      subst sourceMember
      rw [isotopeAtomicMasses_semantics_partiallyFormalized] at absent
      exact absurd absent (by decide)
  | steroidRecommendations1989 =>
      rw [hsource] at sourceMember
      rw [every_steroid1989_provision_has_partial_independent_semantics
        provision sourceMember] at absent
      exact absurd absent (by decide)
  | carotenoidRules1974 =>
      rw [hsource] at sourceMember
      rw [every_carotenoid1974_provision_has_partial_independent_semantics
        provision sourceMember] at absent
      exact absurd absent (by decide)
  | retinoidRecommendations1981 =>
      rw [hsource] at sourceMember
      rw [every_retinoid1981_provision_has_partial_independent_semantics
        provision sourceMember] at absent
      exact absurd absent (by decide)
  | carbohydrateRecommendations1996 =>
      rw [hsource] at sourceMember
      rw [← carbohydrate1996SourcePartition_exact] at sourceMember
      rcases List.mem_append.mp sourceMember with textual | image
      · rw [every_carbohydrate1996_textual_provision_has_partial_independent_semantics
          provision textual] at absent
        exact absurd absent (by decide)
      · simp only [carbohydrate1996ImageArtifactSourceSlice] at image
        obtain ⟨imageRow, imageMember, rfl⟩ := List.mem_map.mp image
        by_cases transcribedFlag :
            Carbohydrate1996ImageAudit.Provision.symbolicTemplateTranscribed imageRow = true
        · have transcribedMember :
              IUPACNormativeProvision.carbohydrate1996ImageArtifact imageRow ∈
                carbohydrate1996TranscribedImageSemanticsSlice := by
            simp only [carbohydrate1996TranscribedImageSemanticsSlice,
              Carbohydrate1996ImageAudit.Provision.transcribed]
            exact List.mem_map_of_mem
              (f := IUPACNormativeProvision.carbohydrate1996ImageArtifact)
              (List.mem_filter.mpr ⟨imageMember, transcribedFlag⟩)
          rw [every_transcribed_carbohydrate1996_image_is_partially_formalized
            _ transcribedMember] at absent
          exact absurd absent (by decide)
        · apply List.mem_append_right
          simp only [carbohydrate1996UntranscribedImageSourceSlice,
            Carbohydrate1996ImageAudit.Provision.notTranscribed]
          refine List.mem_map_of_mem
            (f := IUPACNormativeProvision.carbohydrate1996ImageArtifact) ?_
          refine List.mem_filter.mpr ⟨imageMember, ?_⟩
          rw [Bool.not_eq_true] at transcribedFlag
          simp [transcribedFlag]
  | aminoAcidPeptideRecommendations1983 =>
      rw [hsource] at sourceMember
      rw [every_aminoAcidPeptide1983_provision_has_partial_independent_semantics
        provision sourceMember] at absent
      exact absurd absent (by decide)
  | cyclitolRecommendations1973 =>
      rw [hsource] at sourceMember
      rw [every_cyclitol1973_provision_has_partial_independent_semantics
        provision sourceMember] at absent
      exact absurd absent (by decide)
  | nucleicAcidRecommendations1970 =>
      rw [hsource] at sourceMember
      rw [every_nucleicAcid1970_provision_has_partial_independent_semantics
        provision sourceMember] at absent
      exact absurd absent (by decide)
  | lipidRecommendations1976 =>
      rw [hsource] at sourceMember
      rw [every_lipid1976_provision_has_partial_independent_semantics
        provision sourceMember] at absent
      exact absurd absent (by decide)
  | glycolipidRecommendations1997 =>
      rw [hsource] at sourceMember
      rw [every_glycolipid1997_provision_has_partial_independent_semantics
        provision sourceMember] at absent
      exact absurd absent (by decide)

/-- The open-set characterization: a provision is semantics-absent exactly when it is one of the
595 listed rows. -/
theorem currentSemanticsMaturity_eq_absent_iff (provision : IUPACNormativeProvision) :
    currentSemanticsMaturity provision = .absent ↔
      provision ∈ currentAbsentSemanticsProvisions :=
  ⟨mem_currentAbsentSemanticsProvisions_of_absent provision,
    absent_of_mem_currentAbsentSemanticsProvisions provision⟩

/-- No provision is provision-complete yet; the complete inventory is deliberately empty. -/
theorem currentSemanticsMaturity_ne_provisionComplete (provision : IUPACNormativeProvision) :
    currentSemanticsMaturity provision ≠ .provisionComplete := by
  unfold currentSemanticsMaturity
  simp only [provisionCompleteSemanticsProvisions, List.not_mem_nil, if_false]
  split <;> simp

/-- Complement form of the partition: partial formalization holds exactly off the open set. -/
theorem currentSemanticsMaturity_eq_partiallyFormalized_iff
    (provision : IUPACNormativeProvision) :
    currentSemanticsMaturity provision = .partiallyFormalized ↔
      provision ∉ currentAbsentSemanticsProvisions := by
  constructor
  · intro partialSem member
    rw [absent_of_mem_currentAbsentSemanticsProvisions provision member] at partialSem
    exact absurd partialSem (by decide)
  · intro notMember
    cases maturity : currentSemanticsMaturity provision with
    | provisionComplete =>
        exact absurd maturity (currentSemanticsMaturity_ne_provisionComplete provision)
    | partiallyFormalized => rfl
    | absent =>
        exact absurd (mem_currentAbsentSemanticsProvisions_of_absent provision maturity)
          notMember

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.currentAbsentSemanticsProvisionCount
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.currentAbsentSemanticsProvisions_nodup
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.absent_of_mem_currentAbsentSemanticsProvisions
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.mem_currentAbsentSemanticsProvisions_of_absent
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.currentSemanticsMaturity_eq_absent_iff
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.currentSemanticsMaturity_ne_provisionComplete
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.currentSemanticsMaturity_eq_partiallyFormalized_iff

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.periodicAtomicNumbers_semantics_partiallyFormalized
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.standardAtomicWeights_semantics_partiallyFormalized
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.isotopeAtomicMasses_semantics_partiallyFormalized
