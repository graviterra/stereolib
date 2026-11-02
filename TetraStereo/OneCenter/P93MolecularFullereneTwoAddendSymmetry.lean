import TetraStereo.OneCenter.P93MolecularFullereneRelationalSymmetry

set_option autoImplicit false

/-!
# Exact symmetry collapse for the two-addend P-93 derivatives

All five printed P-93.5.6 derivative examples contain exactly two whole constitutional addends.
This module eliminates the existential permutation of an abstract owned-addend subtype: every
preserving permutation either fixes both addends or swaps them. For the common achiral test
addend, preservation then reduces exactly to finite equality of the two attachment-site images.
-/

namespace TetraStereo.OneCenter.BlueBookP93.Cyclic

noncomputable section

/-- A permutation of a two-element owned-addend family has exactly the fixed or swapped action. -/
theorem exists_ownedAddendEquiv_forall_iff_two
    {molecule : RawMolecule} {carrier : Finset Nat}
    (evidence : MolecularFullereneAddendRelationalEvidence molecule carrier)
    (first second : MolecularFullereneAddend)
    (addendsExact : evidence.addends = [first, second])
    (relation : MolecularFullereneAddend → MolecularFullereneAddend → Prop) :
    (∃ equivalence : MolecularFullereneOwnedAddend evidence ≃
        MolecularFullereneOwnedAddend evidence,
      ∀ source, relation source.1 (equivalence source).1) ↔
      (relation first first ∧ relation second second) ∨
        (relation first second ∧ relation second first) := by
  have distinct : first ≠ second := by
    have nodup := evidence.addendsNodup
    rw [addendsExact] at nodup
    simpa using nodup
  let firstOwned : MolecularFullereneOwnedAddend evidence :=
    ⟨first, by simp [addendsExact]⟩
  let secondOwned : MolecularFullereneOwnedAddend evidence :=
    ⟨second, by simp [addendsExact]⟩
  have owned_cases : ∀ owned : MolecularFullereneOwnedAddend evidence,
      owned = firstOwned ∨ owned = secondOwned := by
    intro owned
    have member : owned.1 = first ∨ owned.1 = second := by
      simpa [addendsExact] using owned.2
    rcases member with eq | eq
    · left
      apply Subtype.ext
      exact eq
    · right
      apply Subtype.ext
      exact eq
  constructor
  · rintro ⟨equivalence, preserves⟩
    rcases owned_cases (equivalence firstOwned) with firstImage | secondImage
    · left
      have secondImage' : equivalence secondOwned = secondOwned := by
        rcases owned_cases (equivalence secondOwned) with impossible | exactImage
        · exact False.elim (distinct (by
            have := equivalence.injective (firstImage.trans impossible.symm)
            exact congrArg Subtype.val this))
        · exact exactImage
      exact ⟨by simpa [firstOwned, firstImage] using preserves firstOwned,
        by simpa [secondOwned, secondImage'] using preserves secondOwned⟩
    · right
      have firstImage' : equivalence secondOwned = firstOwned := by
        rcases owned_cases (equivalence secondOwned) with exactImage | impossible
        · exact exactImage
        · exact False.elim (distinct (by
            have := equivalence.injective (secondImage.trans impossible.symm)
            exact congrArg Subtype.val this))
      exact ⟨by simpa [firstOwned, secondOwned, secondImage] using preserves firstOwned,
        by simpa [firstOwned, secondOwned, firstImage'] using preserves secondOwned⟩
  · rintro (fixed | swapped)
    · refine ⟨Equiv.refl _, ?_⟩
      intro source
      rcases owned_cases source with rfl | rfl
      · exact fixed.1
      · exact fixed.2
    · refine ⟨Equiv.swap firstOwned secondOwned, ?_⟩
      intro source
      rcases owned_cases source with rfl | rfl
      · simpa [Equiv.swap_apply_def, firstOwned, secondOwned, distinct] using swapped.1
      · simpa [Equiv.swap_apply_def, firstOwned, secondOwned, distinct] using swapped.2

/-- Cage image of one complete whole-addend attachment-site set. -/
def mappedMolecularFullereneAttachmentSites
    (input : MolecularFullereneConfigurationInput)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input))
    (addend : MolecularFullereneAddend) : Finset Nat :=
  addend.attachmentSites.image (mapMolecularFullereneCarrierAtom input symmetry)

/-- A full constitutional isomorphism along a cage symmetry necessarily maps the complete source
attachment-site set onto the complete target set.  This forgetful theorem is the key rejection
principle for finite audits: disproving one finite set equality disproves every possible external
atom, site, and port equivalence at once. -/
theorem MolecularFullereneAddend.ConstitutionallyIsomorphicAlong.mappedAttachmentSites_eq
    {molecule : RawMolecule} {input : MolecularFullereneConfigurationInput}
    {symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input)}
    {first second : MolecularFullereneAddend}
    (along : first.ConstitutionallyIsomorphicAlong molecule input symmetry second) :
    mappedMolecularFullereneAttachmentSites input symmetry first = second.attachmentSites := by
  rcases along with
    ⟨_atomEquivalence, _atoms, _bonds, siteEquivalence, agrees,
      _portEquivalence, _sites, _endpoints, _attachmentBonds⟩
  ext site
  constructor
  · intro mappedMember
    obtain ⟨sourceSite, sourcePresent, mapped⟩ := Finset.mem_image.mp mappedMember
    let source : { site // site ∈ first.attachmentSites } := ⟨sourceSite, sourcePresent⟩
    have targetPresent : (siteEquivalence source).1 ∈ second.attachmentSites :=
      (siteEquivalence source).2
    have targetEq : (siteEquivalence source).1 = site := by
      rw [agrees source]
      exact mapped
    exact targetEq ▸ targetPresent
  · intro targetPresent
    let target : { site // site ∈ second.attachmentSites } := ⟨site, targetPresent⟩
    let source := siteEquivalence.symm target
    refine Finset.mem_image.mpr ⟨source.1, source.2, ?_⟩
    have agreesSource := agrees source
    change (siteEquivalence source).1 =
      mapMolecularFullereneCarrierAtom input symmetry source.1 at agreesSource
    simpa [source, target] using agreesSource.symm

/-- The abstract unlabeled-port equivalence is exactly equality with the finite cage-image set. -/
theorem molecularFullereneUnlabeledSameTestPortEquivalence_iff_mappedSites
    (input : MolecularFullereneConfigurationInput)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input))
    (first second : MolecularFullereneAddend)
    (firstSites : first.attachmentSites ⊆ input.carrier) :
    MolecularFullereneUnlabeledSameTestPortEquivalence input symmetry first second ↔
      mappedMolecularFullereneAttachmentSites input symmetry first = second.attachmentSites := by
  constructor
  · rintro ⟨equivalence, agrees⟩
    ext site
    constructor
    · intro mappedMember
      obtain ⟨sourceSite, sourcePresent, mapped⟩ := Finset.mem_image.mp mappedMember
      let source : { site // site ∈ first.attachmentSites } := ⟨sourceSite, sourcePresent⟩
      have targetPresent : (equivalence source).1 ∈ second.attachmentSites :=
        (equivalence source).2
      have targetEq : (equivalence source).1 = site := by
        rw [agrees source]
        exact mapped
      exact targetEq ▸ targetPresent
    · intro targetPresent
      let target : { site // site ∈ second.attachmentSites } := ⟨site, targetPresent⟩
      let source := equivalence.symm target
      refine Finset.mem_image.mpr ⟨source.1, source.2, ?_⟩
      have agreesSource := agrees source
      change (equivalence source).1 =
        mapMolecularFullereneCarrierAtom input symmetry source.1 at agreesSource
      simpa [source, target] using agreesSource.symm
  · intro mappedExact
    let mapSite : { site // site ∈ first.attachmentSites } →
        { site // site ∈ second.attachmentSites } := fun site =>
      ⟨mapMolecularFullereneCarrierAtom input symmetry site.1, by
        rw [← mappedExact]
        exact Finset.mem_image.mpr ⟨site.1, site.2, rfl⟩⟩
    have mapSiteInjective : Function.Injective mapSite := by
      intro left right equal
      apply Subtype.ext
      apply mapMolecularFullereneCarrierAtom_injective_on_carrier input symmetry
        (firstSites left.2) (firstSites right.2)
      exact congrArg Subtype.val equal
    have mapSiteSurjective : Function.Surjective mapSite := by
      intro target
      have mappedMember : target.1 ∈ mappedMolecularFullereneAttachmentSites input symmetry first := by
        rw [mappedExact]
        exact target.2
      obtain ⟨source, sourcePresent, mapped⟩ := Finset.mem_image.mp mappedMember
      refine ⟨⟨source, sourcePresent⟩, ?_⟩
      apply Subtype.ext
      exact mapped
    refine ⟨Equiv.ofBijective mapSite ⟨mapSiteInjective, mapSiteSurjective⟩, ?_⟩
    intro site
    rfl

/-- For two whole addends, all-`T` preservation has only the fixed and swapped cases. -/
theorem molecularFullereneSameTestAddendPatternPreserved_two_iff
    {molecule : RawMolecule} {input : MolecularFullereneConfigurationInput}
    (evidence : MolecularFullereneAddendRelationalEvidence molecule input.carrier)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input))
    (first second : MolecularFullereneAddend)
    (addendsExact : evidence.addends = [first, second]) :
    MolecularFullereneSameTestAddendPatternPreserved evidence symmetry ↔
      (MolecularFullereneUnlabeledSameTestPortEquivalence input symmetry first first ∧
          MolecularFullereneUnlabeledSameTestPortEquivalence input symmetry second second) ∨
        (MolecularFullereneUnlabeledSameTestPortEquivalence input symmetry first second ∧
          MolecularFullereneUnlabeledSameTestPortEquivalence input symmetry second first) := by
  simpa [MolecularFullereneSameTestAddendPatternPreserved] using
    exists_ownedAddendEquiv_forall_iff_two evidence first second addendsExact
      (MolecularFullereneUnlabeledSameTestPortEquivalence input symmetry)

/-- Fully computational normal form: fix or swap the two finite attachment-site sets. -/
theorem molecularFullereneSameTestAddendPatternPreserved_two_iff_mappedSites
    {molecule : RawMolecule} {input : MolecularFullereneConfigurationInput}
    (evidence : MolecularFullereneAddendRelationalEvidence molecule input.carrier)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input))
    (first second : MolecularFullereneAddend)
    (addendsExact : evidence.addends = [first, second]) :
    MolecularFullereneSameTestAddendPatternPreserved evidence symmetry ↔
      (mappedMolecularFullereneAttachmentSites input symmetry first = first.attachmentSites ∧
          mappedMolecularFullereneAttachmentSites input symmetry second = second.attachmentSites) ∨
        (mappedMolecularFullereneAttachmentSites input symmetry first = second.attachmentSites ∧
          mappedMolecularFullereneAttachmentSites input symmetry second = first.attachmentSites) := by
  have firstPresent : first ∈ evidence.addends := by simp [addendsExact]
  have secondPresent : second ∈ evidence.addends := by simp [addendsExact]
  have firstSites := MolecularFullereneAddend.validFor_attachmentSites_subset
    (evidence.addendsValid first firstPresent)
  have secondSites := MolecularFullereneAddend.validFor_attachmentSites_subset
    (evidence.addendsValid second secondPresent)
  rw [molecularFullereneSameTestAddendPatternPreserved_two_iff
    evidence symmetry first second addendsExact]
  rw [molecularFullereneUnlabeledSameTestPortEquivalence_iff_mappedSites
      input symmetry first first firstSites,
    molecularFullereneUnlabeledSameTestPortEquivalence_iff_mappedSites
      input symmetry second second secondSites,
    molecularFullereneUnlabeledSameTestPortEquivalence_iff_mappedSites
      input symmetry first second firstSites,
    molecularFullereneUnlabeledSameTestPortEquivalence_iff_mappedSites
      input symmetry second first secondSites]

/-- Actual constitutional preservation likewise has only the fixed and swapped cases. -/
theorem molecularFullereneActualAddendPatternPreserved_two_iff
    {molecule : RawMolecule} {input : MolecularFullereneConfigurationInput}
    (evidence : MolecularFullereneAddendRelationalEvidence molecule input.carrier)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input))
    (first second : MolecularFullereneAddend)
    (addendsExact : evidence.addends = [first, second]) :
    MolecularFullereneActualAddendPatternPreserved molecule input evidence symmetry ↔
      (first.ConstitutionallyIsomorphicAlong molecule input symmetry first ∧
          second.ConstitutionallyIsomorphicAlong molecule input symmetry second) ∨
        (first.ConstitutionallyIsomorphicAlong molecule input symmetry second ∧
          second.ConstitutionallyIsomorphicAlong molecule input symmetry first) := by
  simpa [MolecularFullereneActualAddendPatternPreserved] using
    exists_ownedAddendEquiv_forall_iff_two evidence first second addendsExact
      (MolecularFullereneAddend.ConstitutionallyIsomorphicAlong molecule input symmetry)

end


end TetraStereo.OneCenter.BlueBookP93.Cyclic

assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.exists_ownedAddendEquiv_forall_iff_two
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.molecularFullereneUnlabeledSameTestPortEquivalence_iff_mappedSites
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.MolecularFullereneAddend.ConstitutionallyIsomorphicAlong.mappedAttachmentSites_eq
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.molecularFullereneSameTestAddendPatternPreserved_two_iff_mappedSites
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.molecularFullereneActualAddendPatternPreserved_two_iff
