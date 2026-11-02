import TetraStereo.OneCenter.IUPACP93CanonicalFullereneAddendTemplates
import TetraStereo.OneCenter.IUPACP93CanonicalFullereneC60CagePackage
import TetraStereo.OneCenter.IUPACP93CanonicalFullereneC70CagePackage
import TetraStereo.OneCenter.IUPACP93CanonicalFullereneC76CagePackage
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Exact template assemblies for the five P-93 fullerene derivatives

The source placement ledger owns whole addends as finite attachment-site sets.  This module
canonically enumerates each set in increasing locant order, uses an exact cardinality proof to
identify that enumeration with the local template ports, and compiles the five ledgers against
the independently reviewed C60, C70, and C76 cage transcriptions.  External atom indices are
therefore generated only by the generic prefix compiler.
-/

namespace TetraStereo.OneCenter
namespace P93CanonicalProgramFullerene

open BlueBookP93.Cyclic

noncomputable section

/-- Canonical increasing enumeration of the printed attachment sites. -/
def iupacP93PrintedFullereneSortedAttachmentSites
    (placement : IUPACP93PrintedFullereneAddendPlacement) : List Nat :=
  placement.attachmentSites.sort (· ≤ ·)

/-- Port `i` is assigned the `i`th smallest printed cage locant.  The exact cardinality proof is
what rules out both omitted ports and fabricated attachment sites. -/
def iupacP93PrintedFullereneAttachmentSite
    (placement : IUPACP93PrintedFullereneAddendPlacement)
    (portCountExact : placement.attachmentSites.card = placement.kind.localTemplate.portCount)
    (port : Fin placement.kind.localTemplate.portCount) : Nat :=
  iupacP93PrintedFullereneSortedAttachmentSites placement |>.get
    ⟨port.val, by
      rw [iupacP93PrintedFullereneSortedAttachmentSites, Finset.length_sort,
        portCountExact]
      exact port.isLt⟩

theorem iupacP93PrintedFullereneAttachmentSite_mem
    (placement : IUPACP93PrintedFullereneAddendPlacement)
    (portCountExact : placement.attachmentSites.card = placement.kind.localTemplate.portCount)
    (port : Fin placement.kind.localTemplate.portCount) :
    iupacP93PrintedFullereneAttachmentSite placement portCountExact port ∈
      placement.attachmentSites := by
  apply (Finset.mem_sort (· ≤ ·)).mp
  exact List.get_mem _ _

theorem iupacP93PrintedFullereneAttachmentSite_injective
    (placement : IUPACP93PrintedFullereneAddendPlacement)
    (portCountExact : placement.attachmentSites.card = placement.kind.localTemplate.portCount) :
    Function.Injective
      (iupacP93PrintedFullereneAttachmentSite placement portCountExact) := by
  intro first second equalSite
  apply Fin.ext
  let firstIndex : Fin (iupacP93PrintedFullereneSortedAttachmentSites placement).length :=
    ⟨first.val, by
      rw [iupacP93PrintedFullereneSortedAttachmentSites, Finset.length_sort,
        portCountExact]
      exact first.isLt⟩
  let secondIndex : Fin (iupacP93PrintedFullereneSortedAttachmentSites placement).length :=
    ⟨second.val, by
      rw [iupacP93PrintedFullereneSortedAttachmentSites, Finset.length_sort,
        portCountExact]
      exact second.isLt⟩
  have indexEqual : firstIndex = secondIndex :=
    ((Finset.sort_nodup placement.attachmentSites (· ≤ ·)).get_inj_iff).mp equalSite
  exact congrArg
    (fun index : Fin (iupacP93PrintedFullereneSortedAttachmentSites placement).length =>
      index.val) indexEqual

/-- Typed placement produced from one audited source row.  Keeping the exact local template in the
result type lets the generic same-template isomorphism theorem be instantiated without recovering
template equality from an erased placed-addend record. -/
def compileIUPACP93PrintedFullerenePlacementOf
    {core : RawMolecule} {carrier : Finset Nat}
    (carrierExact : carrier = Finset.range core.atomCount)
    (placement : IUPACP93PrintedFullereneAddendPlacement)
    (valid : placement.ValidForAtomCount core.atomCount)
    (portCountExact : placement.attachmentSites.card = placement.kind.localTemplate.portCount) :
    MolecularFullereneAddendTemplateAssembly.MolecularFullerenePlacementOf
      carrier placement.kind.localTemplate where
  attachmentSite := iupacP93PrintedFullereneAttachmentSite placement portCountExact
  attachmentSite_mem := by
    intro port
    rw [carrierExact]
    exact valid.2 (iupacP93PrintedFullereneAttachmentSite_mem
      placement portCountExact port)
  attachmentSite_injective :=
    iupacP93PrintedFullereneAttachmentSite_injective placement portCountExact

/-- Compile one audited source placement without accepting any hand-written external atom index.
The cage carrier is fixed by the reviewed transcription's exact range equality. -/
def compileIUPACP93PrintedFullereneAddendPlacement
    {core : RawMolecule} {carrier : Finset Nat}
    (carrierExact : carrier = Finset.range core.atomCount)
    (placement : IUPACP93PrintedFullereneAddendPlacement)
    (valid : placement.ValidForAtomCount core.atomCount)
    (portCountExact : placement.attachmentSites.card = placement.kind.localTemplate.portCount) :
    MolecularFullerenePlacedAddendTemplate carrier :=
  (compileIUPACP93PrintedFullerenePlacementOf carrierExact placement valid
    portCountExact).toPlaced

/-- The generated placement has exactly, not merely a subset of, the printed source sites. -/
theorem compileIUPACP93PrintedFullereneAddendPlacement_attachmentSites
    {core : RawMolecule} {carrier : Finset Nat}
    (carrierExact : carrier = Finset.range core.atomCount)
    (placement : IUPACP93PrintedFullereneAddendPlacement)
    (valid : placement.ValidForAtomCount core.atomCount)
    (portCountExact : placement.attachmentSites.card = placement.kind.localTemplate.portCount) :
    MolecularFullerenePlacedAddendTemplate.attachmentSites
        (compileIUPACP93PrintedFullereneAddendPlacement carrierExact placement valid
          portCountExact) = placement.attachmentSites := by
  ext site
  constructor
  · intro present
    simp only [MolecularFullerenePlacedAddendTemplate.attachmentSites,
      Finset.mem_image, Finset.mem_univ, true_and] at present
    obtain ⟨port, rfl⟩ := present
    exact iupacP93PrintedFullereneAttachmentSite_mem placement portCountExact port
  · intro present
    have sortedPresent : site ∈ iupacP93PrintedFullereneSortedAttachmentSites placement :=
      (Finset.mem_sort (· ≤ ·)).mpr present
    obtain ⟨index, getEqual⟩ := List.get_of_mem sortedPresent
    have indexPortBound : index.val < placement.kind.localTemplate.portCount := by
      rw [← portCountExact, ← Finset.length_sort (s := placement.attachmentSites) (· ≤ ·)]
      exact index.isLt
    simp only [MolecularFullerenePlacedAddendTemplate.attachmentSites,
      Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨index.val, indexPortBound⟩, getEqual⟩

/-- Compile a complete source ledger by structural recursion. Each placement's membership proof
remains local to that placement, and no replacement ordering is introduced beyond the source list. -/
def compileIUPACP93PrintedFullereneAddendPlacements
    {core : RawMolecule} {carrier : Finset Nat}
    (carrierExact : carrier = Finset.range core.atomCount)
    (placements : List IUPACP93PrintedFullereneAddendPlacement)
    (placementsValid : ∀ placement ∈ placements,
      placement.ValidForAtomCount core.atomCount)
    (portCountsExact : ∀ placement ∈ placements,
      placement.attachmentSites.card = placement.kind.localTemplate.portCount) :
    List (MolecularFullerenePlacedAddendTemplate carrier) :=
  match placements with
  | [] => []
  | head :: tail =>
      compileIUPACP93PrintedFullereneAddendPlacement carrierExact head
          (placementsValid head (by simp)) (portCountsExact head (by simp)) ::
        compileIUPACP93PrintedFullereneAddendPlacements carrierExact tail
          (fun placement present => placementsValid placement (by simp [present]))
          (fun placement present => portCountsExact placement (by simp [present]))

theorem compileIUPACP93PrintedFullereneAddendPlacements_attachmentSites
    {core : RawMolecule} {carrier : Finset Nat}
    (carrierExact : carrier = Finset.range core.atomCount)
    (placements : List IUPACP93PrintedFullereneAddendPlacement)
    (placementsValid : ∀ placement ∈ placements,
      placement.ValidForAtomCount core.atomCount)
    (portCountsExact : ∀ placement ∈ placements,
      placement.attachmentSites.card = placement.kind.localTemplate.portCount) :
    (compileIUPACP93PrintedFullereneAddendPlacements carrierExact placements placementsValid
        portCountsExact).map MolecularFullerenePlacedAddendTemplate.attachmentSites =
      placements.map (·.attachmentSites) := by
  induction placements with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      let tailValid : ∀ placement ∈ tail,
          placement.ValidForAtomCount core.atomCount :=
        fun placement present => placementsValid placement (by simp [present])
      let tailCounts : ∀ placement ∈ tail,
          placement.attachmentSites.card = placement.kind.localTemplate.portCount :=
        fun placement present => portCountsExact placement (by simp [present])
      rw [compileIUPACP93PrintedFullereneAddendPlacements]
      simp only [List.map_cons]
      congr 1
      · exact compileIUPACP93PrintedFullereneAddendPlacement_attachmentSites
          carrierExact head (placementsValid head (by simp))
            (portCountsExact head (by simp))
      · simpa only [compileIUPACP93PrintedFullereneAddendPlacements] using
          inductionHypothesis tailValid tailCounts

/-- Compilation preserves the exact source kind-to-template map in source-list order. -/
theorem compileIUPACP93PrintedFullereneAddendPlacements_templates
    {core : RawMolecule} {carrier : Finset Nat}
    (carrierExact : carrier = Finset.range core.atomCount)
    (placements : List IUPACP93PrintedFullereneAddendPlacement)
    (placementsValid : ∀ placement ∈ placements,
      placement.ValidForAtomCount core.atomCount)
    (portCountsExact : ∀ placement ∈ placements,
      placement.attachmentSites.card = placement.kind.localTemplate.portCount) :
    (compileIUPACP93PrintedFullereneAddendPlacements carrierExact placements placementsValid
        portCountsExact).map (·.template) =
      placements.map (fun placement => placement.kind.localTemplate) := by
  induction placements with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [compileIUPACP93PrintedFullereneAddendPlacements, List.map_cons]
      congr 1
      simpa only [compileIUPACP93PrintedFullereneAddendPlacements] using
        inductionHypothesis
          (fun placement present => placementsValid placement (by simp [present]))
          (fun placement present => portCountsExact placement (by simp [present]))

theorem compileIUPACP93PrintedFullereneAddendPlacements_templatesValid
    {core : RawMolecule} {carrier : Finset Nat}
    (carrierExact : carrier = Finset.range core.atomCount)
    (placements : List IUPACP93PrintedFullereneAddendPlacement)
    (placementsValid : ∀ placement ∈ placements,
      placement.ValidForAtomCount core.atomCount)
    (portCountsExact : ∀ placement ∈ placements,
      placement.attachmentSites.card = placement.kind.localTemplate.portCount) :
    ∀ placed ∈ compileIUPACP93PrintedFullereneAddendPlacements carrierExact placements
        placementsValid portCountsExact,
      placed.template.Valid := by
  induction placements with
  | nil => simp [compileIUPACP93PrintedFullereneAddendPlacements]
  | cons head tail inductionHypothesis =>
      intro placed present
      simp only [compileIUPACP93PrintedFullereneAddendPlacements, List.mem_cons] at present
      rcases present with rfl | present
      · exact head.kind.localTemplate_valid
      · apply inductionHypothesis
        exact present

theorem compileIUPACP93PrintedFullereneAddendPlacements_pairwiseDisjoint
    {core : RawMolecule} {carrier : Finset Nat}
    (carrierExact : carrier = Finset.range core.atomCount)
    (placements : List IUPACP93PrintedFullereneAddendPlacement)
    (placementsValid : ∀ placement ∈ placements,
      placement.ValidForAtomCount core.atomCount)
    (portCountsExact : ∀ placement ∈ placements,
      placement.attachmentSites.card = placement.kind.localTemplate.portCount)
    (sourcePairwise : placements.Pairwise fun first second =>
      Disjoint first.attachmentSites second.attachmentSites) :
    (compileIUPACP93PrintedFullereneAddendPlacements carrierExact placements placementsValid
        portCountsExact).Pairwise fun first second =>
      Disjoint first.attachmentSites second.attachmentSites := by
  induction placements with
  | nil => simp [compileIUPACP93PrintedFullereneAddendPlacements]
  | cons head tail inductionHypothesis =>
      rw [List.pairwise_cons] at sourcePairwise
      simp only [compileIUPACP93PrintedFullereneAddendPlacements, List.pairwise_cons]
      constructor
      · intro compiled compiledPresent
        let tailValid : ∀ placement ∈ tail,
            placement.ValidForAtomCount core.atomCount :=
          fun placement present => placementsValid placement (by simp [present])
        let tailCounts : ∀ placement ∈ tail,
            placement.attachmentSites.card = placement.kind.localTemplate.portCount :=
          fun placement present => portCountsExact placement (by simp [present])
        have compiledPresent' : compiled ∈
            compileIUPACP93PrintedFullereneAddendPlacements carrierExact tail
              tailValid tailCounts := by
          simpa only [compileIUPACP93PrintedFullereneAddendPlacements] using compiledPresent
        have sourceSitesPresent : compiled.attachmentSites ∈ tail.map (·.attachmentSites) := by
          rw [← compileIUPACP93PrintedFullereneAddendPlacements_attachmentSites
            carrierExact tail tailValid tailCounts]
          exact List.mem_map.mpr ⟨compiled, compiledPresent', rfl⟩
        obtain ⟨sourcePlacement, sourcePresent, sourceSitesEqual⟩ :=
          List.mem_map.mp sourceSitesPresent
        rw [compileIUPACP93PrintedFullereneAddendPlacement_attachmentSites
          carrierExact head (placementsValid head (by simp))
            (portCountsExact head (by simp)), ← sourceSitesEqual]
        exact sourcePairwise.1 sourcePlacement sourcePresent
      · simpa only [compileIUPACP93PrintedFullereneAddendPlacements] using
          inductionHypothesis
            (fun placement present => placementsValid placement (by simp [present]))
            (fun placement present => portCountsExact placement (by simp [present]))
            sourcePairwise.2

/-- Turn one completely audited printed ledger into the generic assembly input consumed by the
prefix-indexed derivative compiler. -/
def compileIUPACP93PrintedFullereneAddendAssembly
    {core : RawMolecule} {carrier : Finset Nat}
    (carrierExact : carrier = Finset.range core.atomCount)
    (placements : List IUPACP93PrintedFullereneAddendPlacement)
    (audited : IUPACP93PrintedFullereneAddendPlacementsJudgment core.atomCount placements)
    (portCountsExact : ∀ placement ∈ placements,
      placement.attachmentSites.card = placement.kind.localTemplate.portCount) :
    MolecularFullereneAddendTemplateAssembly core carrier where
  placements := compileIUPACP93PrintedFullereneAddendPlacements carrierExact placements
    audited.2.2.1 portCountsExact
  carrier_eq_range := carrierExact
  templatesValid := compileIUPACP93PrintedFullereneAddendPlacements_templatesValid
    carrierExact placements audited.2.2.1 portCountsExact
  attachmentSitesPairwiseDisjoint :=
    compileIUPACP93PrintedFullereneAddendPlacements_pairwiseDisjoint carrierExact placements
      audited.2.2.1 portCountsExact audited.2.2.2

/-! ## The five audited assemblies -/

private theorem c76Type1PortCountsExact :
    ∀ placement ∈ iupacP93CanonicalFullereneC76Type1Placements,
      placement.attachmentSites.card = placement.kind.localTemplate.portCount := by
  intro placement present
  simp [iupacP93CanonicalFullereneC76Type1Placements] at present
  rcases present with rfl | rfl <;> decide

def iupacP93CanonicalFullereneC76Type1Assembly :
    MolecularFullereneAddendTemplateAssembly
      iupacP93CanonicalFullereneC76Transcription.cageMolecule
      iupacP93CanonicalFullereneC76Transcription.numberedPackage.carrier :=
  compileIUPACP93PrintedFullereneAddendAssembly rfl
    iupacP93CanonicalFullereneC76Type1Placements
    iupacP93CanonicalFullereneC76Type1Placements_audited c76Type1PortCountsExact

private theorem c60Type2PortCountsExact :
    ∀ placement ∈ iupacP93CanonicalFullereneC60Type2Placements,
      placement.attachmentSites.card = placement.kind.localTemplate.portCount := by
  intro placement present
  simp [iupacP93CanonicalFullereneC60Type2Placements] at present
  rcases present with rfl | rfl <;> decide

def iupacP93CanonicalFullereneC60Type2Assembly :
    MolecularFullereneAddendTemplateAssembly
      iupacP93CanonicalFullereneC60Transcription.cageMolecule
      iupacP93CanonicalFullereneC60Transcription.numberedPackage.carrier :=
  compileIUPACP93PrintedFullereneAddendAssembly rfl
    iupacP93CanonicalFullereneC60Type2Placements
    iupacP93CanonicalFullereneC60Type2Placements_audited c60Type2PortCountsExact

private theorem c60Type3PortCountsExact :
    ∀ placement ∈ iupacP93CanonicalFullereneC60Type3Placements,
      placement.attachmentSites.card = placement.kind.localTemplate.portCount := by
  intro placement present
  simp [iupacP93CanonicalFullereneC60Type3Placements] at present
  rcases present with rfl | rfl <;> decide

def iupacP93CanonicalFullereneC60Type3Assembly :
    MolecularFullereneAddendTemplateAssembly
      iupacP93CanonicalFullereneC60Transcription.cageMolecule
      iupacP93CanonicalFullereneC60Transcription.numberedPackage.carrier :=
  compileIUPACP93PrintedFullereneAddendAssembly rfl
    iupacP93CanonicalFullereneC60Type3Placements
    iupacP93CanonicalFullereneC60Type3Placements_audited c60Type3PortCountsExact

private theorem c70Type4PortCountsExact :
    ∀ placement ∈ iupacP93CanonicalFullereneC70Type4Placements,
      placement.attachmentSites.card = placement.kind.localTemplate.portCount := by
  intro placement present
  simp [iupacP93CanonicalFullereneC70Type4Placements] at present
  rcases present with rfl | rfl <;> decide

def iupacP93CanonicalFullereneC70Type4Assembly :
    MolecularFullereneAddendTemplateAssembly
      iupacP93CanonicalFullereneC70Transcription.cageMolecule
      iupacP93CanonicalFullereneC70Transcription.numberedPackage.carrier :=
  compileIUPACP93PrintedFullereneAddendAssembly rfl
    iupacP93CanonicalFullereneC70Type4Placements
    iupacP93CanonicalFullereneC70Type4Placements_audited c70Type4PortCountsExact

private theorem c70SuperimposedPortCountsExact :
    ∀ placement ∈ iupacP93CanonicalFullereneC70SuperimposedPlacements,
      placement.attachmentSites.card = placement.kind.localTemplate.portCount := by
  intro placement present
  simp [iupacP93CanonicalFullereneC70SuperimposedPlacements] at present
  rcases present with rfl | rfl <;> decide

def iupacP93CanonicalFullereneC70SuperimposedAssembly :
    MolecularFullereneAddendTemplateAssembly
      iupacP93CanonicalFullereneC70Transcription.cageMolecule
      iupacP93CanonicalFullereneC70Transcription.numberedPackage.carrier :=
  compileIUPACP93PrintedFullereneAddendAssembly rfl
    iupacP93CanonicalFullereneC70SuperimposedPlacements
    iupacP93CanonicalFullereneC70SuperimposedPlacements_audited
    c70SuperimposedPortCountsExact

/-- Exact whole-addend placement preservation for all five derivative assemblies. -/
theorem iupacP93CanonicalFullereneDerivativeAssemblies_attachmentSites :
    iupacP93CanonicalFullereneC76Type1Assembly.placements.map
        MolecularFullerenePlacedAddendTemplate.attachmentSites =
          iupacP93CanonicalFullereneC76Type1Placements.map (·.attachmentSites) ∧
      iupacP93CanonicalFullereneC60Type2Assembly.placements.map
        MolecularFullerenePlacedAddendTemplate.attachmentSites =
          iupacP93CanonicalFullereneC60Type2Placements.map (·.attachmentSites) ∧
      iupacP93CanonicalFullereneC60Type3Assembly.placements.map
        MolecularFullerenePlacedAddendTemplate.attachmentSites =
          iupacP93CanonicalFullereneC60Type3Placements.map (·.attachmentSites) ∧
      iupacP93CanonicalFullereneC70Type4Assembly.placements.map
        MolecularFullerenePlacedAddendTemplate.attachmentSites =
          iupacP93CanonicalFullereneC70Type4Placements.map (·.attachmentSites) ∧
      iupacP93CanonicalFullereneC70SuperimposedAssembly.placements.map
        MolecularFullerenePlacedAddendTemplate.attachmentSites =
          iupacP93CanonicalFullereneC70SuperimposedPlacements.map (·.attachmentSites) := by
  exact ⟨compileIUPACP93PrintedFullereneAddendPlacements_attachmentSites _ _ _ _,
    compileIUPACP93PrintedFullereneAddendPlacements_attachmentSites _ _ _ _,
    compileIUPACP93PrintedFullereneAddendPlacements_attachmentSites _ _ _ _,
    compileIUPACP93PrintedFullereneAddendPlacements_attachmentSites _ _ _ _,
    compileIUPACP93PrintedFullereneAddendPlacements_attachmentSites _ _ _ _⟩

/-- Exact source kind-to-template preservation for all five derivative assemblies. -/
theorem iupacP93CanonicalFullereneDerivativeAssemblies_templates :
    iupacP93CanonicalFullereneC76Type1Assembly.placements.map (·.template) =
        iupacP93CanonicalFullereneC76Type1Placements.map
          (fun placement => placement.kind.localTemplate) ∧
      iupacP93CanonicalFullereneC60Type2Assembly.placements.map (·.template) =
        iupacP93CanonicalFullereneC60Type2Placements.map
          (fun placement => placement.kind.localTemplate) ∧
      iupacP93CanonicalFullereneC60Type3Assembly.placements.map (·.template) =
        iupacP93CanonicalFullereneC60Type3Placements.map
          (fun placement => placement.kind.localTemplate) ∧
      iupacP93CanonicalFullereneC70Type4Assembly.placements.map (·.template) =
        iupacP93CanonicalFullereneC70Type4Placements.map
          (fun placement => placement.kind.localTemplate) ∧
      iupacP93CanonicalFullereneC70SuperimposedAssembly.placements.map (·.template) =
        iupacP93CanonicalFullereneC70SuperimposedPlacements.map
          (fun placement => placement.kind.localTemplate) := by
  exact ⟨compileIUPACP93PrintedFullereneAddendPlacements_templates _ _ _ _,
    compileIUPACP93PrintedFullereneAddendPlacements_templates _ _ _ _,
    compileIUPACP93PrintedFullereneAddendPlacements_templates _ _ _ _,
    compileIUPACP93PrintedFullereneAddendPlacements_templates _ _ _ _,
    compileIUPACP93PrintedFullereneAddendPlacements_templates _ _ _ _⟩

end
end P93CanonicalProgramFullerene
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneDerivativeAssemblies_attachmentSites
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneDerivativeAssemblies_templates
