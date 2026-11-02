import TetraStereo.OneCenter.ProductionCIPRule1aAssembly
import TetraStereo.OneCenter.ProductionCIPRule1aSimpleCycle

set_option autoImplicit false

namespace TetraStereo
namespace Examples

open OneCenter

def singlePartnerAdversary : RawMolecule where
  atoms :=
    [ AtomSpec.aliphatic Element.C, AtomSpec.aliphatic Element.C,
      AtomSpec.aliphatic Element.C, AtomSpec.aliphatic Element.C,
      AtomSpec.aliphatic Element.C, AtomSpec.aliphatic Element.C,
      { element := Element.C, charge := -1 } ]
  bonds :=
    [ ⟨0, 1, ParsedBondKind.double⟩,
      ⟨2, 4, ParsedBondKind.double⟩,
      ⟨3, 5, ParsedBondKind.double⟩,
      ⟨1, 2, ParsedBondKind.single⟩,
      ⟨2, 3, ParsedBondKind.single⟩,
      ⟨3, 0, ParsedBondKind.single⟩,
      ⟨4, 6, ParsedBondKind.single⟩,
      ⟨6, 5, ParsedBondKind.single⟩ ]

def adversaryAttached : Fin singlePartnerAdversary.atomCount := ⟨0, by decide⟩

def adversaryDuplicated : Fin singlePartnerAdversary.atomCount := ⟨1, by decide⟩

theorem singlePartnerAdversary_wellFormed : singlePartnerAdversary.WellFormed := by
  simp [RawMolecule.WellFormed, RawMolecule.BondEndpointsOK, RawMolecule.atomCount,
    singlePartnerAdversary]

theorem singlePartnerAdversary_bondRecordsUnique :
    singlePartnerAdversary.BondRecordsUnique := by
  simp [RawMolecule.BondRecordsUnique, RawBond.edgeKey,
    singlePartnerAdversary]

theorem singlePartnerAdversary_localizedEdges :
    singlePartnerAdversary.localizedMancudeEdges =
      [(0, 1), (2, 4), (3, 5), (1, 2), (2, 3), (3, 0), (4, 6), (6, 5)] := by
  decide

theorem singlePartnerAdversary_localized :
    RawMolecule.containsUndirectedEdge singlePartnerAdversary.localizedMancudeEdges 0 1 = true := by
  decide

theorem singlePartnerAdversary_not_simple :
    singlePartnerAdversary.simpleMancudeCycle? 0 1 = none := by
  decide

theorem singlePartnerAdversary_single_partner :
    singlePartnerAdversary.mancudeDuplicatePartners 0 1 = [1] := by
  decide

theorem singlePartnerAdversary_production_label :
    singlePartnerAdversary.mancudeRule1aLabel? 0 1 =
      some ⟨48, 9⟩ := by
  decide

theorem singlePartnerAdversary_general_label :
    singlePartnerAdversary.generalMancudeRule1aLabel? 0 1 =
      some ⟨48, 9⟩ := by
  have hlabel := singlePartnerAdversary_production_label
  unfold RawMolecule.mancudeRule1aLabel? at hlabel
  simpa [singlePartnerAdversary_localized, singlePartnerAdversary_not_simple] using hlabel

theorem singlePartnerAdversary_componentEdges :
    singlePartnerAdversary.localizedMancudeComponentEdges 0 =
      [(0, 1), (2, 4), (3, 5), (1, 2), (2, 3), (3, 0), (4, 6), (6, 5)] := by
  decide

theorem singlePartnerAdversary_production_stats :
    singlePartnerAdversary.exhaustiveMancudeMatchingStats 0
      (singlePartnerAdversary.localizedMancudeComponentEdges 0) =
      { size := 3, count := 9, partnerZSum := 48 } := by
  rw [singlePartnerAdversary_componentEdges]
  norm_num [RawMolecule.exhaustiveMancudeMatchingStats,
    RawMolecule.combineMancudeStats, RawMolecule.atomZAt, RawMolecule.atomAt?, listGet?,
    singlePartnerAdversary, AtomSpec.aliphatic, Element.atomicNumber]

private theorem singlePartnerAdversary_realization :
    RawMolecule.LocalizedMancudeEdgeListRealization singlePartnerAdversary adversaryAttached
      (singlePartnerAdversary.localizedMancudeComponentEdges 0) := by
  exact singlePartnerAdversary.localizedMancudeComponentEdges_realization
    singlePartnerAdversary_wellFormed singlePartnerAdversary_bondRecordsUnique adversaryAttached

theorem singlePartnerAdversary_independent_count :
    (singlePartnerAdversary.toMoleculeGraph.maximumMancudeMatchings adversaryAttached).card = 9 := by
  rw [← singlePartnerAdversary.exhaustiveMancudeMatchingStats_count_eq_independent_card
    adversaryAttached (singlePartnerAdversary.localizedMancudeComponentEdges 0)
    singlePartnerAdversary_realization]
  change (singlePartnerAdversary.exhaustiveMancudeMatchingStats 0
    (singlePartnerAdversary.localizedMancudeComponentEdges 0)).count = 9
  rw [singlePartnerAdversary_production_stats]

theorem singlePartnerAdversary_independent_partner_sum :
    (singlePartnerAdversary.toMoleculeGraph.maximumMancudeMatchings adversaryAttached).sum
      (singlePartnerAdversary.toMoleculeGraph.mancudePartnerAtomicNumber adversaryAttached) = 48 := by
  rw [← singlePartnerAdversary.exhaustiveMancudeMatchingStats_partnerZSum_eq_independent_sum
    adversaryAttached (singlePartnerAdversary.localizedMancudeComponentEdges 0)
    singlePartnerAdversary_realization]
  change (singlePartnerAdversary.exhaustiveMancudeMatchingStats 0
    (singlePartnerAdversary.localizedMancudeComponentEdges 0)).partnerZSum = 48
  rw [singlePartnerAdversary_production_stats]

theorem singlePartnerAdversary_independent_average_value :
    (singlePartnerAdversary.toMoleculeGraph.exactMancudeAverage adversaryAttached).value =
      (16 : ℚ) / 3 := by
  unfold MoleculeGraph.exactMancudeAverage DeclarativeCIP.ExactAtomicNumber.value
  change (↑((singlePartnerAdversary.toMoleculeGraph.maximumMancudeMatchings
      adversaryAttached).sum
        (singlePartnerAdversary.toMoleculeGraph.mancudePartnerAtomicNumber adversaryAttached)) : ℚ) /
    ↑(singlePartnerAdversary.toMoleculeGraph.maximumMancudeMatchings
      adversaryAttached).card = (16 : ℚ) / 3
  rw [singlePartnerAdversary_independent_partner_sum,
    singlePartnerAdversary_independent_count]
  norm_num

theorem singlePartnerAdversary_semantically_localized :
    singlePartnerAdversary.toMoleculeGraph.LocalizedMancudeEdge
      adversaryAttached adversaryDuplicated := by
  apply (singlePartnerAdversary.containsUndirectedEdge_localizedMancudeEdges_iff
    singlePartnerAdversary_wellFormed singlePartnerAdversary_bondRecordsUnique
    adversaryAttached adversaryDuplicated).mp
  exact singlePartnerAdversary_localized

/-- The removed integral shortcut would be unsound under precisely the repository's current
`WellFormed` and `BondRecordsUnique` hypotheses. -/
theorem singlePartnerAdversary_old_integral_label_ne_independent :
    ((⟨6, 1⟩ : RawMolecule.CIPAtomicLabel).toExactAtomicNumber).value ≠
      (singlePartnerAdversary.toMoleculeGraph.exactRule1aMultipleBond
        adversaryAttached adversaryDuplicated).value := by
  rw [singlePartnerAdversary.toMoleculeGraph.exactRule1aMultipleBond_of_localized
    singlePartnerAdversary_semantically_localized]
  rw [singlePartnerAdversary_independent_average_value]
  norm_num [RawMolecule.CIPAtomicLabel.toExactAtomicNumber,
    RawMolecule.CIPAtomicLabel.effectiveDenominator,
    DeclarativeCIP.ExactAtomicNumber.value]

/-- The repaired executable branch falls through to exhaustive matching and has the independent
exact rational value. -/
theorem singlePartnerAdversary_repaired_label_exact :
    ∃ label, singlePartnerAdversary.mancudeRule1aLabel? 0 1 = some label ∧
      label.toExactAtomicNumber.value =
        (singlePartnerAdversary.toMoleculeGraph.exactRule1aMultipleBond
          adversaryAttached adversaryDuplicated).value := by
  refine ⟨⟨48, 9⟩, singlePartnerAdversary_production_label, ?_⟩
  rw [singlePartnerAdversary.toMoleculeGraph.exactRule1aMultipleBond_of_localized
    singlePartnerAdversary_semantically_localized]
  rw [singlePartnerAdversary_independent_average_value]
  norm_num [RawMolecule.CIPAtomicLabel.toExactAtomicNumber,
    RawMolecule.CIPAtomicLabel.effectiveDenominator,
    DeclarativeCIP.ExactAtomicNumber.value]

theorem singlePartnerAdversary_not_uniform_profile :
    ¬ singlePartnerAdversary.toMoleculeGraph.UniformPartnerProfile
      adversaryAttached adversaryDuplicated := by
  intro hprofile
  have huniform :=
    singlePartnerAdversary.toMoleculeGraph.exactMancudeAverage_value_eq_uniformPartner
      adversaryAttached adversaryDuplicated hprofile
  rw [singlePartnerAdversary_independent_average_value] at huniform
  norm_num [DeclarativeCIP.ExactAtomicNumber.ofNat,
    DeclarativeCIP.ExactAtomicNumber.value, RawMolecule.toMoleculeGraph,
    adversaryDuplicated, singlePartnerAdversary, AtomSpec.aliphatic,
    Element.atomicNumber] at huniform

end Examples
end TetraStereo
