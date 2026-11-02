import TetraStereo.OneCenter.ProductionCIPTwoViewSemantics

set_option autoImplicit false

namespace TetraStereo
namespace Examples

open OneCenter
open OneCenter.DeclarativeCIP

/-- A deliberately small constitution on which the written resonance graph and the root-normalized
hierarchy graph induce different Rule-1a observations.  This is a regression for the paired-view
specification, not an assertion that either view may silently replace the other. -/
def rule1aOxidoCycle : RawMolecule where
  atoms :=
    [AtomSpec.aliphatic Element.P, AtomSpec.aliphatic Element.O,
      AtomSpec.aliphatic Element.C, AtomSpec.aliphatic Element.C]
  bonds :=
    [⟨0, 1, ParsedBondKind.double⟩, ⟨1, 2, ParsedBondKind.single⟩,
      ⟨2, 3, ParsedBondKind.double⟩, ⟨3, 0, ParsedBondKind.single⟩]

def rule1aOxidoCenter : Fin rule1aOxidoCycle.atomCount := ⟨0, by decide⟩
def rule1aOxidoLigand : Fin rule1aOxidoCycle.atomCount := ⟨1, by decide⟩
def rule1aOxidoAttached : Fin rule1aOxidoCycle.atomCount := ⟨2, by decide⟩
def rule1aOxidoDuplicated : Fin rule1aOxidoCycle.atomCount := ⟨3, by decide⟩

theorem rule1aOxidoCycle_wellFormed : rule1aOxidoCycle.WellFormed := by
  simp [RawMolecule.WellFormed, RawMolecule.BondEndpointsOK,
    RawMolecule.atomCount, rule1aOxidoCycle]

theorem rule1aOxidoCycle_bondRecordsUnique : rule1aOxidoCycle.BondRecordsUnique := by
  simp [RawMolecule.BondRecordsUnique, RawBond.edgeKey, rule1aOxidoCycle]

theorem rule1aOxidoCycle_written_label :
    rule1aOxidoCycle.mancudeRule1aLabel? 2 3 = some ⟨14, 2⟩ := by
  decide

theorem rule1aOxidoCycle_coordination_treatment :
    (rule1aOxidoCycle.constitutionalViews
      rule1aOxidoCenter rule1aOxidoLigand).treatment =
        RootBondTreatment.coordinationSingle := by
  decide

theorem rule1aOxidoCycle_view_root_orders :
    (rule1aOxidoCycle.constitutionalViews
        rule1aOxidoCenter rule1aOxidoLigand).resonance.bond
          rule1aOxidoCenter rule1aOxidoLigand = 2 ∧
      (rule1aOxidoCycle.constitutionalViews
        rule1aOxidoCenter rule1aOxidoLigand).expansion.bond
          rule1aOxidoCenter rule1aOxidoLigand = 1 := by
  decide

private theorem rule1aOxidoCycle_expansion_not_localized :
    ¬ (rule1aOxidoCycle.constitutionalViews
        rule1aOxidoCenter rule1aOxidoLigand).expansion.LocalizedMancudeEdge
          rule1aOxidoAttached rule1aOxidoDuplicated := by
  intro h
  rcases h with ⟨_, hpath⟩
  rcases Relation.ReflTransGen.cases_head hpath with heq | ⟨next, hstep, _⟩
  · exact (by decide : rule1aOxidoAttached ≠ rule1aOxidoDuplicated) heq
  · have hnoStep : ∀ next : Fin rule1aOxidoCycle.atomCount,
        ¬ (rule1aOxidoCycle.constitutionalViews
          rule1aOxidoCenter rule1aOxidoLigand).expansion.MancudeStepWithout
            rule1aOxidoAttached rule1aOxidoDuplicated rule1aOxidoAttached next := by
      intro atom
      fin_cases atom
      · intro candidate
        have hbond : (rule1aOxidoCycle.constitutionalViews
            rule1aOxidoCenter rule1aOxidoLigand).expansion.bond
              rule1aOxidoAttached ⟨0, by decide⟩ = 0 := by decide
        rcases candidate.1.1 with hsingle | hdouble
        · rw [hbond] at hsingle
          norm_num at hsingle
        · rw [hbond] at hdouble
          norm_num at hdouble
      · intro candidate
        have hcount : MoleculeGraph.incidentDoubleBondCount
            (rule1aOxidoCycle.constitutionalViews
              rule1aOxidoCenter rule1aOxidoLigand).expansion rule1aOxidoLigand = 0 := by
          decide
        rcases candidate.1.2.2 with hmatched | ⟨_, hcharge⟩
        · change MoleculeGraph.incidentDoubleBondCount
              (rule1aOxidoCycle.constitutionalViews
                rule1aOxidoCenter rule1aOxidoLigand).expansion rule1aOxidoLigand = 1
              at hmatched
          rw [hcount] at hmatched
          omega
        · norm_num [RawMolecule.constitutionalViews,
            RawMolecule.canonicalHierarchyMoleculeGraph, rule1aOxidoCycle,
            rule1aOxidoLigand, AtomSpec.aliphatic] at hcharge
      · intro candidate
        rcases candidate.1.1 with hsingle | hdouble
        · change (rule1aOxidoCycle.constitutionalViews
              rule1aOxidoCenter rule1aOxidoLigand).expansion.bond
                rule1aOxidoAttached rule1aOxidoAttached = 1 at hsingle
          rw [(rule1aOxidoCycle.constitutionalViews
            rule1aOxidoCenter rule1aOxidoLigand).expansion.bond_self] at hsingle
          norm_num at hsingle
        · change (rule1aOxidoCycle.constitutionalViews
              rule1aOxidoCenter rule1aOxidoLigand).expansion.bond
                rule1aOxidoAttached rule1aOxidoAttached = 2 at hdouble
          rw [(rule1aOxidoCycle.constitutionalViews
            rule1aOxidoCenter rule1aOxidoLigand).expansion.bond_self] at hdouble
          norm_num at hdouble
      · intro candidate
        exact candidate.2 (Or.inl ⟨rfl, rfl⟩)
    exact hnoStep next hstep

theorem rule1aOxidoCycle_expansion_value :
    ((rule1aOxidoCycle.constitutionalViews
        rule1aOxidoCenter rule1aOxidoLigand).expansion.exactRule1aMultipleBond
          rule1aOxidoAttached rule1aOxidoDuplicated).value = 6 := by
  rw [(rule1aOxidoCycle.constitutionalViews
    rule1aOxidoCenter rule1aOxidoLigand).expansion.exactRule1aMultipleBond_of_not_localized
      rule1aOxidoCycle_expansion_not_localized]
  norm_num [ExactAtomicNumber.ofNat, ExactAtomicNumber.value,
    RawMolecule.constitutionalViews, RawMolecule.canonicalHierarchyMoleculeGraph,
    rule1aOxidoCycle, rule1aOxidoDuplicated, AtomSpec.aliphatic, Element.atomicNumber]

/-- The two constitutional views are observably distinct; collapsing the paired specification to
one `MoleculeGraph` would make this true production case impossible to state correctly. -/
theorem rule1aOxidoCycle_views_not_rule1a_interchangeable :
    ((⟨14, 2⟩ : RawMolecule.CIPAtomicLabel).toExactAtomicNumber).value ≠
      ((rule1aOxidoCycle.constitutionalViews
        rule1aOxidoCenter rule1aOxidoLigand).expansion.exactRule1aMultipleBond
          rule1aOxidoAttached rule1aOxidoDuplicated).value := by
  rw [rule1aOxidoCycle_expansion_value]
  norm_num [RawMolecule.CIPAtomicLabel.toExactAtomicNumber,
    RawMolecule.CIPAtomicLabel.effectiveDenominator, ExactAtomicNumber.value]

end Examples
end TetraStereo
