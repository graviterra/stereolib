import TetraStereo.OneCenter.ProductionCIPRule1aCertifiedGlobal

set_option autoImplicit false

namespace TetraStereo
namespace Examples

open OneCenter
open OneCenter.DeclarativeCIP

/-- A sixteen-member alternating ring exercises general matching beyond the retired fourteen-edge
threshold.  Atom 16 is an external center so the same constitution also exercises complete
hierarchy compilation. -/
def rule1aLargeSimpleCycle : RawMolecule where
  atoms := List.replicate 17 (AtomSpec.aliphatic Element.C)
  bonds :=
    [⟨0, 1, .double⟩, ⟨1, 2, .single⟩, ⟨2, 3, .double⟩, ⟨3, 4, .single⟩,
      ⟨4, 5, .double⟩, ⟨5, 6, .single⟩, ⟨6, 7, .double⟩, ⟨7, 8, .single⟩,
      ⟨8, 9, .double⟩, ⟨9, 10, .single⟩, ⟨10, 11, .double⟩, ⟨11, 12, .single⟩,
      ⟨12, 13, .double⟩, ⟨13, 14, .single⟩, ⟨14, 15, .double⟩,
      ⟨15, 0, .single⟩, ⟨16, 0, .single⟩]

def rule1aLargeAttached : Fin rule1aLargeSimpleCycle.atomCount := ⟨0, by decide⟩
def rule1aLargeDuplicated : Fin rule1aLargeSimpleCycle.atomCount := ⟨1, by decide⟩

theorem rule1aLargeSimpleCycle_wellFormed : rule1aLargeSimpleCycle.WellFormed := by
  simp [RawMolecule.WellFormed, RawMolecule.BondEndpointsOK,
    RawMolecule.atomCount, rule1aLargeSimpleCycle]

theorem rule1aLargeSimpleCycle_bondRecordsUnique :
    rule1aLargeSimpleCycle.BondRecordsUnique := by
  simp [RawMolecule.BondRecordsUnique, RawBond.edgeKey, rule1aLargeSimpleCycle]

theorem rule1aLargeSimpleCycle_localized_edge_count :
    rule1aLargeSimpleCycle.localizedMancudeEdges.length = 16 := by decide

theorem rule1aLargeSimpleCycle_detected :
    (rule1aLargeSimpleCycle.simpleMancudeCycle? 0 1).isSome := by decide

/-- The general matcher computes the exact value directly for the sixteen-edge component. -/
theorem rule1aLargeSimpleCycle_general_label :
    rule1aLargeSimpleCycle.generalMancudeRule1aLabel? 0 1 = some ⟨12, 2⟩ := by decide

/-- The public labeler retains the same exact closed-cycle value. -/
theorem rule1aLargeSimpleCycle_label :
    rule1aLargeSimpleCycle.mancudeRule1aLabel? 0 1 = some ⟨12, 2⟩ := by decide

theorem rule1aLargeSimpleCycle_label_exact :
    ((⟨12, 2⟩ : RawMolecule.CIPAtomicLabel).toExactAtomicNumber.value) =
      (rule1aLargeSimpleCycle.toMoleculeGraph.exactRule1aMultipleBond
        rule1aLargeAttached rule1aLargeDuplicated).value := by
  exact rule1aLargeSimpleCycle.certifiedMancudeRule1aSound
    rule1aLargeSimpleCycle_wellFormed rule1aLargeSimpleCycle_bondRecordsUnique
    rule1aLargeAttached rule1aLargeDuplicated ⟨12, 2⟩ rule1aLargeSimpleCycle_label

set_option maxRecDepth 100000 in
/-- The same centered ring produces a complete branch hierarchy. -/
theorem rule1aLargeSimpleCycle_hierarchy_complete :
    (branchCanonicalKey? rule1aLargeSimpleCycle 16 0).map
      RawMolecule.CanonicalBranchKey.complete = some true := by decide

end Examples
end TetraStereo
