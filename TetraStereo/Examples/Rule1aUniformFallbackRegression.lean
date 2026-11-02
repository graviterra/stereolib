import TetraStereo.OneCenter.ProductionCIPRule1aUniformFallbackSoundness

set_option autoImplicit false

namespace TetraStereo
namespace Examples

open OneCenter
open OneCenter.DeclarativeCIP

/-- A chorded sixteen-member alternating cycle exercises exhaustive matching beyond the retired
fourteen-edge threshold while its written double bonds exhibit a uniform perfect component.  The
chord makes the component genuinely non-simple.  Atom 16 is an external parent used to exercise
the actual public first-sphere path at atom 0. -/
def rule1aUniformLargeCycle : RawMolecule where
  atoms := List.replicate 17 (AtomSpec.aliphatic Element.C)
  bonds :=
    [⟨0, 1, ParsedBondKind.double⟩, ⟨1, 2, ParsedBondKind.single⟩,
      ⟨2, 3, ParsedBondKind.double⟩, ⟨3, 4, ParsedBondKind.single⟩,
      ⟨4, 5, ParsedBondKind.double⟩, ⟨5, 6, ParsedBondKind.single⟩,
      ⟨6, 7, ParsedBondKind.double⟩, ⟨7, 8, ParsedBondKind.single⟩,
      ⟨8, 9, ParsedBondKind.double⟩, ⟨9, 10, ParsedBondKind.single⟩,
      ⟨10, 11, ParsedBondKind.double⟩, ⟨11, 12, ParsedBondKind.single⟩,
      ⟨12, 13, ParsedBondKind.double⟩, ⟨13, 14, ParsedBondKind.single⟩,
      ⟨14, 15, ParsedBondKind.double⟩, ⟨15, 0, ParsedBondKind.single⟩,
      ⟨4, 12, ParsedBondKind.single⟩,
      ⟨16, 0, ParsedBondKind.single⟩]

def rule1aUniformAttached : Fin rule1aUniformLargeCycle.atomCount := ⟨0, by decide⟩
def rule1aUniformDuplicated : Fin rule1aUniformLargeCycle.atomCount := ⟨1, by decide⟩

def rule1aUniformDuplicateNode : RawMolecule.CanonicalBranchNode :=
  { atom := 1, parent := 0, history := [1, 0, 16],
    provenance := .multipleBondDuplicate 2 }

theorem rule1aUniformLargeCycle_wellFormed : rule1aUniformLargeCycle.WellFormed := by
  simp [RawMolecule.WellFormed, RawMolecule.BondEndpointsOK,
    RawMolecule.atomCount, rule1aUniformLargeCycle]

theorem rule1aUniformLargeCycle_bondRecordsUnique :
    rule1aUniformLargeCycle.BondRecordsUnique := by
  simp [RawMolecule.BondRecordsUnique, RawBond.edgeKey, rule1aUniformLargeCycle]

theorem rule1aUniformLargeCycle_localized_edge_count :
    rule1aUniformLargeCycle.localizedMancudeEdges.length = 17 := by
  decide

theorem rule1aUniformLargeCycle_not_simple :
    rule1aUniformLargeCycle.simpleMancudeCycle? 0 1 = none := by
  decide

theorem rule1aUniformLargeCycle_general_label :
    rule1aUniformLargeCycle.generalMancudeRule1aLabel? 0 1 = some ⟨12, 2⟩ := by
  decide

theorem rule1aUniformLargeCycle_ordinary_label :
    rule1aUniformLargeCycle.mancudeRule1aLabel? 0 1 = some ⟨12, 2⟩ := by
  decide

theorem rule1aUniformLargeCycle_fallback_label :
    rule1aUniformLargeCycle.uniformPerfectMancudeRule1aLabel? 0 1 =
      some ⟨6, 1⟩ := by
  decide

theorem rule1aUniformLargeCycle_firstSphere_label :
    rule1aUniformLargeCycle.canonicalFirstSphereRule1aLabel?
      rule1aUniformDuplicateNode = some ⟨6, 1⟩ := by
  decide

theorem rule1aUniformLargeCycle_localized :
    RawMolecule.containsUndirectedEdge rule1aUniformLargeCycle.localizedMancudeEdges
      0 1 = true := by
  decide

theorem rule1aUniformLargeCycle_fallback_exact :
    ((⟨6, 1⟩ : RawMolecule.CIPAtomicLabel).toExactAtomicNumber).value =
      (rule1aUniformLargeCycle.toMoleculeGraph.exactRule1aMultipleBond
        rule1aUniformAttached rule1aUniformDuplicated).value := by
  exact rule1aUniformLargeCycle.uniformPerfectMancudeRule1aLabel?_sound_of_raw_localized
    rule1aUniformLargeCycle_wellFormed rule1aUniformLargeCycle_bondRecordsUnique
    rule1aUniformAttached rule1aUniformDuplicated rule1aUniformLargeCycle_localized
    ⟨6, 1⟩ rule1aUniformLargeCycle_fallback_label

theorem rule1aUniformLargeCycle_firstSphere_exact :
    ((⟨6, 1⟩ : RawMolecule.CIPAtomicLabel).toExactAtomicNumber).value =
      (rule1aUniformLargeCycle.toMoleculeGraph.exactRule1aMultipleBond
        rule1aUniformAttached rule1aUniformDuplicated).value := by
  exact rule1aUniformLargeCycle.canonicalFirstSphereRule1aLabel?_multiple_sound
    rule1aUniformLargeCycle_wellFormed rule1aUniformLargeCycle_bondRecordsUnique
    rule1aUniformDuplicateNode 2 rfl rule1aUniformAttached rule1aUniformDuplicated
    rfl rfl ⟨6, 1⟩ rule1aUniformLargeCycle_firstSphere_label

/-- The public first-sphere builder reaches the certified uniform shortcut through a real root. -/
theorem rule1aUniformLargeCycle_public_firstSphere :
    rule1aUniformLargeCycle.firstCanonicalRule1aSphere?
      (RawMolecule.canonicalRoot 16 0) = some [⟨6, 1⟩, ⟨6, 1⟩, ⟨6, 1⟩] := by
  decide

end Examples
end TetraStereo
