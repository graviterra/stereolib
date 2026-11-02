import TetraStereo.OneCenter.ProductionCIPRule1aAssembly

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

namespace RawMolecule

/-!
Regression for a formerly unsound simple-cycle shortcut.

Two odd mancude cycles may share only one articulation atom.  Deleting that atom disconnects the
cycles, so the old different-cycle-atom reentry check missed the second ring and incorrectly used
the first triangle's closed formula.  The outside-neighbor pair check must reject this shape and
send it to the exact component matching search.
-/

private def articulationAtom (element : Element) (charge : Int := 0) : AtomSpec :=
  { element, charge }

private def articulationBond (source target : ℕ) (kind : ParsedBondKind) : RawBond :=
  { source, target, kind }

private def articulationFigureEight : RawMolecule :=
  { atoms :=
      [articulationAtom .C, articulationAtom .C, articulationAtom .P,
        articulationAtom .C, articulationAtom .N (-1)]
    bonds :=
      [articulationBond 0 1 .double, articulationBond 1 2 .single,
        articulationBond 2 0 .single, articulationBond 2 3 .double,
        articulationBond 3 4 .single, articulationBond 4 2 .single] }

theorem articulationFigureEight_wellFormed : articulationFigureEight.WellFormed := by
  simp [WellFormed, BondEndpointsOK, atomCount, articulationFigureEight,
    articulationAtom, articulationBond]

theorem articulationFigureEight_bondRecordsUnique :
    articulationFigureEight.BondRecordsUnique := by
  simp [BondRecordsUnique, RawBond.edgeKey, articulationFigureEight,
    articulationAtom, articulationBond]

/-- The simple-cycle shortcut rejects the articulation figure-eight. -/
theorem articulationFigureEight_simpleMancudeCycle_eq_none :
    articulationFigureEight.simpleMancudeCycle? 0 1 = none := by
  decide

/-- The repaired dispatch reaches the exact five-maximum-matching average, rather than the old
triangle shortcut value `21/3`. -/
theorem articulationFigureEight_mancudeRule1aLabel :
    articulationFigureEight.mancudeRule1aLabel? 0 1 = some ⟨33, 5⟩ := by
  decide

theorem articulationFigureEight_generalMancudeRule1aLabel :
    articulationFigureEight.generalMancudeRule1aLabel? 0 1 = some ⟨33, 5⟩ := by
  decide

private def chordedFiveCycle : RawMolecule :=
  { atoms :=
      [articulationAtom .C, articulationAtom .C, articulationAtom .C,
        articulationAtom .C, articulationAtom .N (-1)]
    bonds :=
      [articulationBond 0 1 .double, articulationBond 1 2 .single,
        articulationBond 2 3 .double, articulationBond 3 4 .single,
        articulationBond 4 0 .single, articulationBond 1 3 .single] }

theorem chordedFiveCycle_wellFormed : chordedFiveCycle.WellFormed := by
  simp [WellFormed, BondEndpointsOK, atomCount, chordedFiveCycle,
    articulationAtom, articulationBond]

theorem chordedFiveCycle_bondRecordsUnique : chordedFiveCycle.BondRecordsUnique := by
  simp [BondRecordsUnique, RawBond.edgeKey, chordedFiveCycle,
    articulationAtom, articulationBond]

/-- An internal chord also invalidates the closed simple-cycle formula. -/
theorem chordedFiveCycle_simpleMancudeCycle_eq_none :
    chordedFiveCycle.simpleMancudeCycle? 0 1 = none := by
  decide

/-- The extra maximum matching contributed by the chord changes `26/5` to `33/6`; the repaired
dispatch reaches the latter exact value. -/
theorem chordedFiveCycle_mancudeRule1aLabel :
    chordedFiveCycle.mancudeRule1aLabel? 0 1 = some ⟨33, 6⟩ := by
  decide

theorem chordedFiveCycle_generalMancudeRule1aLabel :
    chordedFiveCycle.generalMancudeRule1aLabel? 0 1 = some ⟨33, 6⟩ := by
  decide

end RawMolecule

end OneCenter
end TetraStereo
