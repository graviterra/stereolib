import TetraStereo.OneCenter.SmilesTetrahedral

set_option autoImplicit false

namespace TetraStereo.OneCenter.AuthoritativeCIPRule6Scheduler

open RawMolecule

/-- Written length four prevents `ligandsWithLonePair` from adding a phantom position. -/
theorem ligandsWithLonePair_length_eq_four_of_written
    (mol : RawMolecule) (center : Nat)
    (writtenFour : (mol.writtenNeighbors center).length = 4) :
    (mol.ligandsWithLonePair center).length = 4 := by
  unfold ligandsWithLonePair
  cases atomEq : mol.atomAt? center with
  | none => simp [writtenFour]
  | some spec => simp [writtenFour]

/-- At a four-coordinate center, the source ligand positions are exactly the written physical
neighbors; the three-coordinate lone-pair convention cannot add a phantom position. -/
theorem ligandsWithLonePair_eq_writtenNeighbors_of_length_four
    (mol : RawMolecule) (center : Nat)
    (writtenFour : (mol.writtenNeighbors center).length = 4) :
    mol.ligandsWithLonePair center = mol.writtenNeighbors center := by
  unfold ligandsWithLonePair
  cases atomEq : mol.atomAt? center with
  | none => simp
  | some spec => simp [writtenFour]

end TetraStereo.OneCenter.AuthoritativeCIPRule6Scheduler
