import TetraStereo.OneCenter.ProductionCIPRule1aCycleSoundness

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

open DeclarativeCIP

namespace RawMolecule

/-- Complete soundness of the executable simple-cycle fast path under the ordinary raw-graph
hypotheses.  The result is structural: detector exactness, the path/cycle matching recurrence, and
the production-to-independent matching equivalence prove the closed formula directly. -/
theorem mancudeRule1aSimpleCycleBranchSound
    (mol : RawMolecule) (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique) : mol.MancudeRule1aSimpleCycleBranchSound :=
  mol.structuralMancudeRule1aSimpleCycleBranchSound hwellFormed hunique

end RawMolecule

end
end OneCenter
end TetraStereo
