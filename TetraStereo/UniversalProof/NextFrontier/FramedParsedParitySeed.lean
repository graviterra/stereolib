import TetraStereo.UniversalProof.NextFrontier.FramedParsedParityFamily
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace TetraStereo.UniversalProof.FramedParsedParitySeed
open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.FramedParsedParityFamily
/-- Independently specified constitutional seed: the two carbon-arm centers only. -/
def expectedSeed (left right : TetrahedralInputParity) : RawDescriptorState :=
  [{ atom := 2, descriptor := descriptorOfParity left false, uppercase := true,
     priorityPositions := [3, 2, 0, 1] },
   { atom := 7, descriptor := descriptorOfParity right false, uppercase := true,
     priorityPositions := [3, 2, 0, 1] }]
/-- Actual public discovery input, including normalization and hydrogen expansion. -/
def actualInitial? (center left right : TetrahedralInputParity) : Option RawDescriptorState := do
  let mol ← familyMol? center left right
  let result := normalizeRawMolecule mol
  let expanded := result.parsed.withExplicitHydrogens
  pure (initialRawDescriptorState result expanded (analysisFuel expanded))
/-- All eight actual initial states, full fields and exact enumeration order. -/
theorem actualInitial_eq_expected (center left right : TetrahedralInputParity) :
    actualInitial? center left right = some (expectedSeed left right) := by
  cases center <;> cases left <;> cases right <;> decide +kernel
/-- The chosen central written parity cannot change the two independent arm seeds. -/
theorem actualInitial_center_independent (first second left right : TetrahedralInputParity) :
    actualInitial? first left right = actualInitial? second left right := by
  rw [actualInitial_eq_expected, actualInitial_eq_expected]
/-- Exact population and absence of a pre-supplied central descriptor. -/
theorem expectedSeed_shape (left right : TetrahedralInputParity) :
    (expectedSeed left right).length = 2 ∧
    (expectedSeed left right).factAt? 1 = none := by
  cases left <;> cases right <;> decide
end TetraStereo.UniversalProof.FramedParsedParitySeed
