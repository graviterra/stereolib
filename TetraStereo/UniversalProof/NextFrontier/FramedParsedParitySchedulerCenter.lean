import TetraStereo.UniversalProof.NextFrontier.FramedParsedParitySeed

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-! Eight independently bounded actual center-update candidates. The candidate metadata is from
Root's successful all-eight compiled observations; each preserved actual-guard call is proved only
if this module passes its kernel gate. No pass, solver, report or source semantics is asserted. -/
namespace TetraStereo.UniversalProof.FramedParsedParitySchedulerCenter
open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.FramedParsedParityFamily
open TetraStereo.UniversalProof.FramedParsedParitySeed

def parsedRaw (center left right : TetrahedralInputParity) : RawMolecule :=
  (familyMol? center left right).getD { atoms := [], bonds := [] }

def actualResult (center left right : TetrahedralInputParity) : ChemistryNormalizationResult :=
  normalizeRawMolecule (parsedRaw center left right)

def actualMol (center left right : TetrahedralInputParity) : RawMolecule :=
  (actualResult center left right).parsed.withExplicitHydrogens

def actualFuel (center left right : TetrahedralInputParity) : Nat :=
  analysisFuel (actualMol center left right)

/-- Full central metadata observed in the actual guarded caller, including the two auxiliary
sources. This candidate is not installed as an executable output. The center guard leaves below
must prove it from the maintained call. -/
def centralCandidate (center left right : TetrahedralInputParity) : Option RawDescriptorFact :=
  (expectedFact? center left right).map fun fact =>
    { atom := 1, descriptor := fact.descriptor, uppercase := fact.uppercase,
      evidenceSize := 2, decisiveRule? := none, descriptorDependentPairs := 2,
      priorityPositions := fact.priorityPositions }

/-! The following are the only expensive finite assignment leaves. -/
theorem central_aaa :
    tetrahedralFactFromState? (actualResult .anticlockwise .anticlockwise .anticlockwise)
      (actualMol .anticlockwise .anticlockwise .anticlockwise) (expectedSeed .anticlockwise .anticlockwise) 100
      (actualFuel .anticlockwise .anticlockwise .anticlockwise) 1 = centralCandidate .anticlockwise .anticlockwise .anticlockwise := by
  decide +kernel

theorem central_aac :
    tetrahedralFactFromState? (actualResult .anticlockwise .anticlockwise .clockwise)
      (actualMol .anticlockwise .anticlockwise .clockwise) (expectedSeed .anticlockwise .clockwise) 100
      (actualFuel .anticlockwise .anticlockwise .clockwise) 1 = centralCandidate .anticlockwise .anticlockwise .clockwise := by
  decide +kernel

theorem central_aca :
    tetrahedralFactFromState? (actualResult .anticlockwise .clockwise .anticlockwise)
      (actualMol .anticlockwise .clockwise .anticlockwise) (expectedSeed .clockwise .anticlockwise) 100
      (actualFuel .anticlockwise .clockwise .anticlockwise) 1 = centralCandidate .anticlockwise .clockwise .anticlockwise := by
  decide +kernel

theorem central_acc :
    tetrahedralFactFromState? (actualResult .anticlockwise .clockwise .clockwise)
      (actualMol .anticlockwise .clockwise .clockwise) (expectedSeed .clockwise .clockwise) 100
      (actualFuel .anticlockwise .clockwise .clockwise) 1 = centralCandidate .anticlockwise .clockwise .clockwise := by
  decide +kernel

theorem central_caa :
    tetrahedralFactFromState? (actualResult .clockwise .anticlockwise .anticlockwise)
      (actualMol .clockwise .anticlockwise .anticlockwise) (expectedSeed .anticlockwise .anticlockwise) 100
      (actualFuel .clockwise .anticlockwise .anticlockwise) 1 = centralCandidate .clockwise .anticlockwise .anticlockwise := by
  decide +kernel

theorem central_cac :
    tetrahedralFactFromState? (actualResult .clockwise .anticlockwise .clockwise)
      (actualMol .clockwise .anticlockwise .clockwise) (expectedSeed .anticlockwise .clockwise) 100
      (actualFuel .clockwise .anticlockwise .clockwise) 1 = centralCandidate .clockwise .anticlockwise .clockwise := by
  decide +kernel

theorem central_cca :
    tetrahedralFactFromState? (actualResult .clockwise .clockwise .anticlockwise)
      (actualMol .clockwise .clockwise .anticlockwise) (expectedSeed .clockwise .anticlockwise) 100
      (actualFuel .clockwise .clockwise .anticlockwise) 1 = centralCandidate .clockwise .clockwise .anticlockwise := by
  decide +kernel

theorem central_ccc :
    tetrahedralFactFromState? (actualResult .clockwise .clockwise .clockwise)
      (actualMol .clockwise .clockwise .clockwise) (expectedSeed .clockwise .clockwise) 100
      (actualFuel .clockwise .clockwise .clockwise) 1 = centralCandidate .clockwise .clockwise .clockwise := by
  decide +kernel

theorem central_update_fact (center left right : TetrahedralInputParity) :
    tetrahedralFactFromState? (actualResult center left right) (actualMol center left right)
      (expectedSeed left right) 100 (actualFuel center left right) 1 =
        centralCandidate center left right := by
  cases center with
  | anticlockwise =>
      cases left with
      | anticlockwise =>
          cases right with
          | anticlockwise => exact central_aaa
          | clockwise => exact central_aac
      | clockwise =>
          cases right with
          | anticlockwise => exact central_aca
          | clockwise => exact central_acc
  | clockwise =>
      cases left with
      | anticlockwise =>
          cases right with
          | anticlockwise => exact central_caa
          | clockwise => exact central_cac
      | clockwise =>
          cases right with
          | anticlockwise => exact central_cca
          | clockwise => exact central_ccc

end TetraStereo.UniversalProof.FramedParsedParitySchedulerCenter
