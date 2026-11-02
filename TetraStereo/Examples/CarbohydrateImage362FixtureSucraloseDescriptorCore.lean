import TetraStereo.Examples.CarbohydrateImage362FixtureCore

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
namespace SucraloseDescriptorCertificate

open OneCenter

def parsed : RawMolecule :=
  match parseOpenSMILES sucralose.isomericSmiles with
  | .error _ => { atoms := [], bonds := [] }
  | .ok molecule => molecule

def normalized := normalizeRawMolecule parsed
def expanded := normalized.parsed.withExplicitHydrogens
def fuel := analysisFuel expanded

def expectedFact (atom : Nat) (descriptor : RS)
    (priorityPositions : List Nat) : RawDescriptorFact :=
  { atom := atom, descriptor := descriptor, uppercase := true,
    priorityPositions := priorityPositions }

def expectedDescriptorState0To7 : RawDescriptorState :=
  [ expectedFact 1 .R [2, 3, 0, 1],
    expectedFact 2 .R [3, 0, 2, 1],
    expectedFact 3 .R [3, 0, 2, 1],
    expectedFact 4 .R [3, 2, 0, 1],
    expectedFact 5 .R [3, 2, 0, 1] ]

def expectedDescriptorState8To15 : RawDescriptorState :=
  [ expectedFact 8 .R [0, 1, 3, 2],
    expectedFact 9 .S [3, 0, 2, 1],
    expectedFact 10 .S [3, 2, 0, 1],
    expectedFact 11 .S [2, 3, 0, 1] ]

def expectedDescriptorState16To22 : RawDescriptorState := []

def expectedDescriptorState : RawDescriptorState :=
  expectedDescriptorState0To7 ++ expectedDescriptorState8To15 ++
    expectedDescriptorState16To22

def atomRange0To7 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]
def atomRange8To15 : List Nat := [8, 9, 10, 11, 12, 13, 14, 15]
def atomRange16To22 : List Nat := [16, 17, 18, 19, 20, 21, 22]

def initialFactAt (idx : Nat) : Option RawDescriptorFact :=
  match tetrahedralOutcomeThroughRule3 normalized expanded fuel idx with
  | StereoOutcome.tetrahedral descriptor =>
      let positions := (rankBranchPositionsThroughRule3? normalized expanded fuel idx
        (expanded.ligandsWithLonePair idx)).getD []
      some (expectedFact idx descriptor positions)
  | _ => none

theorem atomCount_eq : normalized.parsed.atomCount = 23 := by rfl

theorem initialState_as_filterMap :
    initialRawDescriptorState normalized expanded fuel =
      (List.range normalized.parsed.atomCount).filterMap initialFactAt := by
  rfl

end SucraloseDescriptorCertificate
end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
