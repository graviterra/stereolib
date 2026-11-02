import TetraStereo.OneCenter.AuthoritativeChemicalInput
import TetraStereo.OneCenter.SmilesTetrahedral

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures

open OneCenter













structure ExternalIdentityFixture where
  sourceImagePath : String
  commonName : String
  pubChemCID : Nat
  isomericSmiles : String
  inchi : String
  parsedHeavyAtoms : Nat
  totalAtoms : Nat
  expectedReport : String
  deriving DecidableEq, Repr

def trehalose : ExternalIdentityFixture :=
  { sourceImagePath := "2carb/2C3gif/362A.GIF"
    commonName := "α,α-Trehalose"
    pubChemCID := 7427
    isomericSmiles :=
      "C([C@@H]1[C@H]([C@@H]([C@H]([C@H](O1)O[C@@H]2[C@@H]([C@H]([C@@H]([C@H](O2)CO)O)O)O)O)O)O)O"
    inchi :=
      "InChI=1S/C12H22O11/c13-1-3-5(15)7(17)9(19)11(21-3)23-12-10(20)8(18)6(16)4(2-14)22-12/h3-20H,1-2H2/t3-,4-,5-,6-,7+,8+,9-,10-,11-,12-/m1/s1"
    parsedHeavyAtoms := 23
    totalAtoms := 45
    expectedReport :=
      "atom 1: R\natom 2: S\natom 3: S\natom 4: R\natom 5: R\natom 8: R\natom 9: R\natom 10: S\natom 11: S\natom 12: R" }

def sucrose : ExternalIdentityFixture :=
  { sourceImagePath := "2carb/2C3gif/362B.GIF"
    commonName := "Sucrose"
    pubChemCID := 5988
    isomericSmiles :=
      "C([C@@H]1[C@H]([C@@H]([C@H]([C@H](O1)O[C@]2([C@H]([C@@H]([C@H](O2)CO)O)O)CO)O)O)O)O"
    inchi :=
      "InChI=1S/C12H22O11/c13-1-4-6(16)8(18)9(19)11(21-4)23-12(3-15)10(20)7(17)5(2-14)22-12/h4-11,13-20H,1-3H2/t4-,5-,6-,7-,8+,9-,10+,11-,12+/m1/s1"
    parsedHeavyAtoms := 23
    totalAtoms := 45
    expectedReport :=
      "atom 1: R\natom 2: S\natom 3: S\natom 4: R\natom 5: R\natom 8: S\natom 9: S\natom 10: S\natom 11: R" }

def sucralose : ExternalIdentityFixture :=
  { sourceImagePath := "2carb/2C3gif/362C.GIF"
    commonName := "Sucralose"
    pubChemCID := 71485
    isomericSmiles :=
      "C([C@@H]1[C@@H]([C@@H]([C@H]([C@H](O1)O[C@]2([C@H]([C@@H]([C@H](O2)CCl)O)O)CCl)O)O)Cl)O"
    inchi :=
      "InChI=1S/C12H19Cl3O8/c13-1-4-7(17)10(20)12(3-14,22-4)23-11-9(19)8(18)6(15)5(2-16)21-11/h4-11,16-20H,1-3H2/t4-,5-,6+,7-,8+,9-,10+,11-,12+/m1/s1"
    parsedHeavyAtoms := 23
    totalAtoms := 42
    expectedReport :=
      "atom 1: R\natom 2: R\natom 3: R\natom 4: R\natom 5: R\natom 8: R\natom 9: S\natom 10: S\natom 11: S" }

def all : List ExternalIdentityFixture := [trehalose, sucrose, sucralose]

@[simp] theorem fixture_count : all.length = 3 := by decide

def parsedHeavyAtomCount (fixture : ExternalIdentityFixture) : Nat :=
  match parseOpenSMILES fixture.isomericSmiles with
  | .ok molecule => molecule.atomCount
  | .error _ => 0

def expandedAtomCount (fixture : ExternalIdentityFixture) : Nat :=
  match parseOpenSMILES fixture.isomericSmiles with
  | .ok molecule => molecule.normalizeUnspecifiedBonds.withExplicitHydrogens.atomCount
  | .error _ => 0

def authoritativeInput? (fixture : ExternalIdentityFixture) : Option AuthoritativeChemicalInput :=
  match parseOpenSMILES fixture.isomericSmiles with
  | .error _ => none
  | .ok molecule =>
      molecule.normalizeUnspecifiedBonds.withExplicitHydrogens.toAuthoritativeChemicalInput?

end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures
