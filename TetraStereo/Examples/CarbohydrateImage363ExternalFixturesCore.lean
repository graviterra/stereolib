import TetraStereo.OneCenter.AuthoritativeChemicalInput
import TetraStereo.OneCenter.SmilesTetrahedral

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage363ExternalFixtures

open OneCenter

/-!
# External molecular-identity fixtures for 2-Carb-36.3 images 363A--C

These records exercise the parser, certified normalizer, format-neutral semantic bridge, and
descriptor analyzer for the three reducing-disaccharide examples printed in 2-Carb-36.3. The
isomeric SMILES and InChI strings were retrieved from PubChem PUG REST on 2026-08-11 (CIDs 6255,
84571, and 439271).

They are external identity fixtures, not source-to-graph transcriptions of the frozen IUPAC
rasters. In particular, the LacNAc fixture is a regression for the applicability boundary: its
ordinary acetamide nitrogen is not promoted to a tetrahedral stereogenic unit from connectivity
alone.
-/

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

def betaMaltose : ExternalIdentityFixture :=
  { sourceImagePath := "2carb/2C3gif/363A.GIF"
    commonName := "β-Maltose"
    pubChemCID := 6255
    isomericSmiles :=
      "C([C@@H]1[C@H]([C@@H]([C@H]([C@H](O1)O[C@@H]2[C@H](O[C@H]([C@@H]([C@H]2O)O)O)CO)O)O)O)O"
    inchi :=
      "InChI=1S/C12H22O11/c13-1-3-5(15)6(16)9(19)12(22-3)23-10-4(2-14)21-11(20)8(18)7(10)17/h3-20H,1-2H2/t3-,4-,5-,6+,7-,8-,9-,10-,11-,12-/m1/s1"
    parsedHeavyAtoms := 23
    totalAtoms := 45
    expectedReport :=
      "atom 1: R\natom 2: S\natom 3: S\natom 4: R\natom 5: R\natom 8: S\natom 9: R\natom 11: R\natom 12: R\natom 13: R" }

def alphaLactose : ExternalIdentityFixture :=
  { sourceImagePath := "2carb/2C3gif/363B.GIF"
    commonName := "α-Lactose"
    pubChemCID := 84571
    isomericSmiles :=
      "C([C@@H]1[C@@H]([C@@H]([C@H]([C@@H](O1)O[C@@H]2[C@H](O[C@@H]([C@@H]([C@H]2O)O)O)CO)O)O)O)O"
    inchi :=
      "InChI=1S/C12H22O11/c13-1-3-5(15)6(16)9(19)12(22-3)23-10-4(2-14)21-11(20)8(18)7(10)17/h3-20H,1-2H2/t3-,4-,5+,6+,7-,8-,9-,10-,11+,12+/m1/s1"
    parsedHeavyAtoms := 23
    totalAtoms := 45
    expectedReport :=
      "atom 1: R\natom 2: R\natom 3: S\natom 4: R\natom 5: S\natom 8: S\natom 9: R\natom 11: S\natom 12: R\natom 13: R" }

def nAcetyllactosamine : ExternalIdentityFixture :=
  { sourceImagePath := "2carb/2C3gif/363C.GIF"
    commonName := "N-Acetyllactosamine (LacNAc)"
    pubChemCID := 439271
    isomericSmiles :=
      "CC(=O)N[C@@H]1[C@H]([C@@H]([C@H](O[C@H]1O)CO)O[C@H]2[C@@H]([C@H]([C@H]([C@H](O2)CO)O)O)O)O"
    inchi :=
      "InChI=1S/C14H25NO11/c1-4(18)15-7-9(20)12(6(3-17)24-13(7)23)26-14-11(22)10(21)8(19)5(2-16)25-14/h5-14,16-17,19-23H,2-3H2,1H3,(H,15,18)/t5-,6-,7-,8+,9-,10+,11-,12-,13-,14+/m1/s1"
    parsedHeavyAtoms := 26
    totalAtoms := 51
    expectedReport :=
      "atom 4: R\natom 5: R\natom 6: S\natom 7: R\natom 9: R\natom 14: S\natom 15: R\natom 16: S\natom 17: R\natom 18: R" }

def all : List ExternalIdentityFixture := [betaMaltose, alphaLactose, nAcetyllactosamine]

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

end TetraStereo.Examples.CarbohydrateImage363ExternalFixtures
