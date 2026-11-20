import TetraStereo.OneCenter.LocalizedMarkedRetainedPromotedOperations
import TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCompletion

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 0

/-!
# Chemical-information probe of the retained promoted operations

This fixture uses the actual successor operations and the existing certified subdivided cage.
The diagnostic expressions contain no supplied auxiliary labels and no whole-state run.
They are definitions only: the dense default marker would materialize `22 ^ 46` entries in
its deepest row. Tests must use the proved sparse successor rather than execute these dense
expressions during import. Prior bounded attempts and their memory failures are preserved.
-/

namespace TetraStereo.OneCenter.LocalizedPhysicalMarkedCorrectnessProbe

open LocalizedMarkedOperationEvaluator
open LocalizedRecursiveAuxiliaryPhysicalCompletion

-- The existing subdivided-cage source, kept local to avoid importing and replaying the
-- whole-state executable experiments in LocalizedMarkedSubdividedCageProbe.
private def bond (a b : Nat) : RawBond := { source := a, target := b, kind := .single }

def mol : RawMolecule where
  atoms := [.aliphatic .C, .aliphatic .H, .aliphatic .Cl, .aliphatic .C, .aliphatic .H,
    .aliphatic .O, .aliphatic .O, .aliphatic .O, .aliphatic .C, .aliphatic .C, .aliphatic .H,
    .aliphatic .O, .aliphatic .O, .aliphatic .O, .aliphatic .C] ++
    List.replicate 6 (.aliphatic .O)
  bonds := [bond 0 1, bond 0 2, bond 0 3, bond 0 9,
    bond 3 5, bond 3 6, bond 3 7, bond 4 8,
    bond 5 15, bond 15 8, bond 6 16, bond 16 8, bond 7 17, bond 17 8,
    bond 9 11, bond 9 12, bond 9 13, bond 10 14,
    bond 11 18, bond 18 14, bond 12 19, bond 19 14, bond 13 20, bond 20 14]
  neighborOrder := [[1,2,3,9], [0], [0], [0,5,6,7], [8], [3,15], [3,16], [3,17],
    [4,15,16,17], [0,11,12,13], [14], [9,18], [9,19], [9,20], [10,18,19,20],
    [5,8], [6,8], [7,8], [11,14], [12,14], [13,14]]

def far : RawMolecule.CanonicalBranchNode :=
  { atom := 8, parent := 15, history := [8,15,5,3,0], provenance := .realAtom }

def points : List CartesianPoint3 :=
  positions ++ [point (7/2) (1/2) 0, point (7/2) (-1/2) (1/2),
    point (7/2) (-1/2) (-1/2), point (-7/2) (1/2) 0,
    point (-7/2) (-1/2) (1/2), point (-7/2) (-1/2) (-1/2)]

def geom : LocalizedGenericMarkedRecalculation.Geometry := fun atom => points[atom]?

def source : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := cageSource.molecule.atoms ++ List.replicate 6 oxygen
        interactions := mol.bonds.map fun b =>
          LocalizedCyclicPseudoInputWitness.singleBond b.source b.target }
    spatial? := some { positions := points } }

theorem source_wellFormed : source.structurallyWellFormed? = true := by decide +kernel
theorem source_graphReady : source.molecule.localizedCIPGraphReady? = true := by decide +kernel

def certified : CertifiedLocalizedCIPInput where
  certified :=
    { input := source
      structurallyWellFormed :=
        (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff source).mp source_wellFormed }
  graphReady := source.molecule.localizedCIPGraphReady?_eq_true_iff.mp source_graphReady

def actualOperations : Operations :=
  LocalizedMarkedRetainedPromotedOperations.operations certified mol

-- The inherited atom 6 lies deeper in a branch, outside the far centre's four-atom frame.
def directDistantReading : Option RS := markedReading? mol actualOperations geom [] far 6

-- Compare the same raw-result type before the original/mirror case classifier.
def rawDistantReading : Option RS :=
  rawStep? mol actualOperations geom [] (some 6) far (fun _ => [])

def reflectedRawDistantReading : Option RS :=
  rawStep? mol actualOperations (LocalizedGenericMarkedRecalculation.mirror geom)
    [] (some 6) far (fun _ => [])

-- Zero-depth evaluation at this same occurrence: no auxiliary labels are inserted.
def depthZeroDescriptor : Option LocalizedTetrahedralRSPseudoDescriptor :=
  descriptor? mol actualOperations 0 geom [] (some 6) far

end TetraStereo.OneCenter.LocalizedPhysicalMarkedCorrectnessProbe
