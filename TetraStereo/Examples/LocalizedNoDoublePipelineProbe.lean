import TetraStereo.OneCenter.LocalizedNoDoubleReferenceInput
import TetraStereo.OneCenter.LocalizedNoDoubleDescriptorExecutable
import TetraStereo.OneCenter.LocalizedOccurrenceFiniteCarrier
import TetraStereo.OneCenter.LocalizedOccurrenceExecutableRoots
import TetraStereo.OneCenter.FiniteStateIteration

set_option autoImplicit false

namespace TetraStereo.Examples.LocalizedNoDoublePipelineProbe
open OneCenter

private def element (atomicNumber : ℕ) (positive : 0 < atomicNumber)
    (bounded : atomicNumber ≤ 118) : PeriodicElement :=
  { atomicNumber := atomicNumber, positive := positive, atMost118 := bounded }

private def carbon : PeriodicElement := element 6 (by decide) (by decide)
private def fluorine : PeriodicElement := element 9 (by decide) (by decide)
private def chlorine : PeriodicElement := element 17 (by decide) (by decide)
private def bromine : PeriodicElement := element 35 (by decide) (by decide)
private def iodine : PeriodicElement := element 53 (by decide) (by decide)

/-- A format-neutral localized molecule with one constitutional four-neighbor center. -/
private def halomethaneInput : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms :=
          [{ element := carbon }, { element := fluorine }, { element := chlorine },
           { element := bromine }, { element := iodine }]
        interactions :=
          [{ participants := [0, 1], kind := .covalent 1 },
           { participants := [0, 2], kind := .covalent 1 },
           { participants := [0, 3], kind := .covalent 1 },
           { participants := [0, 4], kind := .covalent 1 }] }
    spatial? := some
      { positions :=
          [{ x := 0, y := 0, z := 0 },
           { x := -1, y := -1, z := 1 },
           { x := -1, y := 1, z := -1 },
           { x := 1, y := -1, z := -1 },
           { x := 1, y := 1, z := 1 }] } }


/-- Runtime-only baseline: every certificate in the input is supplied by checked admission. -/
def baseline : Option (Nat × List (Nat × Option CertifiedLocalizedCIPInput.LocalizedAuxiliaryLabel)) := do
  let admitted ← LocalizedNoDoubleReference.admitSource? halomethaneInput
  let input := admitted.certified
  let fuel := input.certified.input.molecule.atomCount + 1
  let carrier := input.localizedOccurrenceCarrier fuel
  let facts := FiniteStateIteration.tabulatedFacts carrier
    (input.localizedExecutableStep input.localizedNoDoubleDescriptorExec?)
    (fun _ => none) (fuel + 2)
  let results := input.canonicalTetrahedralCenters.map fun center =>
    (center.val.val, Certificate.Dependency.lookup facts
      (input.localizedFinalOccurrenceExecutable fuel center))
  some (carrier.length, results)

#eval baseline

#eval show IO Unit from do
  match baseline with
  | some (_, [(0, some (.chiral .R))]) => pure ()
  | _ => throw (IO.userError "reference baseline failed to assign expected R at the admitted center")

end TetraStereo.Examples.LocalizedNoDoublePipelineProbe
