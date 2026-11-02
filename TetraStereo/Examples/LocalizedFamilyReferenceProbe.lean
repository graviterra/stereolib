import TetraStereo.OneCenter.LocalizedFamilyReferencePipeline
import TetraStereo.Examples.LocalizedOmissionReadinessProbe
import TetraStereo.Examples.LocalizedPerceptionExecutableProbe

set_option autoImplicit false
namespace TetraStereo.Examples.LocalizedFamilyReferenceProbe
open OneCenter OneCenter.CertifiedLocalizedCIPInput OneCenter.LocalizedShortCircuit

private def carbon : PeriodicElement := ⟨6, by decide, by decide⟩
private def hydrogen : PeriodicElement := ⟨1, by decide, by decide⟩
private def fluorine : PeriodicElement := ⟨9, by decide, by decide⟩
private def bond (left right order : Nat) : SemanticInteraction :=
  { participants := [left, right], kind := .covalent order }

def oddSource (cis : Bool) : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := [carbon, carbon, carbon, carbon, fluorine, hydrogen, fluorine, hydrogen].map
          fun element => { element }
        interactions := [bond 0 1 2, bond 1 2 2, bond 2 3 2,
          bond 0 4 1, bond 0 5 1, bond 3 6 1, bond 3 7 1] }
    spatial? := some { positions :=
      [{ x := 0, y := 0, z := 0 }, { x := 1, y := 0, z := 0 },
       { x := 2, y := 0, z := 0 }, { x := 3, y := 0, z := 0 },
       { x := 0, y := 1, z := 0 }, { x := 0, y := -1, z := 0 },
       { x := 3, y := if cis then 1 else -1, z := 0 },
       { x := 3, y := if cis then -1 else 1, z := 0 }] } }

/-- Fully explicit cyclooctene with senior ring references on the same side of its double bond. -/
def largeRingSource : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := (List.replicate 8 carbon ++ List.replicate 14 hydrogen).map fun element => { element }
        interactions := [bond 0 1 2] ++ ((List.range 7).map fun i => bond (i + 1) ((i + 2) % 8) 1) ++
          [bond 0 8 1, bond 1 9 1] ++ ((List.range 6).flatMap fun i =>
            [bond (i + 2) (10 + 2 * i) 1, bond (i + 2) (11 + 2 * i) 1]) }
    spatial? := some { positions :=
      [{ x := 0, y := 0, z := 0 }, { x := 2, y := 0, z := 0 },
       { x := 3, y := 1, z := 0 }, { x := 3, y := 2, z := 0 },
       { x := 2, y := 3, z := 0 }, { x := 0, y := 3, z := 0 },
       { x := -1, y := 2, z := 0 }, { x := -1, y := 1, z := 0 }] ++
         (List.range 14).map fun i => { x := (i + 3 : Nat), y := (i + 4 : Nat), z := (i + 5 : Nat) } } }

private def checkTest (name : String) (condition : Bool) : IO Unit :=
  if condition then IO.println ("ok: " ++ name)
  else throw (IO.userError ("failed: " ++ name))

private def runSource (source : AuthoritativeChemicalInput) :
    IO ((input : Input) × Families.Result input) := do
  let some result := Families.evaluateSource? source | throw (IO.userError "family input rejected")
  pure result

def main : IO Unit := do
  let allene ← runSource LocalizedOmissionReadinessProbe.alleneSource
  checkTest "one canonical even-axis candidate is retained" (allene.2.even.length == 1)
  checkTest "allene full pipeline emits Ra"
    (decide (allene.2.even.map (fun attempt => attempt.outcome.map (fun a => a.result.assignment.descriptor)) =
      [some .Ra]))
  checkTest "preferred allene descriptor is M"
    (decide (allene.2.even.map (fun attempt => attempt.outcome.map
      (fun a => a.result.assignment.descriptor.toPreferredP93)) = [some .M]))
  checkTest "same checked state also supplies tetrahedral R"
    (decide (report allene.1 allene.2.auxiliary.facts = [(0, some (.chiral .R))]))
  let mirrorSource := { LocalizedOmissionReadinessProbe.alleneSource with
    spatial? := LocalizedOmissionReadinessProbe.alleneSource.spatial?.map fun spatial =>
      { positions := spatial.positions.map fun point => { point with z := -point.z } } }
  let mirror ← runSource mirrorSource
  checkTest "reflected allene emits Sa and preferred P"
    (decide (mirror.2.even.map (fun attempt => attempt.outcome.map
      (fun a => (a.result.assignment.descriptor, a.result.assignment.descriptor.toPreferredP93))) =
        [some (.Sa, .P)]))
  let missing ← runSource { LocalizedOmissionReadinessProbe.alleneSource with spatial? := none }
  checkTest "missing geometry retains the even-axis candidate with refused outcome"
    (missing.2.even.length == 1 && missing.2.even.all (fun attempt => attempt.outcome.isNone))
  for cis in [false, true] do
    let odd ← runSource (oddSource cis)
    IO.println s!"odd cis={cis}, descriptors={repr (odd.2.odd.map (fun attempt => attempt.outcome.map (fun a => a.result.descriptor)))}"
    checkTest "nonordinary odd cumulene emits the expected E/Z descriptor"
      (decide (odd.2.odd.map (fun attempt => attempt.outcome.map (fun a => a.result.descriptor)) =
        [some (if cis then .Z else .E)]))
  let ring ← runSource LocalizedOmissionReadinessProbe.ringSource
  checkTest "small-ring final omission retains its physical bond attempt"
    (ring.2.monocyclic.length == 1 && ring.2.monocyclic.all (fun attempt => attempt.outcome.isNone))
  let some ringInput := admitSource? largeRingSource | throw (IO.userError "ring input rejected")
  let cache := Cached.buildRuntimeCache ringInput
  let some ringCenter := ringInput.certified.canonicalTetrahedralCenters.find? (fun center => center.1.val == 2)
    | throw (IO.userError "ring tetrahedral candidate absent")
  let target := ringInput.certified.localizedAtomRootOccurrenceExecutable (carrierFuel ringInput) ringCenter.1
  let readChildren := ringInput.certified.localizedRerootChildrenFromCarrier? cache.carrier
  let some base := WithChildren.localizedNoDoubleFourLigandFrameExec? ringInput.certified readChildren target
    | throw (IO.userError "ring candidate frame absent")
  let emptyView : ringInput.certified.LocalizedDependencyView target := fun _ _ => none
  checkTest "terminal H pair yields an automatic refusal certificate"
    (TerminalTie.refusalCertificate? ringInput.certified readChildren target emptyView base).isSome
  let unequalView : ringInput.certified.LocalizedDependencyView target := fun occurrence _ =>
    if occurrence.1.node.current?.map Fin.val == some 10 then some (.chiral .R) else some (.chiral .S)
  checkTest "unequal supplied dependency labels prevent the terminal tie shortcut"
    (TerminalTie.refusalCertificate? ringInput.certified readChildren target unequalView base).isNone
  let largeRing ← runSource largeRingSource
  checkTest "eight-membered ring emits required final Z"
    (decide (largeRing.2.monocyclic.map (fun attempt => attempt.outcome.map (fun a => a.result.descriptor)) =
      [some .Z]))
  let cyclic ← runSource (LocalizedPerceptionExecutableProbe.source true false)
  checkTest "fully cyclic cumulene is reported as one topology boundary"
    (cyclic.2.boundaries.length == 1 && cyclic.2.even.isEmpty && cyclic.2.odd.isEmpty)

#eval main
end TetraStereo.Examples.LocalizedFamilyReferenceProbe
