import TetraStereo.OneCenter.LocalizedRule3ShortCircuitOddNode
import TetraStereo.OneCenter.LocalizedFamilyReferencePipeline

set_option autoImplicit false
namespace TetraStereo.Examples.LocalizedRule3ShortCircuitOddProbe
open OneCenter OneCenter.CertifiedLocalizedCIPInput OneCenter.LocalizedShortCircuit

/-- Two linked odd axes, with explicit substituents and independently specified planar coordinates.
First axis senior references are on the same side; second axis senior references are opposite. -/
def source : AuthoritativeChemicalInput :=
  let carbon : PeriodicElement := ⟨6, by decide, by decide⟩
  let hydrogen : PeriodicElement := ⟨1, by decide, by decide⟩
  let fluorine : PeriodicElement := ⟨9, by decide, by decide⟩
  let bond (a b order : Nat) : SemanticInteraction :=
    { participants := [a, b], kind := .covalent order }
  { molecule :=
      { atoms := (List.replicate 8 carbon ++ [fluorine, hydrogen, fluorine, hydrogen, hydrogen, hydrogen]).map
          fun element => { element }
        interactions := [bond 0 1 2, bond 1 2 2, bond 2 3 2, bond 3 4 1,
          bond 4 5 2, bond 5 6 2, bond 6 7 2,
          bond 0 8 1, bond 0 9 1, bond 7 10 1, bond 7 11 1, bond 3 12 1, bond 4 13 1] }
    spatial? := some { positions :=
      [{ x := 0, y := 0, z := 0 }, { x := 1, y := 0, z := 0 },
       { x := 2, y := 0, z := 0 }, { x := 3, y := 0, z := 0 },
       { x := 3, y := 1, z := 0 }, { x := 4, y := 1, z := 0 },
       { x := 5, y := 1, z := 0 }, { x := 6, y := 1, z := 0 },
       { x := 0, y := 1, z := 0 }, { x := 0, y := -1, z := 0 },
       { x := 6, y := 2, z := 0 }, { x := 6, y := 0, z := 0 },
       { x := 3, y := -1, z := 0 }, { x := 3, y := 2, z := 0 }] } }

private def checkTest (name : String) (condition : Bool) : IO Unit :=
  if condition then IO.println ("ok: " ++ name)
  else throw (IO.userError ("failed: " ++ name))

def main : IO Unit := do
  let start ← IO.monoMsNow
  let some input := admitSource? source | throw (IO.userError "linked axes admission failed")
  let roots := (Families.canonicalDoubleBonds input).filter fun bond =>
    (bond.val.1.val == 0 && bond.val.2.val == 1) ||
    (bond.val.1.val == 4 && bond.val.2.val == 5)
  checkTest "exactly two formerly cyclic canonical roots selected" (roots.length == 2)
  for bond in roots do
    let name := s!"axis root ({bond.val.1.val},{bond.val.2.val})"
    let occurrence := input.certified.localizedCanonicalDoubleBondFirstChildOccurrenceExec
      (carrierFuel input) bond
    let target := OrdinaryPlanar.target input.certified (carrierFuel input) bond
    let view : input.certified.LocalizedDependencyView target := fun _ _ => none
    let callback : List (input.certified.LocalizedRerootCursor (carrierFuel input)) →
        Option input.certified.LocalizedRule3CanonicalKeyFrame := fun _ => none
    checkTest (name ++ " exact odd route accepted")
      (input.certified.localizedRule3OddRouteCertificate? occurrence).isSome
    checkTest (name ++ " new endpoint callback requests empty")
      (input.certified.rule3ExtendedNodeCallbackRequests occurrence).isEmpty
    checkTest (name ++ " old endpoint callback requests nonempty")
      (!(input.certified.rule3NodeCallbackRequests occurrence).isEmpty)
    let some spatial := input.certified.localizedRule3ShortCircuitOddSpatialUnitWithExec?
        target occurrence view callback | throw (IO.userError (name ++ " shortcut spatial refused"))
    let expected : OfficialRule3Geometry := if bond.val.1.val == 0 then .seqcis else .seqtrans
    checkTest (name ++ " exact expected planar geometry") (decide (spatial.unit.geometry = expected))
    let observation := input.certified.localizedRule3ShortCircuitOddSpatialObservation spatial
    let result := input.certified.localizedRule3ExtendedShortCircuitNodeWithExec?
      target occurrence view callback []
    checkTest (name ++ " new node succeeds with always-none callback")
      (decide (result = some (some observation)))
    checkTest (name ++ " excluded physical unit is omitted after geometry")
      (decide (input.certified.localizedRule3ExtendedShortCircuitNodeWithExec?
        target occurrence view callback [observation.physicalUnitId] = some none))
    checkTest (name ++ " old node refuses with always-none callback")
      (input.certified.localizedDescriptorBearingRule3NodeWithExec?
        target occurrence view callback []).isNone
  let finish ← IO.monoMsNow
  IO.println s!"TIMING linked odd-axis shortcut: {finish - start}ms"

#eval main
end TetraStereo.Examples.LocalizedRule3ShortCircuitOddProbe
