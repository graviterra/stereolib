import TetraStereo.OneCenter.LocalizedShortCircuitSupportedDescriptorCertificate

set_option autoImplicit false
namespace TetraStereo.Examples.LocalizedOmissionReadinessProbe
open OneCenter OneCenter.CertifiedLocalizedCIPInput OneCenter.LocalizedShortCircuit

private def carbon : PeriodicElement := ⟨6, by decide, by decide⟩
private def hydrogen : PeriodicElement := ⟨1, by decide, by decide⟩
private def fluorine : PeriodicElement := ⟨9, by decide, by decide⟩
private def chlorine : PeriodicElement := ⟨17, by decide, by decide⟩
private def bromine : PeriodicElement := ⟨35, by decide, by decide⟩
private def bond (left right order : Nat) : SemanticInteraction :=
  { participants := [left, right], kind := .covalent order }

/-- Central priorities Br > Cl > F > C occupy the same rank-ordered coordinates as the
existing R halomethane fixture. Remaining points are synthetic exact coordinates. -/
def spatial (branch : Nat) : SpatialConfiguration :=
  { positions := (List.range 10).map fun i =>
      if i = 0 then { x := 0, y := 0, z := 0 }
      else if i = 1 then { x := -1, y := 1, z := -1 }
      else if i = 2 then { x := 1, y := -1, z := -1 }
      else if i = 3 then { x := 1, y := 1, z := 1 }
      else if i = branch then { x := -1, y := -1, z := 1 }
      else { x := (i + 2 : Nat), y := ((i + 2 : Nat) : Rat) ^ 2, z := ((i + 2 : Nat) : Rat) ^ 3 } }

/-- One even cumulene branch attached to a strict tetrahedral center. -/
def alleneSource : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := [carbon, fluorine, chlorine, bromine, carbon, carbon, carbon,
          fluorine, hydrogen, hydrogen].map fun element => { element }
        interactions := [bond 0 1 1, bond 0 2 1, bond 0 3 1, bond 0 4 1,
          bond 4 5 2, bond 5 6 2, bond 6 7 1, bond 4 8 1, bond 6 9 1] }
    spatial? := some (spatial 4) }

/-- One ordinary three-membered monocycle branch at the same strict tetrahedral center. -/
def ringSource : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := [carbon, fluorine, chlorine, bromine, carbon, carbon, carbon,
          hydrogen, hydrogen, hydrogen].map fun element => { element }
        interactions := [bond 0 1 1, bond 0 2 1, bond 0 3 1, bond 0 6 1,
          bond 4 5 2, bond 5 6 1, bond 6 4 1, bond 4 7 1, bond 5 8 1, bond 6 9 1] }
    spatial? := some (spatial 6) }

private def checkTest (name : String) (condition : Bool) : IO Unit :=
  if condition then IO.println ("ok: " ++ name)
  else throw (IO.userError ("failed: " ++ name))

private def isInternal (input : Input) (occurrence : Occurrence input) : Bool :=
  match input.certified.localizedRule3CumulatedAxisEntryExec? occurrence with
  | some (.internal _ _) => true
  | _ => false

private def isEvenTerminal (input : Input) (occurrence : Occurrence input) : Bool :=
  match input.certified.localizedRule3CumulatedAxisEntryExec? occurrence with
  | some (.terminalStart _) =>
      match input.certified.localizedRule3CumulatedEndpointCursorFrameExec?
          (input.certified.localizedRule3CumulatedTraversalFuel (carrierFuel input)) occurrence with
      | some axis => axis.doubleBondCount == 2
      | none => false
  | _ => false

private def isOmittedRing (input : Input) (occurrence : Occurrence input) : Bool :=
  match input.certified.localizedRule3CumulatedAxisEntryExec? occurrence with
  | some (.ringClosure _ _) =>
      match input.certified.localizedRule3CyclicAuthorityRouteExec? occurrence with
      | some (.ordinaryMonocyclicPolicy _ _ policy) => decide (policy.policy = .permanentlyOmit)
      | _ => false
  | _ => false

private def selectedOmissions (input : Input) (selected : List (Occurrence input)) : Bool :=
  !selected.isEmpty && selected.all fun occurrence =>
    (input.certified.localizedRule3OmissionCertificate? occurrence).isSome &&
    decide (input.certified.localizedRule3ShortCircuitNodeWithExec?
      occurrence occurrence (fun _ _ => none) (fun _ => none) [] = some none)

private def checkTarget (name : String) (input : Input) : IO Unit := do
  checkTest (name ++ " constructs carrier-wide readiness")
    (input.certified.localizedRule3CallbackFreeCarrierCertificate? (carrierFuel input)).isSome
  let some result := certifyCenter? input 0
    | throw (IO.userError (name ++ " target certificate missing"))
  checkTest (name ++ " automatically certifies central R")
    (decide (result.descriptor = .chiral .R))
  let cache := result.certificate.cache
  let some facts := Certificate.Dependency.check (Cached.systemUsingCache input cache)
      (Cached.dependenciesUsingCache input cache) result.certificate.nodes
    | throw (IO.userError (name ++ " exported certificate replay failed"))
  checkTest (name ++ " independent production checker accepts export")
    (decide (Certificate.Dependency.lookup facts result.target = some (.chiral .R)))

def main : IO Unit := do
  let some allene := admitSource? alleneSource | throw (IO.userError "allene admission failed")
  let alleneCarrier := allene.certified.localizedOccurrenceCarrier (carrierFuel allene)
  let internal := alleneCarrier.filter (isInternal allene)
  let terminal := alleneCarrier.filter (isEvenTerminal allene)
  IO.println s!"allene internal={internal.length}, even-terminal={terminal.length}"
  checkTest "nonempty internal cumulene routes omit with refusing callback" (selectedOmissions allene internal)
  checkTest "nonempty even-terminal routes omit with refusing callback" (selectedOmissions allene terminal)
  checkTarget "allene branch" allene
  let some ring := admitSource? ringSource | throw (IO.userError "ring admission failed")
  let ringCarrier := ring.certified.localizedOccurrenceCarrier (carrierFuel ring)
  let omitted := ringCarrier.filter (isOmittedRing ring)
  IO.println s!"ring permanent-omission={omitted.length}"
  checkTest "single-double-bond ring has no additional-double-bond closure route" omitted.isEmpty
  let atoms := List.finRange ring.certified.certified.input.molecule.atomCount
  let some left := atoms[4]? | throw (IO.userError "ring atom4 missing")
  let some right := atoms[5]? | throw (IO.userError "ring atom5 missing")
  let some policy := ring.certified.localizedMonocyclicDoubleBondPolicyAtExec? left right
    | throw (IO.userError "molecule-level monocycle policy missing")
  checkTest "whole-molecule ring policy independently requires permanent omission"
    (decide (policy.policy = .permanentlyOmit))
  checkTarget "ring branch" ring

-- Replay the complete readiness regression after the cached terminal-tie integration.
#eval main
end TetraStereo.Examples.LocalizedOmissionReadinessProbe
