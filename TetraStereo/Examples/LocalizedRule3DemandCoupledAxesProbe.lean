import TetraStereo.OneCenter.LocalizedRule3DemandRankProducer
import TetraStereo.OneCenter.LocalizedFamilyReferencePipeline

set_option autoImplicit false
namespace TetraStereo.Examples.LocalizedRule3DemandCoupledAxesProbe
open OneCenter OneCenter.CertifiedLocalizedCIPInput OneCenter.LocalizedShortCircuit

private def cursorId {input : Input} (cursor : input.certified.LocalizedRerootCursor (carrierFuel input)) : String :=
  s!"occ={repr cursor.occurrence.val}; previous={repr (cursor.previous?.map Subtype.val)}"

private def routeName {input : Input}
    (cursor : input.certified.LocalizedRerootCursor (carrierFuel input)) : String :=
  if (input.certified.localizedRule3OrdinaryRouteCertificate? cursor.occurrence).isSome then
    "ordinary-short"
  else if ¬ input.certified.LocalizedOccurrenceHasRule3DoubleBondEdge cursor.occurrence then "structural"
  else match input.certified.localizedRule3CumulatedAxisEntryExec? cursor.occurrence with
    | none => "axis-entry-refused"
    | some (.internal _ _) => "internal-omission"
    | some (.branched _ _ _ _) => "branched-original"
    | some (.ringClosure _ _) => "ring-closure"
    | some (.terminalStart _) =>
      match input.certified.localizedRule3CumulatedEndpointCursorFrameExec?
          (input.certified.localizedRule3CumulatedTraversalFuel (carrierFuel input)) cursor.occurrence with
      | none => "terminal-topology-refused"
      | some axis => if Odd axis.doubleBondCount then "odd-terminal-original" else "even-terminal-omission"

/-- Diagnostic graph traversal only, called after production discovery reports a cycle.
It records actual successor edges and the repeated active-path cursor; it does not evaluate keys. -/
private def cycleTrace (input : Input) : Nat →
    List (input.certified.LocalizedRerootCursor (carrierFuel input)) →
    List (input.certified.LocalizedRerootCursor (carrierFuel input)) →
    input.certified.LocalizedRerootCursor (carrierFuel input) →
    Except (List (input.certified.LocalizedRerootCursor (carrierFuel input)))
      (List (input.certified.LocalizedRerootCursor (carrierFuel input)))
  | 0, _, finished, _ => .ok finished
  | remaining + 1, active, finished, cursor =>
      if cursor ∈ finished then .ok finished
      else if cursor ∈ active then
        .error ([cursor] ++ (active.takeWhile (fun other => decide (other ≠ cursor))).reverse ++ [cursor])
      else do
        let completed ← (input.certified.rule3DemandSuccessors cursor).foldlM
          (fun done next => cycleTrace input remaining (cursor :: active) done next) finished
        pure (cursor :: completed)

private def printTrace (input : Input)
    (path : List (input.certified.LocalizedRerootCursor (carrierFuel input))) : IO Unit := do
  for cursor in path do IO.println s!"  cycle vertex route={routeName cursor}; {cursorId cursor}"
  for pair in path.zip path.tail do
    let isChild := decide (pair.2 ∈ input.certified.executableLocalizedRerootChildren pair.1)
    let isCallback := decide (pair.2 ∈ (input.certified.rule3NodeCallbackRequests pair.1.occurrence).flatten)
    IO.println s!"  cycle edge child={isChild}, callback={isCallback}"

private def runSource (name : String) (source : AuthoritativeChemicalInput) : IO Unit := do
  let start ← IO.monoMsNow
  let some input := admitSource? source | throw (IO.userError s!"{name}: admission failed")
  let bonds := Families.canonicalDoubleBonds input
  if bonds.isEmpty then throw (IO.userError s!"{name}: no physical double bonds")
  IO.println s!"SOURCE {name}: atoms={input.molecule.atomCount}, bonds={bonds.length}"
  for bond in bonds do
    let occurrence := input.certified.localizedCanonicalDoubleBondFirstChildOccurrenceExec (carrierFuel input) bond
    let cursor : input.certified.LocalizedRerootCursor (carrierFuel input) := { occurrence }
    IO.println s!"ROOT bond=({bond.val.1.val},{bond.val.2.val}), route={routeName cursor}; {cursorId cursor}"
    match input.certified.prepareRule3DemandPlan [cursor] with
    | .ok plan =>
      let demands := plan.ranks.vertices.filter (fun item => !(input.certified.rule3NodeCallbackRequests item.occurrence).isEmpty)
      let count := demands.foldl (fun n item => n + (input.certified.rule3NodeCallbackRequests item.occurrence).length) 0
      IO.println s!"PLAN success vertices={plan.ranks.vertices.length}, callbackVertices={demands.length}, requests={count}, bound={plan.bound}"
      for demanding in demands.take 8 do
        IO.println s!"  demand route={routeName demanding}; {cursorId demanding}"
        for request in input.certified.rule3NodeCallbackRequests demanding.occurrence do
          IO.println s!"    request={repr (request.map cursorId)}"
    | .error (.cycle repeated) =>
      IO.println s!"PLAN cycle repeated={cursorId repeated}, route={routeName repeated}"
      let n := (input.certified.localizedOccurrenceCarrier (carrierFuel input)).length
      match cycleTrace input (n * (n + 1) + 1) [] [] cursor with
      | .error path => printTrace input path
      | .ok _ => throw (IO.userError "production cycle not reproduced by diagnostic traversal")
    | .error .traversalLimit => IO.println "PLAN traversalLimit"
    | .error .invalidRanks => throw (IO.userError "PLAN invalidRanks")
    | .error .missingRoot => throw (IO.userError "PLAN missingRoot")
  let finish ← IO.monoMsNow
  IO.println s!"TIMING {name}: {finish - start}ms"

/-- Two open odd cumulene axes joined by one single bond. All valences are explicit;
coordinates are intentionally absent because this probe inspects only demand topology. -/
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
          bond 0 8 1, bond 0 9 1, bond 7 10 1, bond 7 11 1, bond 3 12 1, bond 4 13 1] } }

def main : IO Unit := do
  runSource "linked-odd-cumulenes" source

#eval main
end TetraStereo.Examples.LocalizedRule3DemandCoupledAxesProbe
