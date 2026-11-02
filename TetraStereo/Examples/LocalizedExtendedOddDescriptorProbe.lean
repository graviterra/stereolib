import TetraStereo.OneCenter.LocalizedExtendedShortCircuitEngineBridge

set_option autoImplicit false
namespace TetraStereo.Examples.LocalizedExtendedOddDescriptorProbe
open OneCenter OneCenter.CertifiedLocalizedCIPInput OneCenter.LocalizedExtendedShortCircuit

/-- Explicit tetrahedral center attached to an odd three-double-bond axis.
The senior axis substituents have exact sequence-cis geometry. At center0 the ordered
Br/Cl/F/C ligand points have positive oriented volume3, independently fixing R. -/
def source : AuthoritativeChemicalInput :=
  let carbon : PeriodicElement := ⟨6, by decide, by decide⟩
  let hydrogen : PeriodicElement := ⟨1, by decide, by decide⟩
  let fluorine : PeriodicElement := ⟨9, by decide, by decide⟩
  let chlorine : PeriodicElement := ⟨17, by decide, by decide⟩
  let bromine : PeriodicElement := ⟨35, by decide, by decide⟩
  let bond (a b order : Nat) : SemanticInteraction :=
    { participants := [a, b], kind := .covalent order }
  { molecule :=
      { atoms := (List.replicate 5 carbon ++ [fluorine, chlorine, bromine, fluorine, hydrogen, hydrogen]).map
          fun element => { element }
        interactions := [bond 0 1 1, bond 1 2 2, bond 2 3 2, bond 3 4 2,
          bond 0 5 1, bond 0 6 1, bond 0 7 1, bond 4 8 1, bond 4 9 1, bond 1 10 1] }
    spatial? := some { positions :=
      [{ x := 0, y := 1, z := 0 }, { x := 0, y := 0, z := 0 },
       { x := 1, y := 0, z := 0 }, { x := 2, y := 0, z := 0 },
       { x := 3, y := 0, z := 0 }, { x := 1, y := 1, z := 0 },
       { x := 0, y := 1, z := 1 }, { x := -1, y := 1, z := -1 },
       { x := 3, y := 1, z := 0 }, { x := 3, y := -1, z := 0 },
       { x := 0, y := -1, z := 0 }] } }

private def checkTest (name : String) (condition : Bool) : IO Unit :=
  if condition then IO.println ("ok: " ++ name)
  else throw (IO.userError ("failed: " ++ name))

def main : IO Unit := do
  let started ← IO.monoMsNow
  let some input := admitSource? source | throw (IO.userError "odd-axis tetrahedron rejected")
  let centers := input.certified.canonicalTetrahedralCenters
  checkTest "odd-axis fixture has precisely center0" (decide (centers.map (fun c => c.val.val) = [0]))
  let some center := centers.head? | throw (IO.userError "center absent")
  let target := input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center
  let view : input.certified.LocalizedDependencyView target := fun _ _ => none
  let cache := Cached.buildRuntimeCache input
  checkTest "odd-axis carrier constructs its no-callback evidence" cache.ready?.isSome
  let scanned ← IO.monoMsNow
  IO.println s!"TIMING odd descriptor cache: {scanned - started}ms; carrier={cache.carrier.length}"
  let readChildren := input.certified.localizedRerootChildrenFromCarrier? cache.carrier
  let some evidence := ExtendedBounded.spatialEvidence? input.certified readChildren target view
    | throw (IO.userError "bounded odd-axis tetrahedral evidence refused")
  checkTest "extended frame has all four raw and rebuilt ligand keys"
    (evidence.keys.rule3Frame.rawKeys.length == 4 && evidence.keys.rule3Frame.keys.length == 4)
  let observations := evidence.keys.rule3Frame.keys.flatMap fun key =>
    key.observations.flatMap fun layer => layer.map fun entry => entry.2.unit.geometry
  checkTest "tetrahedral comparison frame retains actual odd-axis sequence-cis geometry"
    (decide (.seqcis ∈ observations))
  checkTest "independent exact ordered geometry yields R"
    (decide (descriptorOfPriorityOrderedPoints? evidence.points = some .R))
  checkTest "all four ligands are strictly ordered with zero pseudo comparisons"
    (evidence.tracked.highestFirst.length == 4 && evidence.tracked.pseudoComparisons == 0)
  checkTest "cached extended descriptor emits R"
    (decide (Cached.evaluatorUsingCache input cache target view = some (.chiral .R)))
  let localDone ← IO.monoMsNow
  IO.println s!"TIMING odd descriptor local evidence: {localDone - scanned}ms"
  let result := Cached.referenceUsingCache input cache
  checkTest "full reference certificate reports center0 R"
    (decide (report input result.facts = [(0, some (.chiral .R))]))
  checkTest "full reference certificate includes every carrier occurrence"
    (result.nodes.length == cache.carrier.length)
  let produced ← IO.monoMsNow
  IO.println s!"TIMING odd descriptor reference: {produced - localDone}ms; nodes={result.nodes.length}"
  let some replay := Cached.checkUsingCache? input cache result.nodes
    | throw (IO.userError "odd-axis generated certificate rejected")
  checkTest "independent replay reproduces complete reference facts" (decide (replay = result.facts))
  checkTest "truncated odd-axis certificate is rejected"
    (Cached.checkUsingCache? input cache (result.nodes.drop 1)).isNone
  let finished ← IO.monoMsNow
  IO.println s!"TIMING odd descriptor complete: {finished - started}ms"

#eval main
end TetraStereo.Examples.LocalizedExtendedOddDescriptorProbe
