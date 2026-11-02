import TetraStereo.OneCenter.LocalizedReferencePipeline
import TetraStereo.OneCenter.LocalizedRule3ShortCircuitSpatial

set_option autoImplicit false
namespace TetraStereo.Examples.LocalizedDieneReferenceProbe
open OneCenter OneCenter.CertifiedLocalizedCIPInput OneCenter.LocalizedReference

private def carbon : PeriodicElement := ⟨6, by decide, by decide⟩
private def hydrogen : PeriodicElement := ⟨1, by decide, by decide⟩
private def fluorine : PeriodicElement := ⟨9, by decide, by decide⟩
private def chlorine : PeriodicElement := ⟨17, by decide, by decide⟩
private def bromine : PeriodicElement := ⟨35, by decide, by decide⟩

private def bond (left right order : Nat) : SemanticInteraction :=
  { participants := [left, right], kind := .covalent order }

/-- Strict Br/Cl/F/C tetrahedral center attached to a planar diene. These are ordinary source data;
admission and all occurrence construction are performed at runtime. -/
def dieneSource : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := [carbon, fluorine, chlorine, bromine, carbon, carbon, carbon, carbon,
          fluorine, hydrogen, hydrogen, hydrogen, hydrogen].map (fun e => { element := e })
        interactions := [bond 0 1 1, bond 0 2 1, bond 0 3 1, bond 0 4 1,
          bond 4 5 2, bond 5 6 1, bond 6 7 2, bond 7 8 1,
          bond 4 9 1, bond 5 10 1, bond 6 11 1, bond 7 12 1] }
    spatial? := some { positions :=
      [{ x := 0, y := 1, z := 0 }, { x := 0, y := 2, z := 0 },
       { x := 0, y := 1, z := 1 }, { x := -1, y := 0, z := -1 },
       { x := 1, y := 0, z := 0 }, { x := 2, y := 0, z := 0 },
       { x := 3, y := 1, z := 0 }, { x := 4, y := 1, z := 0 },
       { x := 5, y := 2, z := 0 }, { x := 1, y := -1, z := 0 },
       { x := 2, y := -1, z := 0 }, { x := 3, y := 2, z := 0 },
       { x := 4, y := 0, z := 0 }] } }

def main : IO Unit := do
  let some input := admitSource? dieneSource | throw (IO.userError "diene admission failed")
  let fuel := carrierFuel input
  let some center := input.certified.canonicalTetrahedralCenters.find?
    (fun c => c.val.val == 0) | throw (IO.userError "central tetrahedral candidate absent")
  let target := input.certified.localizedFinalOccurrenceExecutable fuel center
  let carrier := input.certified.localizedOccurrenceCarrier fuel
  IO.println s!"diene admitted: {carrier.length} occurrences"
  for (left, right) in [(4, 5), (6, 7)] do
    let some cursor := carrier.find? fun item =>
      decide (item.val.root.val = 0 ∧ item.val.node.provenance = .realAtom) &&
        (item.val.node.current?.map (fun atom => atom.val) == some right) &&
        (item.val.node.parent?.map (fun atom => atom.val) == some left)
      | throw (IO.userError "double-bond occurrence missing")
    let some observed := input.certified.localizedRule3ShortCircuitSpatialUnitWithExec?
      target cursor (fun _ _ => none) (fun _ => none)
      | throw (IO.userError "strict endpoint geometry failed")
    IO.println s!"strict endpoint geometry {left}={right}: {repr observed.unit.core.geometry}"
  let engine := input.certified.tetrahedralSpatialDescriptorAt? center
    (fun _ => CIPRuleEngine.OfficialLigandRuleContext.empty)
  IO.println s!"existing constitutional engine central result: {repr engine}"
  let some base := input.certified.localizedNoDoubleFourLigandFrameExec? target
    | throw (IO.userError "central four-ligand frame absent")
  -- The full budget is deliberately not run in this diagnostic: two exploratory attempts were
  -- interrupted after more than two minutes. These are bounded frame observations, not a claim
  -- about the full original descriptor or the fixed-point state.
  for nestedFuel in [4, 16, 32] do
    let frame := input.certified.buildLocalizedDescriptorBearingRule3FrameExec?
      target (fun _ _ => none) nestedFuel base.cursors
    IO.println s!"original central frame at nested fuel {nestedFuel}: success={frame.isSome}"

#eval main
end TetraStereo.Examples.LocalizedDieneReferenceProbe
