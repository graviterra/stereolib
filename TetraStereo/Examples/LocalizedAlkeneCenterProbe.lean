import TetraStereo.OneCenter.LocalizedEngineBridge

set_option autoImplicit false
namespace TetraStereo.Examples.LocalizedAlkeneCenterProbe
open OneCenter OneCenter.LocalizedReference

private def carbon : PeriodicElement := ⟨6, by decide, by decide⟩
private def hydrogen : PeriodicElement := ⟨1, by decide, by decide⟩
private def fluorine : PeriodicElement := ⟨9, by decide, by decide⟩
private def chlorine : PeriodicElement := ⟨17, by decide, by decide⟩
private def bromine : PeriodicElement := ⟨35, by decide, by decide⟩
private def bond (left right order : Nat) : SemanticInteraction :=
  { participants := [left, right], kind := .covalent order }

/-- F/Cl/Br tetrahedral carbon attached to CH=CHF, with exact nondegenerate geometry. -/
def source : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := [carbon, fluorine, chlorine, bromine, carbon, carbon, fluorine,
          hydrogen, hydrogen].map (fun e => { element := e })
        interactions := [bond 0 1 1, bond 0 2 1, bond 0 3 1, bond 0 4 1,
          bond 4 5 2, bond 5 6 1, bond 4 7 1, bond 5 8 1] }
    spatial? := some { positions :=
      [{ x := 0, y := 1, z := 0 }, { x := 0, y := 2, z := 0 },
       { x := 0, y := 1, z := 1 }, { x := -1, y := 0, z := -1 },
       { x := 1, y := 0, z := 0 }, { x := 2, y := 0, z := 0 },
       { x := 3, y := 1, z := 0 }, { x := 1, y := -1, z := 0 },
       { x := 2, y := -1, z := 0 }] } }

private def checkAssertion (name : String) (condition : Bool) : IO Unit :=
  if condition then IO.println ("ok: " ++ name)
  else throw (IO.userError ("failed: " ++ name))

def main : IO Unit := do
  let some input := admitSource? source | throw (IO.userError "alkene center admission failed")
  let proposed := EngineBridge.propose input
  let result := evaluate input proposed
  let observed := report input result.facts
  IO.println s!"tetrahedral center attached to alkene: {repr observed}"
  IO.println s!"existing engine certificate accepted: {(checkProposals? input proposed).isSome}"
  checkAssertion "alkene-bearing source yields tetrahedral R"
    (decide (observed = [(0, some (.chiral .R))]))
  checkAssertion "returned full-domain certificate replays"
    ((checkProposals? input result.nodes).isSome)

#eval main
end TetraStereo.Examples.LocalizedAlkeneCenterProbe
