import TetraStereo.OneCenter.LocalizedReferenceInput
import TetraStereo.OneCenter.LocalizedCyclicCumulenePerceptionExecutable

set_option autoImplicit false
namespace TetraStereo.Examples.LocalizedPerceptionExecutableProbe
open OneCenter OneCenter.LocalizedReference

private def carbon : PeriodicElement := ⟨6, by decide, by decide⟩
private def bond (left right order : Nat) : SemanticInteraction :=
  { participants := [left, right], kind := .covalent order }

def source (allDouble pendant : Bool) : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := List.replicate (if pendant then 4 else 3) { element := carbon }
        interactions := [bond 0 1 2, bond 1 2 (if allDouble then 2 else 1),
          bond 2 0 (if allDouble then 2 else 1)] ++
          (if pendant then [bond 2 3 1] else []) } }

private def checkAssertion (name : String) (condition : Bool) : IO Unit :=
  if condition then IO.println ("ok: " ++ name)
  else throw (IO.userError ("failed: " ++ name))

def main : IO Unit := do
  for (allDouble, pendant) in [(false, false), (false, true), (true, false)] do
    let some admitted := admitSource? (source allDouble pendant)
      | throw (IO.userError "ring source rejected")
    let input := admitted.certified
    let atoms := (Finset.univ : Finset input.Atom).sort (· ≤ ·)
    let some left := atoms[0]? | throw (IO.userError "atom 0 absent")
    let some right := atoms[1]? | throw (IO.userError "atom 1 absent")
    checkAssertion "pruned core retains exactly triangle vertices"
      (input.localizedCycleCore.card == 3)
    checkAssertion "reachable component includes every pendant atom"
      ((input.localizedCovalentComponentAtomsExec left).card == atoms.length)
    checkAssertion "one declarative cycle survives complete pruned search"
      ((input.localizedSimpleCycleVertexSetsInComponentExec left).card == 1)
    checkAssertion "ordinary monocycle excludes all-double cycle"
      ((input.localizedMonocyclicDoubleBondAtExec? left right).isSome == !allDouble)
    checkAssertion "cyclic cumulene finds exactly all-double component"
      (input.localizedCyclicCumuleneComponentsExec.length == if allDouble then 1 else 0)
    checkAssertion "cyclic component containing atom agrees"
      ((input.localizedCyclicCumuleneComponentContainingExec? left).isSome == allDouble)

#eval main
end TetraStereo.Examples.LocalizedPerceptionExecutableProbe
