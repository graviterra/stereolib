import TetraStereo.Examples.BlueBookHexachlorocyclohexaneConstitution
import TetraStereo.Engine.RingRecursivePriorities

set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
namespace TetraStereo.Examples.BlueBookHexachlorocyclohexane
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation Engine.RingChemicalPriority Recursive

/-- Reverse the original cycle about the named carbon, carrying each
chlorine and hydrogen with the carbon to which it is bonded. -/
def exchange (i a : Nat) := 6*(a/6) + (2*i + 6 - a%6)%6

def hints : List Nat → Option Recursive.Frame
  | [i] => some ⟨.fourB,i+6,(i+1)%6,(i+5)%6,i+12,exchange i,false⟩
  | _ => none

def radius (path : List Nat) := if path.length = 1 then 0 else 7 - path.length

def atRoot (g : Geometry) (i : Nat) : Option Reading :=
  (certifyHalogenated molecule g hints radius 2 [i]).map Subtype.val

/-- Transport the constitutional result to any nondegenerate geometry that
realizes this local hand. -/
theorem auxiliary_of_geometry (g : Geometry) (i : Fin 6) (cw : Bool) (k : Fin 5) (r : Reading)
    (read : geometric g (order i cw k) (order i cw k) = some r) :
    Supported molecule g (path i cw k) r := by
  obtain ⟨ranking,h⟩ := branch_order i cw k
  exact .ranked ranking (h ▸ read)

end TetraStereo.Examples.BlueBookHexachlorocyclohexane
assert_kernel_only TetraStereo.Examples.BlueBookHexachlorocyclohexane.auxiliary_of_geometry
