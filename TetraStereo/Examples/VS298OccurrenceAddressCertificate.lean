import TetraStereo.Examples.VS298OccurrenceCertificate

set_option autoImplicit false

namespace TetraStereo.Examples.VS298

open OneCenter
open OneCenter.ProductionCIPOccurrenceDiscovery

def branchKey (slot : Fin 4) : RawMolecule.CanonicalBranchKey :=
  (centerDiscovery.branch slot).key

theorem branchKey_accepted (slot : Fin 4) :
    branchCanonicalKey? molecule centerOne.val (ligandAtom root slot) =
      some (branchKey slot) :=
  (centerDiscovery.branch slot).accepted

theorem branchKey_complete (slot : Fin 4) : (branchKey slot).complete = true :=
  (centerDiscovery.branch slot).complete

def ligandFourSlot : Fin 4 := 2

theorem ligandFourSlot_spec : ligandAtom root ligandFourSlot = 4 := by decide

end TetraStereo.Examples.VS298
