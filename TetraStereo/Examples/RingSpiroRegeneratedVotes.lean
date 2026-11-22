import TetraStereo.Examples.RingSpiroReferenceSeparation

set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 50000
set_option Elab.async false

namespace TetraStereo.Examples.RingSpiroRegeneratedVotes
open OneCenter LocalizedGenericMarkedRecalculation RingSpiroReferenceSeparation

private abbrev root := canonicalCenterRoot 0
private abbrev fuel := comparatorFuel molecule

/-- The ordinary comparison call itself finds two tied pairs at the spiro carbon. -/
theorem ordinary_pairs : ordinary? molecule fuel [] root =
    some ([1,3,0,2], [some .eq,some .gt,some .eq]) := by decide +kernel

/-- Regenerate temporary auxiliary facts under the actual chosen atom,
rank the original frame with those facts and read its rational coordinates. -/
def trial? (g : Geometry) (mark : Nat) : Option (Nat × List Nat × RS) := do
  let regenerated := underWith molecule fuel g [] root
    (facts molecule fuel (structuralDepth molecule root)) mark
  let state ← appendFacts? [] regenerated
  let frame ← frameAtoms? molecule root
  let order ← rankedAtoms? frame (← marked? molecule fuel state root mark)
  return (state.length, order, ← readback? g order)

def expected (h : RS) : List (Nat × List Nat × RS) :=
  [(4,[2,4,1,3],h),(4,[2,4,1,3],h),(4,[4,2,3,1],h),(4,[4,2,3,1],h)]

theorem original_trials : [1,2,3,4].mapM (trial? geometry) = some (expected .R) := by decide +kernel
theorem reflected_trials : [1,2,3,4].mapM (trial? (mirror geometry)) = some (expected .S) := by decide +kernel

/-- Full recalculation at the three detected centers, including independent
regeneration on the reflected coordinates to determine the case. -/
theorem assignments : ([0,5,6].map fun c => assignCenter? molecule fuel geometry c) =
    List.replicate 3 (some (.chiral .R)) ∧
    ([0,5,6].map fun c => assignCenter? molecule fuel (mirror geometry) c) =
    List.replicate 3 (some (.chiral .S)) := by decide +kernel

end TetraStereo.Examples.RingSpiroRegeneratedVotes

assert_kernel_only TetraStereo.Examples.RingSpiroRegeneratedVotes.ordinary_pairs
assert_kernel_only TetraStereo.Examples.RingSpiroRegeneratedVotes.original_trials
assert_kernel_only TetraStereo.Examples.RingSpiroRegeneratedVotes.reflected_trials
assert_kernel_only TetraStereo.Examples.RingSpiroRegeneratedVotes.assignments
