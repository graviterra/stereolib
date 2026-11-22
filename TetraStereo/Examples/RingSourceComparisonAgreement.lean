import TetraStereo.Engine.PublicAPI

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 50000
set_option Elab.async false

namespace TetraStereo.Examples.RingSourceComparisonAgreement
open OneCenter Engine Engine.CentresRing CentresRingSpiroCasing

private def layout : Molecular.Layout := renumberedLayouts[3]'(by decide)
private def geometry (i : Nat) := moved.positions[i]?
private abbrev mol := CentresRingSpiroCasing.renumbered

/-- Inspect the actual chronological call, including its mark and visible
publications. The input layout supplies discovery and carrier order only. -/
def checkIndex (n : Nat) : Bool := (do
  let d ← Molecular.derive mol geometry layout
  let c ← d.calls[n]?
  let _ ← ComparisonAgreement.checkCall? mol geometry 3 2 c
  return ()).isSome

theorem call_count : (Molecular.derive mol geometry layout).map (·.calls.length) = some 39 := by
  decide +kernel

/-- Both labels are computed from the input molecule. The first is the
release sort's readout; the second uses the actual and reflected priorities. -/
def labels : Option (String × String) := do
  let d ← Molecular.derive mol geometry layout
  let c ← deriveRingReferenceOccurrence? mol geometry 2 mol.atomCount [3]
  return (d.trace.label,labelCode (c.verdict.bind RingChemicalPriority.Recursive.Reading.label))

theorem casing : labels = some ("s","S") := by decide +kernel

/-- Check each of the 39 cells separately to bound the kernel working set. -/
theorem all_calls (n : Fin 39) : checkIndex n.val = true := by
  fin_cases n <;> decide +kernel

/-- Every comparison call in the actual derivation has a signed molecular
justification, even though the release reports the wrong case at the root. -/
theorem every_comparison {d : Molecular.Derivation mol geometry}
    (ran : Molecular.derive mol geometry layout = some d)
    {n : Nat} {c : Molecular.Call} (found : d.calls[n]? = some c) :
    Nonempty (ComparisonAgreement.Agreement mol geometry 3 c) := by
  have size : d.calls.length = 39 := by simpa [ran] using call_count
  have lt : n < 39 := by simpa [size] using (List.getElem?_eq_some_iff.mp found).1
  have checked := all_calls ⟨n,lt⟩
  cases ok : ComparisonAgreement.checkCall? mol geometry 3 2 c with
  | none => simp [checkIndex,ran,found,ok] at checked
  | some proof => exact ⟨proof⟩

def checkPublication (n : Nat) : Bool := (do
  let d ← Molecular.derive mol geometry layout
  let u ← d.trace.updates[n]?
  let _ ← ComparisonAgreement.checkAuxiliary? mol geometry d.trace 2 u
  return ()).isSome

theorem publication_count :
    (Molecular.derive mol geometry layout).map (·.trace.updates.length) = some 8 := by decide +kernel

theorem all_publications (n : Fin 8) : checkPublication n.val = true := by
  fin_cases n <;> decide +kernel

/-- Each source update carries the correct value at its own discovery path. -/
theorem every_publication {d : Molecular.Derivation mol geometry}
    (ran : Molecular.derive mol geometry layout = some d)
    {n : Nat} {u : Update} (found : d.trace.updates[n]? = some u) :
    Nonempty (ComparisonAgreement.Auxiliary mol geometry d.trace u) := by
  have size : d.trace.updates.length = 8 := by simpa [ran] using publication_count
  have lt : n < 8 := by simpa [size] using (List.getElem?_eq_some_iff.mp found).1
  have checked := all_publications ⟨n,lt⟩
  cases ok : ComparisonAgreement.checkAuxiliary? mol geometry d.trace 2 u with
  | none => simp [checkPublication,ran,found,ok] at checked
  | some proof => exact ⟨proof⟩

end TetraStereo.Examples.RingSourceComparisonAgreement

assert_kernel_only TetraStereo.Examples.RingSourceComparisonAgreement.every_comparison
assert_kernel_only TetraStereo.Examples.RingSourceComparisonAgreement.casing
assert_kernel_only TetraStereo.Examples.RingSourceComparisonAgreement.every_publication
