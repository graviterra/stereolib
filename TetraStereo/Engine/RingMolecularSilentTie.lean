import TetraStereo.Engine.RingSphereSilentEdges
import TetraStereo.Engine.RingSphereKeyShape

set_option autoImplicit false

namespace TetraStereo.Engine.RingSphereCoverage
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader masked)
open RingRetainedChemicalTrace (Reaches compareAt?)

/-- Equality of the constitutional keys supplies both population alignments.
The only stereo premise is an actual known absence at each reachable cell. -/
theorem silent_tie {i : Input} {f a b : Site i} {read : Reader i} {t}
    (prior : compareAt? i f a b = some t) (tie : cipTraceOutcome t = .eq)
    (left : ∀ q, Reaches i (⟨a,some f⟩ : Arm i) q → read q.occurrence = some none)
    (right : ∀ q, Reaches i (⟨b,some f⟩ : Arm i) q → read q.occurrence = some none) :
    RingSpherePriority.edge? i f a b read = some (0,0) := by
  have inc := (RingRetainedChemicalTrace.compareAt?_source prior).1
  have valid (q : Site i) (adj : i.certified.LocalizedCarrierTreeAdjacent q.val f.val) :
      i.certified.LocalizedRerootCursorValid (⟨q,some f⟩ : Arm i) :=
    (i.certified.mem_localizedRerootNeighborFrames_iff _ _).mpr ⟨q.property,adj⟩
  obtain ⟨l,hl,ls⟩ := silent_profile (valid a inc.2.2.1) left
  obtain ⟨r,hr,rs⟩ := silent_profile (valid b inc.2.2.2) right
  obtain ⟨widths,queue⟩ := RingSphereKeyShape.tie_shape prior tie hl hr
  exact empty_head_edge (left _ .here) (silent_molecular prior tie hl hr widths queue ls rs)

/-- No auxiliary reader, seed, depth bound, ordering, or score is supplied.
For this graph-defined class the public molecular comparison always returns
the exact tie in both spatial presentations, even with nested sibling ties. -/
theorem structural_edge {i : Input} {f a b : Site i} {t}
    (prior : compareAt? i f a b = some t) (tie : cipTraceOutcome t = .eq)
    (left : NoVisibleCenter i f ⟨a,some f⟩) (right : NoVisibleCenter i f ⟨b,some f⟩) :
    RingSpherePriority.edge? i f a b (masked f (RingSpherePublication.atRoot i f.val.root)) = some (0,0) := by
  have inc := (RingRetainedChemicalTrace.compareAt?_source prior).1
  exact silent_tie prior tie (structural_silence inc.2.2.1.1 left) (structural_silence inc.2.2.2.1 right)

/-- At the first unresolved cell, both profiles and both population equalities
are obtained from the molecule. Only the descriptor-stage consensus remains. -/
theorem frontier_consensus {i : Input} {root : i.certified.Atom} {f a b : Site i} {t}
    (listed : f ∈ RingMolecularSchedule.frontier i root) (prior : compareAt? i f a b = some t)
    (tie : cipTraceOutcome t = .eq) :
    let read := masked f (RingMolecularSchedule.atRoot i root)
    ∃ l r, RingSpherePopulation.profile? i read ⟨a,some f⟩ = some l ∧
      RingSpherePopulation.profile? i read ⟨b,some f⟩ = some r ∧ ∀ k : Int × Int,
      RingSpherePriority.score? i f a b read = some k ↔ Agrees l r false k.1 ∧ Agrees l r true k.2 := by
  obtain ⟨l,r,hl,hr,iff⟩ := frontier listed prior tie
  obtain ⟨widths,queue⟩ := RingSphereKeyShape.tie_shape prior tie hl hr
  exact ⟨l,r,hl,hr,fun k => by rw [iff k]; simp only [widths,queue,true_and]⟩

end TetraStereo.Engine.RingSphereCoverage

assert_kernel_only TetraStereo.Engine.RingSphereCoverage.silent_tie
assert_kernel_only TetraStereo.Engine.RingSphereCoverage.structural_edge
assert_kernel_only TetraStereo.Engine.RingSphereCoverage.frontier_consensus
