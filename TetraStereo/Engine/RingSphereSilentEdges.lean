import TetraStereo.Engine.RingSphereSilentCoverage
import TetraStereo.Engine.RingSpherePublication

set_option autoImplicit false

namespace TetraStereo.Engine.RingSphereCoverage
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader Eligible masked)
open RingRetainedChemicalTrace (Reaches compareAt?)

/-- Every existing retained comparison gives the same two signed readings
when the independent sphere certificate applies to the same occurrences. -/
theorem retained_agrees {i f a b read s} (c : RingSpherePriority.Certificate i f a b read)
    (old : RingNestedActivePair.Edge i f a b read s) : s = c.score := by
  cases old with
  | below p ht | above p ht =>
    obtain rfl := Option.some.inj (p.symm.trans c.prior)
    exact nomatch ht.symm.trans c.tied
  | stereo p =>
    apply Prod.ext
    · exact Option.some.inj (p.actual.symm.trans (c.agrees p.leftRead p.rightRead false))
    · exact Option.some.inj (p.reflected.symm.trans (c.agrees p.leftRead p.rightRead true))

/-- A known empty head rules out a strict comparison of two *positive*
proximal unit classes. All earlier retained results agree with the certificate. -/
theorem empty_head_edge {i f a b read k} (head : read a = some none)
    (found : RingSpherePriority.score? i f a b read = some k) : RingSpherePriority.edge? i f a b read = some k := by
  obtain ⟨c,ck⟩ := RingSpherePriority.score_source found
  have miss : RingProximalUnit.first? i f a b read = none := by
    cases h : RingProximalUnit.first? i f a b read with
    | none => rfl
    | some cert =>
      have empty := Option.some.inj (cert.leftRead.symm.trans head)
      have pos := cert.available.1
      rw [empty] at pos
      contradiction
  unfold RingSpherePriority.edge? RingProximalUnit.edge?
  rw [miss]
  cases h : RingNestedActivePair.edge? i f a b read with
  | none => simp [found]
  | some s => exact congrArg some ((retained_agrees c s.property).trans ck)

/-- A structural test on the full addressed molecular components. Only
eligible deeper occurrences can contribute an auxiliary descriptor. -/
def NoVisibleCenter (i : Input) (f : Site i) (q : Arm i) : Prop :=
  ∀ t, Reaches i q t → Eligible f t.occurrence →
    ∀ c, ¬i.certified.RealTetrahedralCenterNode t.occurrence.val.node c

theorem structural_silence {i : Input} {f : Site i} {q : Arm i}
    (on : q.occurrence.val.root = f.val.root) (h : NoVisibleCenter i f q) :
    ∀ t, Reaches i q t → masked f (RingSpherePublication.atRoot i f.val.root) t.occurrence = some none := by
  intro t path
  have same := (RingFrontierProfileShape.reaches_root path).trans on
  by_cases visible : Eligible f t.occurrence
  · have absent := (RingRetainedAuxiliary.absence_iff i t.occurrence).mpr (h t path visible)
    have previous (read : Reader i) : RingClosedGroupTie.publish? i t.occurrence read = some none := by
      simp [RingClosedGroupTie.publish?,RingClosedPairAssignment.publish?,RingNestedActivePair.publish?,absent]
    simp only [masked,same,ne_eq,not_true_eq_false,if_false,visible,if_true]
    rw [RingSpherePublication.atRoot_eq same]
    exact RingSpherePublication.preserves (previous _)
  · simp [masked,same,visible]

end TetraStereo.Engine.RingSphereCoverage

assert_kernel_only TetraStereo.Engine.RingSphereCoverage.retained_agrees
assert_kernel_only TetraStereo.Engine.RingSphereCoverage.empty_head_edge
assert_kernel_only TetraStereo.Engine.RingSphereCoverage.structural_silence
