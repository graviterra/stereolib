import TetraStereo.Engine.RingSpherePriority
import TetraStereo.Engine.RingNestedMagnitude

set_option autoImplicit false

namespace TetraStereo.Engine.RingSpherePriority
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site Arm molecularValues)
open RingNestedActivePair (Visit Reader consistent)
open RingSphereReadings (Profile unitRows lowerRows upperRows)

private theorem member_of_map {α β : Type} (f : α → Option β) {as : List α} {bs : List β}
    (hit : as.mapM f = some bs) {b} (inside : b ∈ bs) : ∃ a, f a = some b := by
  have all := TerminalTie.mapM_forall₂ _ _ _ hit
  clear hit
  induction all with
  | nil => contradiction
  | cons h _ ih =>
    rcases List.mem_cons.mp inside with rfl | hi
    · exact ⟨_,h⟩
    · exact ih hi

theorem profile_consistent {i : Input} {q : Arm i} {read p}
    (found : RingSpherePopulation.profile? i read q = some p) :
    ∀ v ∈ p.flatten, v.publication.all consistent = true := by
  intro v hv
  obtain ⟨row,member,inside⟩ := List.mem_flatten.mp hv
  obtain ⟨rs,hr⟩ := member_of_map (List.mapM (RingSpherePopulation.observe i read)) found member
  obtain ⟨t,ht⟩ := member_of_map _ hr inside
  obtain ⟨z,_,h⟩ := Option.bind_eq_some_iff.mp ht
  unfold RingNestedActivePair.visit at h
  obtain ⟨label,_,test⟩ := Option.bind_eq_some_iff.mp h
  split at test <;> try contradiction
  next ok =>
    obtain rfl := Option.some.inj test
    exact ok.1

private theorem projected {a b : Profile} {rev k} (found : RingSphereReadings.score? a b rev = some k) :
    RingNestedActivePair.projectedScore? a b rev = some k := by
  have result := RingSphereReadings.independent found
    (RingSphereReadings.canonical _) (RingSphereReadings.canonical _)
    (RingSphereReadings.canonical _) (RingSphereReadings.canonical _)
    (RingSphereReadings.canonical _) (RingSphereReadings.canonical _)
    (RingSphereReadings.canonical _) (RingSphereReadings.canonical _)
    (RingSphereReadings.canonical _) (RingSphereReadings.canonical _)
  rw [RingSphereReadings.upper_flatten,RingSphereReadings.upper_flatten] at result
  simp only [lowerRows,← List.map_flatten] at result
  exact result

/-- Every signed consensus is stable with magnitude one, tied on both
geometries, or sign-reversing with magnitude two. -/
theorem Certificate.signed_scores {i f a b read} (c : Certificate i f a b read) :
    c.score ∈ molecularValues :=
  RingNestedActivePair.projected_score_pair (profile_consistent c.leftRead) (profile_consistent c.rightRead)
    (projected c.actual) (projected c.reflected)

theorem edge_values {i f a b read s} (hit : edge? i f a b read = some s) : s ∈ molecularValues := by
  cases old : RingProximalUnit.edge? i f a b read with
  | none =>
    cases consensus : score? i f a b read with
    | none =>
      have grouped : RingGroupedStereo.score? i f a b read = some s := by simpa [edge?,old,consensus] using hit
      exact RingGroupedStereo.score_values grouped
    | some v =>
      obtain rfl : v = s := Option.some.inj (by simpa [edge?,old,consensus] using hit)
      obtain ⟨c,rfl⟩ := score_source consensus
      exact c.signed_scores
  | some v =>
    have eqn : v = s := Option.some.inj ((preserves old).symm.trans hit)
    subst v
    unfold RingProximalUnit.edge? at old
    split at old
    · rename_i c _
      obtain rfl := Option.some.inj old
      unfold RingProximalUnit.value
      split <;> decide
    · obtain ⟨c,_,rfl⟩ := Option.map_eq_some_iff.mp old
      exact c.property.signed_scores

end TetraStereo.Engine.RingSpherePriority

assert_kernel_only TetraStereo.Engine.RingSpherePriority.profile_consistent
assert_kernel_only TetraStereo.Engine.RingSpherePriority.Certificate.signed_scores
assert_kernel_only TetraStereo.Engine.RingSpherePriority.edge_values
