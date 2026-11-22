import TetraStereo.Engine.RingDiscoveredPriority
import TetraStereo.OneCenter.LocalizedMarkedTerminalGaugeSwap

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority.DiscoveredPriority
open OneCenter Recursive LocalizedGenericMarkedRecalculation LocalizedMarkedTerminalGaugeSwap

/-- The constitutional frame fixes the two atoms of the exchanged pair
and a permutation of four distinct ligands. -/
theorem Order.pair_present {m p d f w} (o : @Order m p d f w) :
    o.ligands.Nodup ∧ o.ligands.length = 4 ∧ f.left.ligand ∈ o.ligands ∧ f.right.ligand ∈ o.ligands := by
  have perm := o.complete.map (SignedPair.Row.ligand)
  exact ⟨perm.nodup_iff.mpr f.distinct,by simpa [Order.ligands] using o.complete.length_eq.trans f.four,
    perm.mem_iff.mpr (List.mem_map_of_mem f.leftMem),perm.mem_iff.mpr (List.mem_map_of_mem f.rightMem)⟩

theorem Step.same_order {m p ls rs} (s : Step m p ls rs) (same : s.actualWins = s.reflectedWins) :
    s.reflected.ligands = s.actual.ligands := by simpa only [if_pos same] using s.transport

theorem Step.exchanged_order {m p ls rs} (s : Step m p ls rs) (opposite : s.actualWins ≠ s.reflectedWins) :
    s.reflected.ligands = s.actual.ligands.map (swapAtom s.frame.left.ligand s.frame.right.ligand) := by
  simpa only [if_neg opposite,exchange,swapAtom] using s.transport

/-- The first physical hand and the two molecular winning directions determine
the complete mirror reading, including simultaneous refusal on missing or
degenerate coordinates. -/
theorem Step.mirror_readback {m p ls rs} (s : Step m p ls rs) (g : Geometry) :
    readback? (mirror g) s.reflected.ligands =
      (readback? g s.actual.ligands).map (fun h => if s.actualWins = s.reflectedWins then h.swap else h) := by
  by_cases same : s.actualWins = s.reflectedWins
  · simp only [s.same_order same,if_pos same,readback_mirror]
  · obtain ⟨nodup,len,left,right⟩ := s.actual.pair_present
    rw [s.exchanged_order same,readback_mirror,
      readback_swapAtom g _ _ s.frame.different _ nodup len left right]
    cases readback? g s.actual.ligands with
    | none => rfl
    | some hand => cases hand <;> simp [same,RS.swap]

theorem Step.geometric_of_raw {m p ls rs} (s : Step m p ls rs) {g : Geometry} {h : RS}
    (raw : readback? g s.actual.ligands = some h) :
    geometric g s.actual.ligands s.reflected.ligands =
      some ⟨h,if s.actualWins = s.reflectedWins then h.swap else h⟩ := by
  simp [geometric,s.mirror_readback,raw]

theorem Step.hands {m p ls rs} (s : Step m p ls rs) {g : Geometry} {r : Reading}
    (computed : geometric g s.actual.ligands s.reflected.ligands = some r) :
    readback? g s.actual.ligands = some r.actual ∧
      r.reflected = (if s.actualWins = s.reflectedWins then r.actual.swap else r.actual) := by
  cases raw : readback? g s.actual.ligands with
  | none => simp [geometric,raw] at computed
  | some hand =>
    have eqn := Option.some.inj ((s.geometric_of_raw raw).symm.trans computed)
    subst r
    exact ⟨rfl,rfl⟩

theorem Step.uppercase_of_same {m p ls rs} (s : Step m p ls rs) {g : Geometry} {r : Reading}
    (same : s.actualWins = s.reflectedWins)
    (computed : geometric g s.actual.ligands s.reflected.ligands = some r) :
    r.reflected = r.actual.swap ∧ r.label = some (.chiral r.actual) := by
  have h : r.reflected = r.actual.swap := by simpa only [if_pos same] using (s.hands computed).2
  exact ⟨h,by simpa only [Reading.label,h] using caseFromMirror?_eq_swap r.actual⟩

theorem Step.lowercase_of_opposite {m p ls rs} (s : Step m p ls rs) {g : Geometry} {r : Reading}
    (different : s.actualWins ≠ s.reflectedWins)
    (computed : geometric g s.actual.ligands s.reflected.ligands = some r) :
    r.reflected = r.actual ∧ r.label = some (.pseudoasymmetric (pseudoRSOfRS r.actual)) := by
  have h : r.reflected = r.actual := by simpa only [if_neg different] using (s.hands computed).2
  exact ⟨h,by simpa only [Reading.label,h] using caseFromMirror?_eq_same r.actual⟩

/-- The basis records the independently checked strict comparison. Only a
Rule 5 decision exchanges the winning direction on reflection. -/
def Basis.five {m p d f ls rs w v} : @Basis m p d f ls rs w v → Bool
  | .classes _ => false
  | .stereo s _ _ _ _ => s == .five

theorem Basis.same_iff {m p d f ls rs w v} (b : @Basis m p d f ls rs w v) :
    w = v ↔ b.five = false := by
  cases b with
  | classes => simp [Basis.five]
  | stereo s w prior a r => cases s <;> cases w <;> simp [Basis.five,mirrorWinner]

/-- The actual coordinate order gives the absolute letter. Rule 4a, 4b or
4c gives uppercase, and Rule 5 gives the corresponding lowercase letter. -/
theorem Step.chemical_letter {m p ls rs} (s : Step m p ls rs) {g : Geometry} {r : Reading}
    (computed : geometric g s.actual.ligands s.reflected.ligands = some r) :
    readback? g s.actual.ligands = some r.actual ∧
      r.label = some (if s.basis.five then .pseudoasymmetric (pseudoRSOfRS r.actual) else .chiral r.actual) := by
  refine ⟨(s.hands computed).1,?_⟩
  cases rule : s.basis.five with
  | false => simpa only [rule] using (s.uppercase_of_same (s.basis.same_iff.mpr rule) computed).2
  | true =>
    have opposite : s.actualWins ≠ s.reflectedWins := by
      intro same
      have contradiction := s.basis.same_iff.mp same
      simp [rule] at contradiction
    simpa only [rule] using (s.lowercase_of_opposite opposite computed).2

end TetraStereo.Engine.RingChemicalPriority.DiscoveredPriority

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.DiscoveredPriority.Step.mirror_readback
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.DiscoveredPriority.Step.uppercase_of_same
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.DiscoveredPriority.Step.lowercase_of_opposite
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.DiscoveredPriority.Basis.same_iff
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.DiscoveredPriority.Step.chemical_letter
