import TetraStereo.Examples.RingPhosphaneOxirane
import Batteries.Tactic.OpenPrivate

/-! Exact native phosphorus publications and the frozen C0 auxiliary reader. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingNestedActivePair (Reader)
open RingPyramidalConstitution (pLabels_Cl_F_C)
open RingActiveDistanceSchedule (frozen distance Cell)
open private c4Center from TetraStereo.Examples.RingPhosphaneOxirane

theorem p1_labels (i : Input) (raw : i.molecule = molecule) (q : Site i) {r : Reader i}
    (ready : RingGroupedStereo.Ready q r)
    (real : q.val.node.provenance = .realAtom)
    (current : q.val.node.current? = some (atom i raw 1)) :
    RingPyramidalPublication.pLabels i q r (atom i raw 1) =
      (readback? (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified) [5,6,0,1]).map fun h =>
        (LocalizedTetrahedralRSPseudoDescriptor.chiral h,
          LocalizedTetrahedralRSPseudoDescriptor.chiral h.swap) := by
  have written (s : Fin 3) : i.molecule.atoms[(p1 i raw s).val.val]? =
      some (AtomSpec.aliphatic (![Element.Cl,Element.F,Element.C] s)) := by
    rw [p1_val,atom_val,raw]
    fin_cases s <;> rfl
  exact pLabels_Cl_F_C ready (atom i raw 1)
    (selected_phosphorus i raw q _ real current (Or.inl rfl)) (p1 i raw) written

theorem p2_labels (i : Input) (raw : i.molecule = molecule) (q : Site i) {r : Reader i}
    (ready : RingGroupedStereo.Ready q r)
    (real : q.val.node.provenance = .realAtom)
    (current : q.val.node.current? = some (atom i raw 2)) :
    RingPyramidalPublication.pLabels i q r (atom i raw 2) =
      (readback? (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified) [7,8,0,2]).map fun h =>
        (LocalizedTetrahedralRSPseudoDescriptor.chiral h,
          LocalizedTetrahedralRSPseudoDescriptor.chiral h.swap) := by
  have written (s : Fin 3) : i.molecule.atoms[(p2 i raw s).val.val]? =
      some (AtomSpec.aliphatic (![Element.Cl,Element.F,Element.C] s)) := by
    rw [p2_val,atom_val,raw]
    fin_cases s <;> rfl
  exact pLabels_Cl_F_C ready (atom i raw 2)
    (selected_phosphorus i raw q _ real current (Or.inr rfl)) (p2 i raw) written

theorem p1_state (i : Input) (raw : i.molecule = molecule)
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true) (q : Site i)
    (real : q.val.node.provenance = .realAtom)
    (current : q.val.node.current? = some (atom i raw 1)) :
    RingChemicalGraphProof.state i q = some
      ((readback? (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified) [5,6,0,1]).map fun h =>
        (LocalizedTetrahedralRSPseudoDescriptor.chiral h,
          LocalizedTetrahedralRSPseudoDescriptor.chiral h.swap)) := by
  rw [RingChemicalGraphProof.state_eq,RingPyramidalPublication.publish,
    selected_phosphorus i raw q _ real current (Or.inl rfl)]
  exact congrArg some (p1_labels i raw q (RingChemicalGraphProof.ready admitted q) real current)

theorem p2_state (i : Input) (raw : i.molecule = molecule)
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true) (q : Site i)
    (real : q.val.node.provenance = .realAtom)
    (current : q.val.node.current? = some (atom i raw 2)) :
    RingChemicalGraphProof.state i q = some
      ((readback? (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified) [7,8,0,2]).map fun h =>
        (LocalizedTetrahedralRSPseudoDescriptor.chiral h,
          LocalizedTetrahedralRSPseudoDescriptor.chiral h.swap)) := by
  rw [RingChemicalGraphProof.state_eq,RingPyramidalPublication.publish,
    selected_phosphorus i raw q _ real current (Or.inr rfl)]
  exact congrArg some (p2_labels i raw q (RingChemicalGraphProof.ready admitted q) real current)


/-- Closed-form auxiliary cells, with no assumption on a supplied publication. -/
def canonicalStore (i : Input) (h1 h2 : Option RS) (q : Site i) : Cell := some
  (if q.val.node.provenance = .realAtom then
    if q.val.node.current?.map Fin.val = some 1 then
      h1.map (fun h => (.chiral h,.chiral h.swap))
    else if q.val.node.current?.map Fin.val = some 2 then
      h2.map (fun h => (.chiral h,.chiral h.swap))
    else none
  else none)

def canonicalReader (i : Input) (raw : i.molecule = molecule) (h1 h2 : Option RS) : Reader i :=
  frozen (canonicalStore i h1 h2) (RingGroupedReport.origin i (atom i raw 0))

private theorem canonicalStore_off (i : Input) (raw : i.molecule = molecule) (h1 h2 : Option RS)
    (q : Site i) (off : ¬ RingEligibleGraph.Eligible (RingPyramidalPublication.eligible i) q) :
    canonicalStore i h1 h2 q = some none := by
  have absent (n : IDs) (hn : n = 1 ∨ n = 2) : q.val.node.provenance = .realAtom →
      q.val.node.current?.map Fin.val ≠ some n.val := by
    intro real hit
    obtain ⟨a,current,value⟩ := Option.map_eq_some_iff.mp hit
    have same : a = atom i raw n := Fin.ext (value.trans (atom_val i raw n).symm)
    apply off
    refine ⟨real,a,current,?_⟩
    apply (eligible_ids i raw a).mpr
    rcases hn with rfl | rfl
    · exact Or.inr (Or.inl same)
    · exact Or.inr (Or.inr (Or.inl same))
  unfold canonicalStore
  by_cases real : q.val.node.provenance = .realAtom
  · have no1 : q.val.node.current?.map Fin.val ≠ some 1 := absent 1 (Or.inl rfl) real
    have no2 : q.val.node.current?.map Fin.val ≠ some 2 := absent 2 (Or.inr rfl) real
    simp only [if_pos real,if_neg no1,if_neg no2]
  · simp [real]

theorem branch_state (i : Input) (raw : i.molecule = molecule)
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true) (q : Site i)
    (root : q.val.root = atom i raw 0)
    (other : q.val.node.current? ≠ some (atom i raw 0)) :
    RingChemicalGraphProof.state i q = canonicalStore i
      (readback? (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified) [5,6,0,1])
      (readback? (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified) [7,8,0,2]) q := by
  by_cases allowed : RingEligibleGraph.Eligible (RingPyramidalPublication.eligible i) q
  · obtain ⟨real,a,current,eligible⟩ := allowed
    rcases (eligible_ids i raw a).mp eligible with zero | one | two | four
    · exact (other (current.trans (congrArg some zero))).elim
    · subst a
      rw [p1_state i raw admitted q real current]
      simp [canonicalStore,real,current,atom_val]
    · subst a
      rw [p2_state i raw admitted q real current]
      simp [canonicalStore,real,current,atom_val]
    · subst a
      let p := pairAtFour i raw (c4Center i raw) rfl
      have refusal := p.occurrence_refusal admitted q
        (by rw [root]; exact (atom_injective i raw).ne (by decide))
        (by rw [root]; exact (atom_injective i raw).ne (by decide)) real current
      rw [refusal]
      simp [canonicalStore,real,current,atom_val]
  · rw [RingChemicalGraphProof.state_eq,RingChemicalGraphProof.skips i q _ allowed,
      canonicalStore_off i raw _ _ q allowed]

/-- The entire actual C0 frozen reader, including off-root and masked sites,
is determined by the two physical P readbacks. -/
theorem frozen_c0 (i : Input) (raw : i.molecule = molecule)
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    frozen (RingChemicalGraphProof.state i) (RingGroupedReport.origin i (atom i raw 0)) =
      canonicalReader i raw
        (readback? (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified) [5,6,0,1])
        (readback? (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified) [7,8,0,2]) := by
  funext q
  unfold canonicalReader frozen
  by_cases offroot : q.val.root ≠ (RingGroupedReport.origin i (atom i raw 0)).val.root
  · simp only [if_pos offroot]
  · simp only [if_neg offroot]
    by_cases visible : distance (RingGroupedReport.origin i (atom i raw 0)) < distance q ∧
        q.val.node.current? ≠ some (RingGroupedReport.origin i (atom i raw 0)).val.root
    · simp only [if_pos visible]
      exact branch_state i raw admitted q (by simpa using not_ne_iff.mp offroot) visible.2
    · simp only [if_neg visible]

/-- The queue gate expressed solely through original atom IDs and graph provenance. -/
theorem candidate_c0_iff (i : Input) (raw : i.molecule = molecule) (q : Site i) :
    RingEligibleGraph.candidate (RingPyramidalPublication.eligible i) (atom i raw 0) q ↔
      q.val.root.val = 0 ∧ q.val.node.provenance = .realAtom ∧
        (q.val.node.current?.map Fin.val = some 1 ∨
          q.val.node.current?.map Fin.val = some 2 ∨
          q.val.node.current?.map Fin.val = some 4) := by
  have atId (a : i.certified.Atom) (n : IDs) : a = atom i raw n ↔ a.val = n.val :=
    ⟨fun h => by rw [h,atom_val],fun h => Fin.ext (h.trans (atom_val i raw n).symm)⟩
  cases current : q.val.node.current? with
  | none => simp [RingEligibleGraph.candidate,RingEligibleGraph.Eligible,current]
  | some a =>
    simp only [RingEligibleGraph.candidate,RingEligibleGraph.Eligible,current,Option.map_some,
      Option.some.injEq,atId]
    have ex : (∃ b, a = b ∧ RingPyramidalPublication.eligible i b = true) ↔
        RingPyramidalPublication.eligible i a = true := by
      constructor
      · rintro ⟨b,rfl,h⟩; exact h
      · intro h; exact ⟨a,rfl,h⟩
    simp only [ex,eligible_ids i raw a,atId]
    constructor
    · rintro ⟨root,off,real,eligible⟩
      have offId : a.val ≠ 0 := fun h => off (congrArg some ((atId a 0).mpr h))
      exact ⟨root,real,eligible.resolve_left offId⟩
    · rintro ⟨root,real,one | two | four⟩
      · exact ⟨root,by
          intro eqn
          have zero := congrArg (Option.map Fin.val) eqn
          simp only [Option.map_some,atom_val,Option.some.injEq] at zero
          omega,real,Or.inr (Or.inl one)⟩
      · exact ⟨root,by
          intro eqn
          have zero := congrArg (Option.map Fin.val) eqn
          simp only [Option.map_some,atom_val,Option.some.injEq] at zero
          omega,real,Or.inr (Or.inr (Or.inl two))⟩
      · exact ⟨root,by
          intro eqn
          have zero := congrArg (Option.map Fin.val) eqn
          simp only [Option.map_some,atom_val,Option.some.injEq] at zero
          omega,real,Or.inr (Or.inr (Or.inr four))⟩

/-- Exact materialized C0 entry at every queue prefix, including unwritten
addresses. The gate contains no ranking, descriptor or runtime premise. -/
theorem sphereEntry_c0 (i : Input) (raw : i.molecule = molecule)
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (k : Nat) (bound : k ≤ RingActiveDistanceSchedule.height i + 1) (q : Site i) :
    sphereEntry i (atom i raw 0) k q =
      if q.val.root.val = 0 ∧ q.val.node.provenance = .realAtom ∧
        (q.val.node.current?.map Fin.val = some 1 ∨
          q.val.node.current?.map Fin.val = some 2 ∨
          q.val.node.current?.map Fin.val = some 4) ∧
        RingActiveDistanceSchedule.height i < distance q + k then
        some (canonicalStore i
          (readback? (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified) [5,6,0,1])
          (readback? (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified) [7,8,0,2]) q)
      else none := by
  rw [sphereEntry_exact i (atom i raw 0) k bound q]
  have gate := candidate_c0_iff i raw q
  by_cases candidate : RingEligibleGraph.candidate (RingPyramidalPublication.eligible i) (atom i raw 0) q
  · have numeric := gate.mp candidate
    have value := branch_state i raw admitted q candidate.1 candidate.2.1
    rw [value]
    simp only [candidate,numeric.1,numeric.2.1,numeric.2.2,true_and]
  · have numeric := gate.not.mp candidate
    by_cases depth : RingActiveDistanceSchedule.height i < distance q + k
    · simp only [candidate,if_false,depth,and_true]
      rw [if_neg numeric]
    · simp [candidate,depth]

end TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane

assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane.p1_labels
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane.p2_labels
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane.p1_state
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane.p2_state
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane.branch_state
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane.frozen_c0

assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane.candidate_c0_iff
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane.sphereEntry_c0
