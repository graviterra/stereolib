import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitStabilizer
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCalibration
import TetraStereo.OneCenter.LocalizedChemicalRingTwoFixedNeighbors
import TetraStereo.OneCenter.LocalizedPhysicalMarkedParityCompleteness
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

/-!
Finite classification of the actual molecular symmetries exchanging root arms 28/29
while fixing root 0 and inherited reference 30. Exactly three explicit involutions
have these actions. Each fixes center 2 and induces an odd ligand permutation there.

The classification uses isotope/adjacency signatures and a four-atom stabilizer
certificate, not enumeration of all permutations or any evaluator-label premise.
The physical sign conclusion holds for every configuration because center 2 is fixed.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCoveringSymmetry

open LocalizedChemicalRingReferenceOrbitInput LocalizedChemicalRingReferenceOrbitCalibration
open LocalizedChemicalRingReferenceOrbitStabilizer LocalizedChemicalRingTwoFixedNeighbors
open LocalizedPhysicalMarkedParityCompleteness

private def candidateFun (k : Fin 3) (a : Fin 46) : Fin 46 :=
  match k.val with
  | 0 => ![0, 1, 2, 4, 3, 5, 7, 6, 8, 10, 9, 11, 13, 12, 15, 14, 18, 19, 16, 17, 21, 20, 24, 25, 22, 23, 26, 27, 29, 28, 30, 31, 33, 32, 34, 35, 37, 36, 38, 39, 41, 40, 44, 45, 42, 43] a
  | 1 => ![0, 1, 2, 4, 3, 6, 5, 7, 9, 8, 10, 12, 11, 13, 16, 17, 14, 15, 19, 18, 22, 23, 20, 21, 25, 24, 26, 27, 29, 28, 30, 31, 33, 32, 34, 35, 37, 36, 38, 39, 41, 40, 44, 45, 42, 43] a
  | _ => ![0, 1, 2, 4, 3, 7, 6, 5, 10, 9, 8, 13, 12, 11, 19, 18, 17, 16, 15, 14, 25, 24, 23, 22, 21, 20, 26, 27, 29, 28, 30, 31, 33, 32, 34, 35, 37, 36, 38, 39, 41, 40, 44, 45, 42, 43] a

def candidate (k : Fin 3) : Equiv.Perm (Fin 46) where
  toFun := candidateFun k
  invFun := candidateFun k
  left_inv := by intro a; fin_cases k <;> fin_cases a <;> rfl
  right_inv := by intro a; fin_cases k <;> fin_cases a <;> rfl

theorem candidate_graph (k : Fin 3) : graph.IsAutomorphism (candidate k) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro a <;> fin_cases k <;> fin_cases a <;> decide +kernel

private def candidateAut (k : Fin 3) : graph.Aut := ⟨candidate k, candidate_graph k⟩

theorem candidate_actions (k : Fin 3) :
    candidate k 0 = 0 ∧ candidate k 28 = 29 ∧ candidate k reference = reference ∧
      candidate k 5 = (![5, 6, 7] : Fin 3 → Fin 46) k ∧
      candidate k 2 = 2 ∧ candidate k 1 = 1 := by
  fin_cases k <;> decide +kernel

private def Spoke (a : Fin 46) : Prop :=
  graph.atomZ a = graph.atomZ 5 ∧ graph.atomMass a = graph.atomMass 5 ∧
    (∃ b : Fin 46, graph.Adj a b ∧ graph.atomZ b = graph.atomZ 8 ∧
      graph.atomMass b = graph.atomMass 8) ∧
    (∃ b : Fin 46, graph.Adj a b ∧ graph.atomZ b = graph.atomZ 11 ∧
      graph.atomMass b = graph.atomMass 11)

private theorem spoke_cases (a : Fin 46) : Spoke a → a = 5 ∨ a = 6 ∨ a = 7 := by
  unfold Spoke
  fin_cases a <;> decide +kernel

private theorem spoke_image (e : graph.Aut) :
    e.val (5 : Fin 46) = 5 ∨ e.val (5 : Fin 46) = 6 ∨ e.val (5 : Fin 46) = 7 := by
  apply spoke_cases
  refine ⟨MoleculeGraph.Aut.atomZ_eq (m := graph) e 5,
    MoleculeGraph.Aut.atomMass_eq (m := graph) e 5, ?_, ?_⟩
  · exact ⟨e.val 8, (MoleculeGraph.Aut.adj_iff (m := graph) e 5 8).mpr (by decide +kernel),
      MoleculeGraph.Aut.atomZ_eq (m := graph) e 8, MoleculeGraph.Aut.atomMass_eq (m := graph) e 8⟩
  · exact ⟨e.val 11, (MoleculeGraph.Aut.adj_iff (m := graph) e 5 11).mpr (by decide +kernel),
      MoleculeGraph.Aut.atomZ_eq (m := graph) e 11, MoleculeGraph.Aut.atomMass_eq (m := graph) e 11⟩

/-- Four actual atom pins force the entire graph automorphism to be identity. -/
theorem four_pins_rigid (e : graph.Aut)
    (f0 : e.val (0 : Fin 46) = (0 : Fin 46)) (f28 : e.val (28 : Fin 46) = 28)
    (f30 : e.val (30 : Fin 46) = 30) (f5 : e.val (5 : Fin 46) = 5) :
    e.val = 1 := by
  have f2 : e.val (2 : Fin 46) = 2 := by
    apply fixed_of_signature graph e [5] 2
    · intro x member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl
      assumption
    · unfold SignatureUnique
      decide +kernel
  have f8 : e.val (8 : Fin 46) = 8 := by
    apply fixed_of_signature graph e [5] 8
    · intro x member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl
      assumption
    · unfold SignatureUnique
      decide +kernel
  have f29 : e.val (29 : Fin 46) = 29 := by
    apply fixed_of_signature graph e [0, 28] 29
    · intro x member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> assumption
    · unfold SignatureUnique
      decide +kernel
  have f31 : e.val (31 : Fin 46) = 31 := by
    apply fixed_of_signature graph e [30] 31
    · intro x member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl
      assumption
    · unfold SignatureUnique
      decide +kernel
  have f32 : e.val (32 : Fin 46) = 32 := by
    apply fixed_of_signature graph e [28] 32
    · intro x member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl
      assumption
    · unfold SignatureUnique
      decide +kernel
  have f33 : e.val (33 : Fin 46) = 33 := by
    apply fixed_of_signature graph e [29] 33
    · intro x member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl
      assumption
    · unfold SignatureUnique
      decide +kernel
  have f34 : e.val (34 : Fin 46) = 34 := by
    apply fixed_of_signature graph e [30] 34
    · intro x member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl
      assumption
    · unfold SignatureUnique
      decide +kernel
  have f35 : e.val (35 : Fin 46) = 35 := by
    apply fixed_of_signature graph e [31] 35
    · intro x member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl
      assumption
    · unfold SignatureUnique
      decide +kernel
  have f36 : e.val (36 : Fin 46) = 36 := by
    apply fixed_of_signature graph e [32, 33] 36
    · intro x member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> assumption
    · unfold SignatureUnique
      decide +kernel
  have f37 : e.val (37 : Fin 46) = 37 := by
    apply fixed_of_signature graph e [32, 33] 37
    · intro x member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> assumption
    · unfold SignatureUnique
      decide +kernel
  have f38 : e.val (38 : Fin 46) = 38 := by
    apply fixed_of_signature graph e [34] 38
    · intro x member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl
      assumption
    · unfold SignatureUnique
      decide +kernel
  have f39 : e.val (39 : Fin 46) = 39 := by
    apply fixed_of_signature graph e [35] 39
    · intro x member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl
      assumption
    · unfold SignatureUnique
      decide +kernel
  have f42 : e.val (42 : Fin 46) = 42 := by
    apply fixed_of_signature graph e [36, 38] 42
    · intro x member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> assumption
    · unfold SignatureUnique
      decide +kernel
  have f43 : e.val (43 : Fin 46) = 43 := by
    apply fixed_of_signature graph e [36, 39] 43
    · intro x member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> assumption
    · unfold SignatureUnique
      decide +kernel
  have f44 : e.val (44 : Fin 46) = 44 := by
    apply fixed_of_signature graph e [37, 38] 44
    · intro x member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> assumption
    · unfold SignatureUnique
      decide +kernel
  have f45 : e.val (45 : Fin 46) = 45 := by
    apply fixed_of_signature graph e [37, 39] 45
    · intro x member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> assumption
    · unfold SignatureUnique
      decide +kernel
  have f26 : e.val (26 : Fin 46) = 26 := by
    apply fixed_of_signature graph e [35] 26
    · intro x member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl
      assumption
    · unfold SignatureUnique
      decide +kernel
  have f27 : e.val (27 : Fin 46) = 27 := by
    apply fixed_of_signature graph e [38, 39, 26] 27
    · intro x member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> assumption
    · unfold SignatureUnique
      decide +kernel
  have f40 : e.val (40 : Fin 46) = 40 := by
    apply fixed_of_signature graph e [43, 44, 45] 40
    · intro x member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> assumption
    · unfold SignatureUnique
      decide +kernel
  have f3 : e.val (3 : Fin 46) = 3 := by
    apply fixed_of_signature graph e [40] 3
    · intro x member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl
      assumption
    · unfold SignatureUnique
      decide +kernel
  have f14 : e.val (14 : Fin 46) = 14 := by
    apply fixed_of_signature graph e [8, 3] 14
    · intro x member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> assumption
    · unfold SignatureUnique
      decide +kernel
  apply shortcut_stabilizer e _ f30
  intro a member
  simp only [shortcutPath, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

private theorem equal_candidate (e : graph.Aut) (k : Fin 3)
    (rootFixed : e.val (0 : Fin 46) = (0 : Fin 46))
    (entry : e.val (28 : Fin 46) = (29 : Fin 46))
    (referenceFixed : e.val reference = reference)
    (spoke : e.val (5 : Fin 46) = candidate k 5) : e.val = candidate k := by
  let h : graph.Aut := (candidateAut k)⁻¹ * e
  have normalized (a : Fin 46) (same : e.val a = candidate k a) : h.val a = a := by
    change (candidate k).symm (e.val a) = a
    rw [same]
    exact (candidate k).symm_apply_apply a
  have actions := candidate_actions k
  have identity := four_pins_rigid h
    (normalized 0 (rootFixed.trans actions.1.symm))
    (normalized 28 (entry.trans actions.2.1.symm))
    (normalized 30 (referenceFixed.trans actions.2.2.1.symm))
    (normalized 5 spoke)
  apply Equiv.ext
  intro a
  have atAtom := congrArg (fun f : Equiv.Perm (Fin 46) => f a) identity
  change (candidate k).symm (e.val a) = a at atAtom
  have result := congrArg (candidate k) atAtom
  simpa only [Equiv.apply_symm_apply] using result

/-- Complete classification for the marked arm-exchange action, derived from this graph. -/
theorem reference_exchange_classification (e : graph.Aut)
    (rootFixed : e.val (0 : Fin 46) = (0 : Fin 46))
    (entry : e.val (28 : Fin 46) = (29 : Fin 46))
    (referenceFixed : e.val reference = reference) :
    ∃ k : Fin 3, e.val = candidate k := by
  rcases spoke_image e with spoke | spoke | spoke
  · exact ⟨0, equal_candidate e 0 rootFixed entry referenceFixed spoke⟩
  · exact ⟨1, equal_candidate e 1 rootFixed entry referenceFixed spoke⟩
  · exact ⟨2, equal_candidate e 2 rootFixed entry referenceFixed spoke⟩

private theorem candidate_local_actions (k : Fin 3) :
    ∃ fixed moved : Fin 46, (1 : Fin 46) ≠ fixed ∧ graph.Adj 2 fixed ∧
      candidate k fixed = fixed ∧ graph.Adj 2 moved ∧ candidate k moved ≠ moved := by
  fin_cases k
  · exact ⟨5, 6, by decide, by decide +kernel, rfl, by decide +kernel, by decide⟩
  · exact ⟨7, 5, by decide, by decide +kernel, rfl, by decide +kernel, by decide⟩
  · exact ⟨6, 5, by decide, by decide +kernel, rfl, by decide +kernel, by decide⟩

noncomputable section

/-- The physical center is fixed and its actual detected frame has odd local action.
This holds independently of any supplied or generated auxiliary descriptor. -/
theorem reference_exchange_current_odd (e : physical.Aut)
    (rootFixed : e.val (0 : Fin 46) = (0 : Fin 46))
    (entry : e.val (28 : Fin 46) = (29 : Fin 46))
    (referenceFixed : e.val reference = reference) :
    physical.centerPerm e current = current ∧
      permHandedness (physical.ligandPermAt e current) = -1 := by
  obtain ⟨k, same⟩ := reference_exchange_classification ⟨e.val, e.2.1⟩
    rootFixed entry referenceFixed
  have actions := candidate_actions k
  obtain ⟨fixed, moved, distinct, adjacent, fixedEq, moveAdjacent, moveNe⟩ :=
    candidate_local_actions k
  apply local_odd_of_two_fixed_neighbors physical e current
    (by change e.val (2 : Fin 46) = (2 : Fin 46); rw [same]; exact actions.2.2.2.2.1)
    (1 : Fin 46) fixed distinct (by decide +kernel) adjacent
  · rw [same]
    exact actions.2.2.2.2.2
  · rw [same]
    exact fixedEq
  · exact ⟨moved, moveAdjacent, by rw [same]; exact moveNe⟩

/-- Every possible marked arm-exchange symmetry is physically negative at center 2,
for any physical configuration: no candidate is a proper map at that center. -/
theorem reference_exchange_current_negative (configuration : physical.Configuration)
    (e : physical.Aut) (rootFixed : e.val (0 : Fin 46) = (0 : Fin 46))
    (entry : e.val (28 : Fin 46) = (29 : Fin 46))
    (referenceFixed : e.val reference = reference) :
    physical.centerPerm e current = current ∧ relativeSign physical configuration e current = -1 := by
  obtain ⟨fixed, odd⟩ := reference_exchange_current_odd e rootFixed entry referenceFixed
  refine ⟨fixed, ?_⟩
  unfold relativeSign transportedSign
  rw [fixed, odd]
  have square : physical.configurationSign configuration current *
      physical.configurationSign configuration current = 1 :=
    permHandedness_mul_self (configuration current)
  nlinarith

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCoveringSymmetry

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCoveringSymmetry.candidate_graph
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCoveringSymmetry.candidate_actions
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCoveringSymmetry.four_pins_rigid
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCoveringSymmetry.reference_exchange_classification
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCoveringSymmetry.reference_exchange_current_odd
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCoveringSymmetry.reference_exchange_current_negative
