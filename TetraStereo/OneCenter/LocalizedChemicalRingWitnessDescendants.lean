import TetraStereo.OneCenter.LocalizedChemicalRingRankedReconstruction
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Every real extension of a realizing witness lies in its remaining residual component.
Consequently the ranked reconstruction's induction hypothesis covers all its later real path
occurrences, including cyclic graphs. Ring-return duplicates are not treated as fresh vertices. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingWitnessDescendants

open RetainedCoherentSymmetry RetainedRingSymmetryReconstruction BoundaryComponentReconstruction
open LocalizedChemicalRingRankedReconstruction

variable {V : Type*} [Fintype V] [DecidableEq V] (m : MoleculeGraph V)

theorem bondedChain_tail (path : List V) (chain : BondedChain m path) :
    BondedChain m path.tail := by
  cases path with
  | nil => trivial
  | cons x xs =>
      cases xs with
      | nil => trivial
      | cons y ys => exact chain.2

theorem bondedChain_append_right (initial suffix : List V)
    (chain : BondedChain m (initial ++ suffix)) : BondedChain m suffix := by
  induction initial with
  | nil => exact chain
  | cons x xs ih => exact ih (bondedChain_tail m (x :: (xs ++ suffix)) chain)

/-- The final vertex of an extended residual path is still reachable from the witness's
terminal after deleting all earlier witness vertices. -/
theorem extension_component {B : List V} {entry : V} (initial : List V) (nonempty : initial ≠ [])
    (suffix : List V) (valid : ResidualObsPath m B entry (initial ++ suffix)) :
    InComponent m (B ++ initial.dropLast) (pathTerminal initial nonempty)
      (pathTerminal (initial ++ suffix) valid.nonempty) := by
  let terminal := pathTerminal initial nonempty
  have splitPrefix : initial.dropLast ++ [terminal] = initial := List.dropLast_append_getLast nonempty
  have splitPath : initial ++ suffix = initial.dropLast ++ (terminal :: suffix) := by
    calc
      initial ++ suffix = (initial.dropLast ++ [terminal]) ++ suffix :=
        congrArg (fun path => path ++ suffix) splitPrefix.symm
      _ = initial.dropLast ++ (terminal :: suffix) := by simp only [List.append_assoc, List.singleton_append]
  have nodup : (initial.dropLast ++ (terminal :: suffix)).Nodup := splitPath ▸ valid.nodup
  have tailPath : ResidualObsPath m (B ++ initial.dropLast) terminal (terminal :: suffix) := by
    refine ⟨by simp, rfl, (List.nodup_append.mp nodup).2.1, ?_, ?_⟩
    · intro x member excluded
      rcases List.mem_append.mp excluded with inBoundary | inPrefix
      · apply valid.outside x ?_ inBoundary
        rw [splitPath]
        exact List.mem_append_right _ member
      · exact (List.nodup_append.mp nodup).2.2 x inPrefix x member rfl
    · exact bondedChain_append_right m _ _ (splitPath ▸ valid.chain)
  have result := obsPath_mem_inComponent tailPath
    (List.getLast_mem (List.cons_ne_nil terminal suffix))
  have terminalEq : pathTerminal (initial ++ suffix) valid.nonempty =
      pathTerminal (terminal :: suffix) (List.cons_ne_nil terminal suffix) := by
    simp only [pathTerminal, splitPath, List.getLast_append_of_ne_nil _ (List.cons_ne_nil terminal suffix)]
  simpa only [terminalEq] using result

theorem strict_extension_terminal_ne {B : List V} {entry : V}
    (initial : List V) (nonempty : initial ≠ []) (suffix : List V) (fresh : suffix ≠ [])
    (valid : ResidualObsPath m B entry (initial ++ suffix)) :
    pathTerminal (initial ++ suffix) valid.nonempty ≠ pathTerminal initial nonempty := by
  intro same
  have lastSuffix : pathTerminal (initial ++ suffix) valid.nonempty ∈ suffix := by
    rw [pathTerminal, List.getLast_append_of_ne_nil _ fresh]
    exact List.getLast_mem fresh
  rw [same] at lastSuffix
  exact (List.nodup_append.mp valid.nodup).2.2 _ (List.getLast_mem nonempty) _ lastSuffix rfl

/-- The structural rank strictly increases along every nonempty real extension of a
chosen ranked witness. This discharges the descendant-membership side of rank induction. -/
theorem extension_rank_lt {B : List V} {entry : V} (initial : List V) (nonempty : initial ≠ [])
    (rank : V → Nat)
    (ranked : ∀ y, InComponent m (B ++ initial.dropLast) (pathTerminal initial nonempty) y →
      y ≠ pathTerminal initial nonempty → rank (pathTerminal initial nonempty) < rank y)
    (suffix : List V) (fresh : suffix ≠ [])
    (valid : ResidualObsPath m B entry (initial ++ suffix)) :
    rank (pathTerminal initial nonempty) < rank (pathTerminal (initial ++ suffix) valid.nonempty) :=
  ranked _ (extension_component m initial nonempty suffix valid)
    (strict_extension_terminal_ne m initial nonempty suffix fresh valid)

end TetraStereo.OneCenter.LocalizedChemicalRingWitnessDescendants

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingWitnessDescendants.extension_component
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingWitnessDescendants.strict_extension_terminal_ne
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingWitnessDescendants.extension_rank_lt
