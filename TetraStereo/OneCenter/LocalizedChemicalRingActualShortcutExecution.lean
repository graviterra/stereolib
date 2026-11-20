import TetraStereo.OneCenter.LocalizedChemicalRingBoundaryOrientationShortcut
import TetraStereo.OneCenter.LocalizedChemicalRingMatchedWitnessRefusal
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
A correction that damages an earlier boundary center supplies an alternate ACTUAL
recursive query at the same current atom. Splicing its residual shortcut into the old
frontPath preserves a simple molecular path and the original selected root branch. The
actual selection, raw descent and sufficient structural budget are derived from the
original key reconstruction, not assumed for the new path.

No matching label on the image path or successful descriptor is asserted. Those remain
the substantive obligations when using this new occurrence to repair the reconstruction.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingActualShortcutExecution

open RetainedCoherentSymmetry RetainedRingSymmetryReconstruction
open LocalizedChemicalRingBoundaryOrientationShortcut
open LocalizedChemicalRingInheritedRefusalCases LocalizedChemicalRingSelectedRefusalWitness
open LocalizedChemicalRingBoundaryWitnessExecution LocalizedChemicalRingBoundaryWitnessFactMatch
open LocalizedChemicalRingWitnessFactMatch LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingMatchedWitnessRefusal
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedMarkedOperationEvaluator (tiedChildren)
open LocalizedMarkedTerminalReferenceScope (Descends)
open LocalizedGenericMarkedRecalculation (structuralDepth)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign)

private theorem chain_splice {V : Type*} [Fintype V] [DecidableEq V] (m : MoleculeGraph V)
    (frontPath : List V) (d : V) (oldTail newTail : List V)
    (old : BondedChain m (frontPath ++ d :: oldTail))
    (replacement : BondedChain m (d :: newTail)) :
    BondedChain m (frontPath ++ d :: newTail) := by
  induction frontPath with
  | nil => exact replacement
  | cons x frontPath ih =>
      cases frontPath with
      | nil => exact ⟨old.1, replacement⟩
      | cons y rest => exact ⟨old.1, ih old.2⟩

private theorem path_member {V : Type*} (frontPath suffix : List V) (d c x : V)
    (member : x ∈ frontPath ++ [d]) : x ∈ frontPath ++ d :: (suffix ++ [c]) := by
  rcases List.mem_append.mp member with first | last
  · exact List.mem_append_left _ first
  · exact List.mem_append_right _ (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp last)))

/-- The shortcut avoids the entire old path, so splicing it after an earlier vertex
does not repeat atoms or alter the original entry. -/
theorem splice_residual_path {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (B : List V) (entry d c x : V) (frontPath suffix interior : List V)
    (old : ResidualObsPath m B entry (frontPath ++ d :: (suffix ++ [c])))
    (middle : ResidualObsPath m (B ++ (frontPath ++ d :: (suffix ++ [c]))) x interior)
    (shortcut : BondedChain m (d :: (interior ++ [c]))) :
    ResidualObsPath m B entry (frontPath ++ d :: (interior ++ [c])) := by
  let front := frontPath ++ [d]
  have oldNodup : (front ++ (suffix ++ [c])).Nodup := by
    simpa only [front, List.append_assoc, List.singleton_append] using old.nodup
  have frontNodup := (List.nodup_append.mp oldNodup).1
  have cNotFront : c ∉ front := by
    intro present
    exact (List.nodup_append.mp oldNodup).2.2 c present c (by simp) rfl
  have oldC : c ∈ frontPath ++ d :: (suffix ++ [c]) := by simp
  have cNotMiddle : c ∉ interior := fun present =>
    middle.outside c present (List.mem_append_right _ oldC)
  have combined : (front ++ interior).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨frontNodup, middle.nodup, ?_⟩
    intro a inFront b inMiddle same
    subst b
    exact middle.outside a inMiddle
      (List.mem_append_right B (path_member frontPath suffix d c a inFront))
  have finalNodup : ((front ++ interior) ++ [c]).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨combined, by simp, ?_⟩
    intro a present b last same
    have atC : b = c := List.mem_singleton.mp last
    subst b
    subst a
    exact (not_or.mpr ⟨cNotFront, cNotMiddle⟩) (List.mem_append.mp present)
  refine ⟨by simp, ?_, ?_, ?_, chain_splice m frontPath d _ _ old.chain shortcut⟩
  · cases frontPath <;> simpa only [List.nil_append, List.cons_append, List.head?_cons] using old.head
  · simpa only [front, List.append_assoc, List.singleton_append] using finalNodup
  · intro a member
    rcases List.mem_append.mp member with first | rest
    · exact old.outside a (List.mem_append_left _ first)
    rcases List.mem_cons.mp rest with atD | rest
    · subst a
      exact old.outside d (by simp)
    rcases List.mem_append.mp rest with interiorMember | atC
    · exact fun deleted => middle.outside a interiorMember (List.mem_append_left _ deleted)
    · have same : a = c := List.mem_singleton.mp atC
      subst a
      exact old.outside c oldC

noncomputable section
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The old path and a negative supported correction construct the alternate path.
Its final incoming atom is one of the correction's outward attachments. -/
theorem alternate_residual_path (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (g : m.Aut) (B : List V) (entry current a b : V)
    (oldPath : List V) (old : ResidualObsPath m.mol B entry oldPath)
    (terminal : pathTerminal oldPath old.nonempty = current)
    (boundary : ∀ v ∈ B ++ oldPath, (g : Equiv.Perm V) v = v)
    (support : ∀ v, ¬ InComponent m.mol (B ++ oldPath) a v →
      ¬ InComponent m.mol (B ++ oldPath) b v → (g : Equiv.Perm V) v = v)
    (leftEdge : m.mol.Adj a current) (rightEdge : m.mol.Adj b current)
    (d : m.Center) (earlier : d.1 ∈ oldPath.dropLast)
    (negative : relativeSign m cfg g d = -1) :
    ∃ y, (y = a ∨ y = b) ∧
      ∃ p : {p : List V // ResidualObsPath m.mol B entry p},
        pathTerminal p.1 p.2.nonempty = current ∧
        ∃ before : List V, p.1 = before ++ [y, current] := by
  have endSplit : oldPath.dropLast ++ [current] = oldPath := by
    rw [← terminal]
    exact List.dropLast_append_getLast old.nonempty
  have currentMember : current ∈ oldPath := by
    rw [← endSplit]
    simp
  have distinct : d.1 ≠ current := by
    intro same
    have nodup : (oldPath.dropLast ++ [current]).Nodup := by rw [endSplit]; exact old.nodup
    exact (List.nodup_append.mp nodup).2.2 d.1 earlier current (by simp) same
  obtain ⟨x, y, _, _, choice, interior, last, _, _, chain⟩ :=
    boundary_negative_shortcut m cfg g (B ++ oldPath) a b current boundary support
      (List.mem_append_right _ currentMember) leftEdge rightEdge d
      (List.mem_append_right _ ((List.dropLast_sublist oldPath).mem earlier)) distinct negative
  obtain ⟨frontPath, suffix, split, _⟩ := List.eq_append_cons_of_mem earlier
  have oldEq : oldPath = frontPath ++ d.1 :: (suffix ++ [current]) := by
    rw [← endSplit, split]
    simp only [List.append_assoc, List.cons_append]
  have oldValid : ResidualObsPath m.mol B entry (frontPath ++ d.1 :: (suffix ++ [current])) :=
    oldEq ▸ old
  have middle : ResidualObsPath m.mol
      (B ++ (frontPath ++ d.1 :: (suffix ++ [current]))) x interior.1 := oldEq ▸ interior.2
  have valid := splice_residual_path m.mol B entry d.1 current x frontPath suffix interior.1
    oldValid middle chain
  refine ⟨y, choice, ⟨frontPath ++ d.1 :: (interior.1 ++ [current]), valid⟩, ?_, ?_⟩
  · simp [pathTerminal]
  · refine ⟨frontPath ++ [d.1] ++ interior.1.dropLast, ?_⟩
    have splitMiddle : interior.1.dropLast ++ [y] = interior.1 := by
      rw [← last]
      exact List.dropLast_append_getLast interior.2.nonempty
    change frontPath ++ d.1 :: (interior.1 ++ [current]) =
      frontPath ++ [d.1] ++ interior.1.dropLast ++ [y, current]
    simpa only [List.append_assoc, List.singleton_append, List.cons_append] using
      congrArg (fun vertices => frontPath ++ d.1 :: (vertices ++ [current])) splitMiddle.symm

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
  (data : OccurrenceData input mol c node) (reached : Reached mol node)
  (reference : input.Atom) (left right : Fin 4) (a b : input.Atom) (distinct : a ≠ b)
  (w : MatchedSymmetry input single
    (snapshotWith LocalizedChemicalRingInheritedFallback.rawStep? input mol
      (structuralDepth mol node) (inputGeometry input) node reference.val)
    data.target data.real ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl
    reference left right a b)

include agreement admissible supported reached distinct w in
/-- The alternate route is an actual selected descendant with the original structural
budget. Its occurrence is constructed from the physical correction, not a supplied path. -/
theorem actual_alternate_query (cfg : input.detectedMultiCenterMolecule.Configuration)
    (g : input.detectedMultiCenterMolecule.Aut) (current outL outR : input.Atom)
    (oldPath : List input.Atom)
    (old : ResidualObsPath input.moleculeGraph data.target.1.node.history.reverse a oldPath)
    (terminal : pathTerminal oldPath old.nonempty = current)
    (boundary : ∀ v ∈ data.target.1.node.history.reverse ++ oldPath,
      (g : Equiv.Perm input.Atom) v = v)
    (support : ∀ v,
      ¬ InComponent input.moleculeGraph (data.target.1.node.history.reverse ++ oldPath) outL v →
      ¬ InComponent input.moleculeGraph (data.target.1.node.history.reverse ++ oldPath) outR v →
      (g : Equiv.Perm input.Atom) v = v)
    (leftEdge : input.moleculeGraph.Adj outL current)
    (rightEdge : input.moleculeGraph.Adj outR current)
    (d : input.detectedMultiCenterMolecule.Center) (earlier : d.1 ∈ oldPath.dropLast)
    (negative : relativeSign input.detectedMultiCenterMolecule cfg g d = -1) :
    ∃ y, (y = outL ∨ y = outR) ∧
      ∃ p : {p : List input.Atom //
        ResidualObsPath input.moleculeGraph data.target.1.node.history.reverse a p},
      pathTerminal p.1 p.2.nonempty = current ∧
      (∃ before : List input.Atom, p.1 = before ++ [y, current]) ∧
      ∃ child ∈ tiedChildren mol (sparseOperations input mol) [] node,
        Descends mol child (rawPathNode data.target.1.root (boundaryPath data.target p.1)) ∧
        (rawPathNode data.target.1.root (boundaryPath data.target p.1)).history.length ≤
          structuralDepth mol node + node.history.length := by
  obtain ⟨y, choice, p, last, parent⟩ := alternate_residual_path input.detectedMultiCenterMolecule
    cfg g data.target.1.node.history.reverse a current outL outR oldPath old terminal boundary
    support leftEdge rightEdge d earlier negative
  exact ⟨y, choice, p, last, parent,
    matched_path_execution input mol agreement admissible supported single c node data reached
      reference left right a b distinct w p.1 p.2⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingActualShortcutExecution

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingActualShortcutExecution.splice_residual_path
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingActualShortcutExecution.alternate_residual_path
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingActualShortcutExecution.actual_alternate_query
