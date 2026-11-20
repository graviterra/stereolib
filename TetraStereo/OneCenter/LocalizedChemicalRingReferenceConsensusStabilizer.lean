import TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusSymmetry
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitRootMirrorCriterion
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

/-!
Finite classification of the history-fixing symmetries that can move a ligand at an actual
occurrence inside a root arm of the 46-atom input.

For every graph automorphism fixing root 0 and the arm atom (28, 29, 30 or 31), fixing the
whole raw history of a real descendant of that arm, and moving some neighbor of the
descendant's center, either
* the history avoids every lower-gadget atom 5..25 and the center is 2, 3 or 4 (the spoke
  rotation `rho` then fixes the history and moves the center's lower ligands), or
* the occurrence is `o+ = [0,28,32,27,26]` (arm 28) or `o- = [0,29,33,27,26]` (arm 29).
In the O18 arms 30 and 31 the second alternative never occurs.

The stabilizers come from the accepted twelve normal forms of root-fixing automorphisms; the
possible histories are enumerated by a closed finite family of actual canonical children.
This is pure graph data: no evaluator, label or comparison is used.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusStabilizer

open LocalizedChemicalRingReferenceOrbitInput
open LocalizedChemicalRingReferenceOrbitArmSymmetry (armSwap)
open LocalizedChemicalRingReferenceOrbitOtherArmSymmetry (otherArmSwap)
open LocalizedChemicalRingReferenceOrbitCoveringSymmetry (candidate)
open LocalizedChemicalRingReferenceOrbitRootMirrorCriterion (root_aut_normal_form)
open LocalizedChemicalRingReferenceConsensusSymmetry (rho)
open LocalizedMarkedTerminalReferenceScope (Descends)

/-! ## Stabilizers of the root and one arm atom -/

/-- The accepted normal form of a root-fixing automorphism. -/
def form (k : Fin 3) (a r : Bool) : Equiv.Perm (Fin 46) :=
  candidate k * (if a then armSwap else 1) * (if r then otherArmSwap else 1)

private theorem form_fixes_o16 : ∀ (k : Fin 3) (a r : Bool), form k a r 28 = 28 → a = true := by
  decide +kernel

private theorem form_fixes_29 : ∀ (k : Fin 3) (a r : Bool), form k a r 29 = 29 → a = true := by
  decide +kernel

private theorem form_fixes_o18 : ∀ (k : Fin 3) (a r : Bool), form k a r 30 = 30 → r = false := by
  decide +kernel

private theorem form_fixes_31 : ∀ (k : Fin 3) (a r : Bool), form k a r 31 = 31 → r = false := by
  decide +kernel

/-! ## Closed families of history-fixed actual descendants -/

/-- Boolean form of "`π` fixes the atom with this raw index". -/
def fixesNat (π : Equiv.Perm (Fin 46)) (a : Nat) : Bool :=
  if h : a < 46 then decide (π ⟨a, h⟩ = ⟨a, h⟩) else true

theorem fixesNat_of_forall (π : Equiv.Perm (Fin 46)) (a : Nat)
    (fixed : ∀ h : a < 46, π ⟨a, h⟩ = ⟨a, h⟩) : fixesNat π a = true := by
  unfold fixesNat
  split
  · rename_i h
    exact decide_eq_true (fixed h)
  · rfl

/-- A raw history avoids every lower-gadget atom moved by the spoke rotation. -/
def RhoFixed (history : List Nat) : Prop := ∀ a ∈ history, fixesNat rho a = true

instance (history : List Nat) : Decidable (RhoFixed history) := by
  unfold RhoFixed
  infer_instance

private def spokeAtoms (k : Fin 3) : List Nat :=
  match k.val with
  | 0 => [5, 8, 11]
  | 1 => [7, 10, 13]
  | _ => [6, 9, 12]

private def lowerPaths (lead : List Nat) (spoke : List Nat) : List (List Nat) :=
  match spoke with
  | [s, b10, b11] => [lead ++ [s], lead ++ [s, b10], lead ++ [s, b11]]
  | _ => []

/-- Real descendants of an O16 arm whose history can be fixed by an O18 exchange. -/
def o16Family (arm : Nat) (k : Fin 3) : List RawMolecule.CanonicalBranchNode :=
  let partner := if arm = 28 then 29 else 28
  let armB := if arm = 28 then 32 else 33
  let partnerB := if arm = 28 then 33 else 32
  let armFar := if arm = 28 then 36 else 37
  let partnerFar := if arm = 28 then 37 else 36
  ([[0, arm], [0, arm, armB], [0, arm, armB, 27], [0, arm, armB, armFar],
    [0, arm, armB, 27, 26], [0, arm, armB, 27, partnerB],
    [0, arm, armB, 27, 26, 1], [0, arm, armB, 27, partnerB, partner],
    [0, arm, armB, 27, partnerB, partnerFar], [0, arm, armB, 27, 26, 1, 2]] ++
    lowerPaths [0, arm, armB, 27, 26, 1, 2] (spokeAtoms k)).map nodeOf

/-- Real descendants of an O18 arm whose history can be fixed by an O16 exchange. -/
def o18Family (arm : Nat) (k : Fin 3) : List RawMolecule.CanonicalBranchNode :=
  let partner := if arm = 30 then 31 else 30
  let armB := if arm = 30 then 34 else 35
  let partnerB := if arm = 30 then 35 else 34
  let armFar := if arm = 30 then 38 else 39
  let partnerFar := if arm = 30 then 39 else 38
  ([[0, arm], [0, arm, armB], [0, arm, armB, 26], [0, arm, armB, armFar],
    [0, arm, armB, 26, 1], [0, arm, armB, 26, 27], [0, arm, armB, 26, partnerB],
    [0, arm, armB, 26, partnerB, partner], [0, arm, armB, 26, partnerB, partnerFar],
    [0, arm, armB, 26, 1, 2]] ++
    lowerPaths [0, arm, armB, 26, 1, 2] (spokeAtoms k)).map nodeOf

private def FamilyClosed (π : Equiv.Perm (Fin 46)) (family : List RawMolecule.CanonicalBranchNode) :
    Prop :=
  ∀ parent ∈ family, ∀ child ∈ mol.canonicalChildren parent,
    (∀ a ∈ child.history, fixesNat π a = true) → child.forcedLeaf = true ∨ child ∈ family

private instance (π : Equiv.Perm (Fin 46)) (family : List RawMolecule.CanonicalBranchNode) :
    Decidable (FamilyClosed π family) := by
  unfold FamilyClosed
  infer_instance

private theorem o16_closed (arm : Nat) (allowed : arm = 28 ∨ arm = 29) (k : Fin 3) :
    FamilyClosed (form k true true) (o16Family arm k) := by
  rcases allowed with rfl | rfl <;> fin_cases k <;> decide +kernel

private theorem o18_closed (arm : Nat) (allowed : arm = 30 ∨ arm = 31) (k : Fin 3) :
    FamilyClosed (form k false false) (o18Family arm k) := by
  rcases allowed with rfl | rfl <;> fin_cases k <;> decide +kernel

private theorem family_descends (π : Equiv.Perm (Fin 46)) (family : List RawMolecule.CanonicalBranchNode)
    (closed : FamilyClosed π family) (start : RawMolecule.CanonicalBranchNode) (initial : start ∈ family)
    (node : RawMolecule.CanonicalBranchNode) (path : Descends mol start node)
    (fixed : ∀ a ∈ node.history, fixesNat π a = true) :
    node.forcedLeaf = true ∨ node ∈ family := by
  induction path with
  | refl => exact Or.inr initial
  | @tail parent child path edge ih =>
      have facts := LocalizedGenericMarkedRecalculation.mem_canonicalChildren mol parent child edge
      have parentFixed : ∀ a ∈ parent.history, fixesNat π a = true := by
        intro a member
        apply fixed
        rw [facts.1]
        exact List.mem_cons_of_mem _ member
      rcases ih parentFixed with leaf | present
      · rw [LocalizedGenericMarkedRecalculation.canonicalChildren_forcedLeaf mol parent leaf] at edge
        cases edge
      · exact closed parent present child edge fixed

/-! ## The classification -/

/-- The occurrence is at a detected non-root center and `π` moves one of its neighbors. -/
def MovesNeighbor (π : Equiv.Perm (Fin 46)) (node : RawMolecule.CanonicalBranchNode) : Prop :=
  (node.atom = 2 ∨ node.atom = 3 ∨ node.atom = 4 ∨ node.atom = 26) ∧
    ∃ a : Fin 46, a.val = node.atom ∧ ∃ x : Fin 46, graph.Adj a x ∧ π x ≠ x

/-- The rotation-fixed alternative of the classification. -/
def RhoOccurrence (node : RawMolecule.CanonicalBranchNode) : Prop :=
  RhoFixed node.history ∧ (node.atom = 2 ∨ node.atom = 3 ∨ node.atom = 4)

instance (node : RawMolecule.CanonicalBranchNode) : Decidable (RhoOccurrence node) := by
  unfold RhoOccurrence
  infer_instance

private abbrev AtCenter (node : RawMolecule.CanonicalBranchNode) : Prop :=
  node.atom = 2 ∨ node.atom = 3 ∨ node.atom = 4 ∨ node.atom = 26

private theorem o16_family_center (arm : Nat) (allowed : arm = 28 ∨ arm = 29) (k : Fin 3) :
    ∀ node ∈ o16Family arm k, AtCenter node →
      RhoOccurrence node ∨ node = nodeOf [0, 28, 32, 27, 26] ∨ node = nodeOf [0, 29, 33, 27, 26] := by
  rcases allowed with rfl | rfl <;> fin_cases k <;> decide +kernel

private theorem o18_family_center (arm : Nat) (allowed : arm = 30 ∨ arm = 31) (k : Fin 3) :
    ∀ node ∈ o18Family arm k, AtCenter node → RhoOccurrence node ∨ node.atom = 26 := by
  rcases allowed with rfl | rfl <;> fin_cases k <;> decide +kernel

private theorem neighbors26 (x : Fin 46) (adjacent : graph.Adj 26 x) :
    x = 1 ∨ x = 27 ∨ x = 34 ∨ x = 35 := by
  revert adjacent
  fin_cases x <;> decide +kernel

private theorem rotation_fixed_iff :
    ∀ (k : Fin 3) (a : Fin 46), k ≠ 0 → form k true false a = a → rho a = a := by
  decide +kernel

private theorem rotation_zero : ∀ a : Fin 46, form 0 true false a = a := by
  decide +kernel

private theorem rotation_at26 :
    ∀ k : Fin 3, form k true false 1 = 1 ∧ form k true false 27 = 27 ∧
      form k true false 34 = 34 ∧ form k true false 35 = 35 := by
  decide +kernel

private theorem o16Exchange_at26 :
    ∀ k : Fin 3, form k false false 1 = 1 ∧ form k false false 27 = 27 ∧
      form k false false 34 = 34 ∧ form k false false 35 = 35 := by
  decide +kernel

private theorem rotation_moves (k : Fin 3) (node : RawMolecule.CanonicalBranchNode)
    (fixed : ∀ a ∈ node.history, ∀ h : a < 46, form k true false ⟨a, h⟩ = ⟨a, h⟩)
    (moves : MovesNeighbor (form k true false) node) : RhoOccurrence node := by
  obtain ⟨center, a, atomEq, x, adjacent, moved⟩ := moves
  have nonzero : k ≠ 0 := by
    rintro rfl
    exact moved (rotation_zero x)
  refine ⟨?_, ?_⟩
  · intro value member
    apply fixesNat_of_forall
    intro bound
    exact rotation_fixed_iff k _ nonzero (fixed value member bound)
  · rcases center with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exfalso
      have same : a = 26 := Fin.ext (atomEq.trans h)
      subst same
      have actions := rotation_at26 k
      rcases neighbors26 x adjacent with rfl | rfl | rfl | rfl
      · exact moved actions.1
      · exact moved actions.2.1
      · exact moved actions.2.2.1
      · exact moved actions.2.2.2

private theorem forall_fixes (π : Equiv.Perm (Fin 46)) (node : RawMolecule.CanonicalBranchNode)
    (fixed : ∀ a ∈ node.history, ∀ h : a < 46, π ⟨a, h⟩ = ⟨a, h⟩) :
    ∀ a ∈ node.history, fixesNat π a = true :=
  fun a member => fixesNat_of_forall π a (fixed a member)

/-- **Classification in the O16 arms.** -/
theorem o16_arm_classification (arm : Nat) (allowed : arm = 28 ∨ arm = 29)
    (e : graph.Aut) (f0 : e.val (0 : Fin 46) = (0 : Fin 46))
    (fixedArm : ∀ h : arm < 46, e.val ⟨arm, h⟩ = ⟨arm, h⟩)
    (node : RawMolecule.CanonicalBranchNode) (path : Descends mol (nodeOf [0, arm]) node)
    (real : node.forcedLeaf = false)
    (fixed : ∀ a ∈ node.history, ∀ h : a < 46, e.val ⟨a, h⟩ = ⟨a, h⟩)
    (moves : MovesNeighbor e.val node) :
    RhoOccurrence node ∨ node = nodeOf [0, 28, 32, 27, 26] ∨ node = nodeOf [0, 29, 33, 27, 26] := by
  obtain ⟨k, a, r, same⟩ := root_aut_normal_form e f0
  have same' : e.val = form k a r := same
  rw [same'] at fixed moves fixedArm
  have aTrue : a = true := by
    rcases allowed with rfl | rfl
    · exact form_fixes_o16 k a r (fixedArm (by decide))
    · exact form_fixes_29 k a r (fixedArm (by decide))
  subst aTrue
  cases r with
  | false => exact Or.inl (rotation_moves k node fixed moves)
  | true =>
      have start : nodeOf [0, arm] ∈ o16Family arm k := by
        rcases allowed with rfl | rfl <;> fin_cases k <;> decide +kernel
      rcases family_descends (form k true true) (o16Family arm k) (o16_closed arm allowed k)
        (nodeOf [0, arm]) start node path (forall_fixes _ node fixed) with leaf | present
      · rw [real] at leaf
        cases leaf
      · exact o16_family_center arm allowed k node present moves.1

/-- **Classification in the O18 arms**: only rotation-fixed lower occurrences. -/
theorem o18_arm_classification (arm : Nat) (allowed : arm = 30 ∨ arm = 31)
    (e : graph.Aut) (f0 : e.val (0 : Fin 46) = (0 : Fin 46))
    (fixedArm : ∀ h : arm < 46, e.val ⟨arm, h⟩ = ⟨arm, h⟩)
    (node : RawMolecule.CanonicalBranchNode) (path : Descends mol (nodeOf [0, arm]) node)
    (real : node.forcedLeaf = false)
    (fixed : ∀ a ∈ node.history, ∀ h : a < 46, e.val ⟨a, h⟩ = ⟨a, h⟩)
    (moves : MovesNeighbor e.val node) : RhoOccurrence node := by
  obtain ⟨k, a, r, same⟩ := root_aut_normal_form e f0
  have same' : e.val = form k a r := same
  rw [same'] at fixed moves fixedArm
  have rFalse : r = false := by
    rcases allowed with rfl | rfl
    · exact form_fixes_o18 k a r (fixedArm (by decide))
    · exact form_fixes_31 k a r (fixedArm (by decide))
  subst rFalse
  cases a with
  | true => exact rotation_moves k node fixed moves
  | false =>
      have start : nodeOf [0, arm] ∈ o18Family arm k := by
        rcases allowed with rfl | rfl <;> fin_cases k <;> decide +kernel
      rcases family_descends (form k false false) (o18Family arm k) (o18_closed arm allowed k)
        (nodeOf [0, arm]) start node path (forall_fixes _ node fixed) with leaf | present
      · rw [real] at leaf
        cases leaf
      · rcases o18_family_center arm allowed k node present moves.1 with occurrence | at26
        · exact occurrence
        · exfalso
          obtain ⟨_, b, atomEq, x, adjacent, moved⟩ := moves
          have sameB : b = 26 := Fin.ext (atomEq.trans at26)
          subst sameB
          have actions := o16Exchange_at26 k
          rcases neighbors26 x adjacent with rfl | rfl | rfl | rfl
          · exact moved actions.1
          · exact moved actions.2.1
          · exact moved actions.2.2.1
          · exact moved actions.2.2.2

end TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusStabilizer

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusStabilizer.fixesNat_of_forall
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusStabilizer.o16_arm_classification
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusStabilizer.o18_arm_classification
