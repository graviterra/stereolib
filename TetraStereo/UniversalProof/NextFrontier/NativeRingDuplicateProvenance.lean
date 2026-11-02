import TetraStereo.UniversalProof.NextFrontier.NativeRingHydrogenFacts
import TetraStereo.UniversalProof.NextFrontier.FramedAtomicDispatch
import TetraStereo.UniversalProof.PositiveHydrogenBondTransportProofs.PositiveHydrogenBondTransport

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeRingDuplicateProvenance

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.UniversalProof.NativeRingDomain
open TetraStereo.UniversalProof.GeneralRingPhysicalAdmission
open TetraStereo.UniversalProof.NativeRingHydrogenFacts
open TetraStereo.UniversalProof.PositiveHydrogenBondTransportProofs.PositiveHydrogenBondTransport

/-- Follow the physical cycle from the substituted carbon through successive methylenes. -/
def cycleNode : Nat → CanonicalBranchNode
  | 0 => canonicalRoot 0 2
  | k + 1 =>
      { atom := k + 4, parent := (cycleNode k).atom,
        history := (k + 4) :: (cycleNode k).history, provenance := .realAtom }

theorem cycleNode_atom (k : Nat) :
    (cycleNode k).atom = if k = 0 then 2 else k + 3 := by
  cases k <;> rfl

theorem cycleNode_real (k : Nat) : (cycleNode k).provenance = .realAtom := by
  cases k <;> rfl

theorem cycleNode_forced (k : Nat) : (cycleNode k).forcedLeaf = false := by
  cases k <;> rfl

theorem cycleNode_atom_positive (k : Nat) : 0 < (cycleNode k).atom := by
  rw [cycleNode_atom]
  split <;> omega

theorem cycleNode_parent_bound (k : Nat) : (cycleNode k).parent < k + 4 := by
  cases k with
  | zero => decide
  | succ k =>
      change (cycleNode k).atom < k + 1 + 4
      rw [cycleNode_atom]
      split <;> omega

theorem cycleNode_history_bound (k : Nat) :
    ∀ atom ∈ (cycleNode k).history, atom < k + 4 := by
  induction k with
  | zero => intro atom member; simp only [cycleNode, canonicalRoot, List.mem_cons,
      List.not_mem_nil, or_false] at member; omega
  | succ k ih =>
      intro atom member
      rcases List.mem_cons.mp member with same | old
      · omega
      · have bound := ih atom old
        omega

theorem cycleNode_history_root (k : Nat) : 0 ∈ (cycleNode k).history := by
  induction k with
  | zero => decide
  | succ k ih => exact List.mem_cons_of_mem _ ih

private theorem canonicalBondOrder_positive (mol : RawMolecule) (node : CanonicalBranchNode)
    (next : Nat) (positive : 0 < mol.bondOrder node.atom next) :
    0 < mol.canonicalBondOrder node next := by
  unfold canonicalBondOrder
  split
  · split
    · decide
    · exact positive
  · exact positive

private theorem retain_nonparent_copy (parent : Nat) (copy : Nat × Nat)
    (copies : List (Nat × Nat)) (different : copy.1 ≠ parent) (member : copy ∈ copies) :
    copy ∈ eraseCanonicalParentCopy parent copies := by
  induction copies with
  | nil => simp at member
  | cons head tail ih =>
      by_cases erased : (head.1 == parent && head.2 == 0) = true
      · simp only [eraseCanonicalParentCopy, erased, ↓reduceIte]
        rcases List.mem_cons.mp member with same | retained
        · subst head
          have both : copy.1 = parent ∧ copy.2 = 0 := by simpa using erased
          exact (different both.1).elim
        · exact retained
      · simp only [eraseCanonicalParentCopy, erased, Bool.false_eq_true, ↓reduceIte, List.mem_cons]
        rcases List.mem_cons.mp member with same | retained
        · exact Or.inl same
        · exact Or.inr (ih retained)

/-- The exact child emitted by the production constructor along a real graph edge. -/
def edgeChild (node : CanonicalBranchNode) (next : Nat) : CanonicalBranchNode :=
  { atom := next, parent := node.atom, history := next :: node.history,
    provenance := if node.history.contains next then
      .ringDuplicate (canonicalHistoryDistance node next) else .realAtom }

/-- An independently present forward single bond supplies copy zero in the actual generator.
Only immediate backtracking is removed; a return to any earlier history atom becomes a duplicate. -/
theorem edgeChild_mem (mol : RawMolecule) (node : CanonicalBranchNode) (next : Nat)
    (present : ({ source := node.atom, target := next, kind := .single } : RawBond) ∈ mol.bonds)
    (different : node.atom ≠ next) (notParent : next ≠ node.parent)
    (real : node.forcedLeaf = false) : edgeChild node next ∈ mol.canonicalChildren node := by
  have positive : 0 < mol.bondOrder node.atom next := by
    apply (bondOrder_pos_iff_exists_bond mol different).mpr
    exact ⟨_, present, by simp [RawBond.connects]⟩
  have copiesPositive := canonicalBondOrder_positive mol node next positive
  have seed : (next, 0) ∈ mol.canonicalChildCopies node := by
    unfold canonicalChildCopies
    apply retain_nonparent_copy _ _ _ notParent
    apply List.mem_flatMap.mpr
    refine ⟨{ source := node.atom, target := next, kind := .single }, present, ?_⟩
    simp only [beq_self_eq_true, ↓reduceIte]
    exact List.mem_map.mpr ⟨0, List.mem_range.mpr copiesPositive, rfl⟩
  unfold canonicalChildren
  rw [real]
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply List.mem_map.mpr
  exact ⟨(next, 0), seed, by rfl⟩

theorem expanded_cycle_start (n : Nat) (parity : TetrahedralInputParity) :
    CanonicalCenterTreeNode (expanded n parity) 0 (cycleNode 0) := by
  have edge := withExplicitHydrogens_retains_original_bonds (ringRaw n parity)
    ({ source := 0, target := 2, kind := .single } : RawBond) (prefix1_mem n)
  apply CanonicalCenterTreeNode.child CanonicalCenterTreeNode.root
  simpa [edgeChild, canonicalCenterRoot, canonicalRoot, cycleNode] using
    edgeChild_mem (expanded n parity) (canonicalCenterRoot 0) 2 edge
      (by decide) (by decide) rfl

theorem expanded_cycle_step (n : Nat) (parity : TetrahedralInputParity)
    (k : Nat) (bound : k ≤ n) :
    cycleNode (k + 1) ∈ (expanded n parity).canonicalChildren (cycleNode k) := by
  have present : ({ source := (cycleNode k).atom, target := k + 4, kind := .single } : RawBond)
      ∈ (expanded n parity).bonds := by
    rw [cycleNode_atom]
    exact withExplicitHydrogens_retains_original_bonds (ringRaw n parity) (chainBond k)
      (chainBond_mem n k (by omega))
  have different : (cycleNode k).atom ≠ k + 4 := by rw [cycleNode_atom]; split <;> omega
  have notParent : k + 4 ≠ (cycleNode k).parent := by
    have bound := cycleNode_parent_bound k
    omega
  have fresh : k + 4 ∉ (cycleNode k).history := by
    intro member
    have bound := cycleNode_history_bound k _ member
    omega
  have generated := edgeChild_mem (expanded n parity) (cycleNode k) (k + 4)
    present different notParent (cycleNode_forced k)
  simpa only [edgeChild, List.contains_eq_mem, fresh, decide_false, Bool.false_eq_true,
    ↓reduceIte, cycleNode] using generated

theorem expanded_cycle_generated (n : Nat) (parity : TetrahedralInputParity)
    (k : Nat) (bound : k ≤ n + 1) :
    CanonicalCenterTreeNode (expanded n parity) 0 (cycleNode k) := by
  induction k with
  | zero => exact expanded_cycle_start n parity
  | succ k ih =>
      exact CanonicalCenterTreeNode.child (ih (by omega))
        (expanded_cycle_step n parity k (by omega))

def ringDuplicate (n : Nat) : CanonicalBranchNode := edgeChild (cycleNode (n + 1)) 0

theorem ringDuplicate_not_real (n : Nat) : (ringDuplicate n).provenance ≠ .realAtom := by
  simp [ringDuplicate, edgeChild, cycleNode_history_root]

/-- The closing edge creates a genuine ring-duplicate occurrence at every ring size. -/
theorem expanded_ring_duplicate_generated (n : Nat) (parity : TetrahedralInputParity) :
    CanonicalCenterTreeNode (expanded n parity) 0 (ringDuplicate n) := by
  have present : ({ source := (cycleNode (n + 1)).atom, target := 0, kind := .single } : RawBond)
      ∈ (expanded n parity).bonds :=
    withExplicitHydrogens_retains_original_bonds (ringRaw n parity) (closureBond n)
      (closureBond_mem n)
  have different : (cycleNode (n + 1)).atom ≠ 0 := by
    have positive := cycleNode_atom_positive (n + 1)
    omega
  have notParent : 0 ≠ (cycleNode (n + 1)).parent := by
    change 0 ≠ (cycleNode n).atom
    have positive := cycleNode_atom_positive n
    omega
  exact CanonicalCenterTreeNode.child
    (expanded_cycle_generated n parity (n + 1) (Nat.le_refl _))
    (edgeChild_mem _ _ _ present different notParent (cycleNode_forced _))

/-- The framed profile really is unavailable because its generated all-real guard encounters the
actual ring duplicate. This is derived from the graph family, never assumed from dispatch. -/
theorem expanded_profile_none (n : Nat) (parity : TetrahedralInputParity) :
    FrameRuntime.profile? (expanded n parity) (canonicalCenterRoot 0) = none := by
  cases profileEq : FrameRuntime.profile? (expanded n parity) (canonicalCenterRoot 0) with
  | none => rfl
  | some profile =>
      have real := (FramedAtomicDispatch.profile_generated CanonicalCenterTreeNode.root
        profile profileEq (ringDuplicate n) (expanded_ring_duplicate_generated n parity)).2
      exact (ringDuplicate_not_real n real).elim

end TetraStereo.UniversalProof.NativeRingDuplicateProvenance
