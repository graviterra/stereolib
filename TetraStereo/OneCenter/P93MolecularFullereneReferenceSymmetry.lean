import TetraStereo.OneCenter.P93MolecularFullereneSystematicNumberingPriority
import Mathlib.GroupTheory.OrderOfElement

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP93.Cyclic

noncomputable section

/-!
# Finite reference symmetries for systematic fullerene numbering

Fu-3.1 and Fu-3.2 begin by examining proper rotation axes from highest order downward.  Before an
axis can be paired with a starting ring, bond, or atom, the molecular cage needs an exhaustive
source-backed universe of proper rotational symmetries.  For the checked oriented spherical face
map, these are precisely the nonidentity cage automorphisms that preserve the coherent orientation
of every face.

This module enumerates all such finite carrier permutations and proves exact membership and
nonemptiness.  It does not yet identify the two cells pierced by a symmetry axis or test a helical
numbering path; those are subsequent judgments over this complete symmetry universe.
-/

/-- A carrier permutation preserves the coherent cyclic orientation of the complete face map.
Comparison is up to rotation, so the arbitrary first vertex used to write a face is irrelevant. -/
def MolecularFullereneFaceOrientationPreserving
    (input : MolecularFullereneConfigurationInput)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input)) : Prop :=
  ∀ face ∈ input.faces,
    ∃ target ∈ input.faces,
      List.IsRotated (mapMolecularFullereneFace input symmetry face) target

noncomputable instance molecularFullereneFaceOrientationPreservingDecidable
    (input : MolecularFullereneConfigurationInput)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input)) :
    Decidable (MolecularFullereneFaceOrientationPreserving input symmetry) :=
  Classical.propDecidable _

/-- Independent combinatorial meaning of one nontrivial proper rotational symmetry of the checked
oriented molecular fullerene surface. -/
def MolecularFullereneProperRotationSymmetryJudgment
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input)) : Prop :=
  OrientedMolecularFullereneFaceMapJudgment molecule input ∧
    MolecularFullereneCarrierAutomorphism molecule input symmetry ∧
    MolecularFullereneFaceOrientationPreserving input symmetry ∧
    symmetry ≠ 1

noncomputable instance molecularFullereneProperRotationSymmetryJudgmentDecidable
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input)) :
    Decidable (MolecularFullereneProperRotationSymmetryJudgment
      molecule input symmetry) :=
  Classical.propDecidable _

/-- Every admitted reference rotation has finite order strictly greater than one. -/
theorem MolecularFullereneProperRotationSymmetryJudgment.order_gt_one
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input))
    (judged : MolecularFullereneProperRotationSymmetryJudgment
      molecule input symmetry) :
    1 < orderOf symmetry := by
  have positive : 0 < orderOf symmetry := orderOf_pos symmetry
  have notOne : orderOf symmetry ≠ 1 := by
    intro orderOne
    exact judged.2.2.2 ((orderOf_eq_one_iff).mp orderOne)
  omega

/-- Exhaustive finite set of nonidentity orientation-preserving cage automorphisms. -/
noncomputable def molecularFullereneProperRotationSymmetries
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput) :
    Finset (Equiv.Perm (MolecularFullereneCarrierAtom input)) :=
  (Fintype.elems : Finset (Equiv.Perm (MolecularFullereneCarrierAtom input))).filter
    fun symmetry =>
      decide (MolecularFullereneProperRotationSymmetryJudgment molecule input symmetry)

/-- Enumeration membership is exactly the independent proper-rotation judgment. -/
@[simp] theorem mem_molecularFullereneProperRotationSymmetries_iff
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input)) :
    symmetry ∈ molecularFullereneProperRotationSymmetries molecule input ↔
      MolecularFullereneProperRotationSymmetryJudgment molecule input symmetry := by
  constructor
  · intro present
    exact of_decide_eq_true (Finset.mem_filter.mp present).2
  · intro judged
    apply Finset.mem_filter.mpr
    exact ⟨Fintype.complete symmetry, by simpa only [decide_eq_true_eq] using judged⟩

/-- The finite reference-symmetry universe is nonempty exactly when a nontrivial proper cage
rotation exists. -/
theorem molecularFullereneProperRotationSymmetries_nonempty_iff
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput) :
    (molecularFullereneProperRotationSymmetries molecule input).Nonempty ↔
      ∃ symmetry,
        MolecularFullereneProperRotationSymmetryJudgment molecule input symmetry := by
  constructor
  · rintro ⟨symmetry, present⟩
    exact ⟨symmetry,
      (mem_molecularFullereneProperRotationSymmetries_iff
        molecule input symmetry).mp present⟩
  · rintro ⟨symmetry, judged⟩
    exact ⟨symmetry,
      (mem_molecularFullereneProperRotationSymmetries_iff
        molecule input symmetry).mpr judged⟩

/-- The identity permutation is never misclassified as a Fu-3 proper reference rotation. -/
theorem identity_not_mem_molecularFullereneProperRotationSymmetries
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput) :
    (1 : Equiv.Perm (MolecularFullereneCarrierAtom input)) ∉
      molecularFullereneProperRotationSymmetries molecule input := by
  intro present
  have judged :=
    (mem_molecularFullereneProperRotationSymmetries_iff molecule input 1).mp present
  exact judged.2.2.2 rfl

/-! ## Ring, bond, and atom ends of a proper rotation axis -/

/-- The three possible surface cells through which one end of a Fu-3.1/Fu-3.2 reference axis
passes.  A bond is stored in the canonical `left < right` orientation supplied by the cage-edge
finset. -/
inductive FullereneProperRotationAxisEnd where
  | ring (face : List ℕ)
  | bond (edge : ℕ × ℕ)
  | atom (atom : ℕ)
  deriving DecidableEq, Repr

/-- Cell dimension used by Fu-3.1.2: ring is preferred to bond, which is preferred to atom. -/
inductive FullereneAxisEndKind where
  | ring
  | bond
  | atom
  deriving DecidableEq, Repr

def FullereneProperRotationAxisEnd.kind :
    FullereneProperRotationAxisEnd → FullereneAxisEndKind
  | .ring _ => .ring
  | .bond _ => .bond
  | .atom _ => .atom

def fullereneAxisEndKindRank : FullereneAxisEndKind → ℕ
  | .ring => 2
  | .bond => 1
  | .atom => 0

def compareFullereneAxisEndKinds
    (left right : FullereneAxisEndKind) : Ordering :=
  compare (fullereneAxisEndKindRank left) (fullereneAxisEndKindRank right)

/-- Fu-3.1.2 first precedence step. -/
theorem fullereneAxisEndKind_ring_gt_bond :
    compareFullereneAxisEndKinds .ring .bond = .gt := by
  rfl

/-- Fu-3.1.2 second precedence step. -/
theorem fullereneAxisEndKind_bond_gt_atom :
    compareFullereneAxisEndKinds .bond .atom = .gt := by
  rfl

/-- Every named face, canonical cage edge, and cage atom, before invariance under a particular
rotation is checked. -/
noncomputable def molecularFullereneProperRotationAxisEndCandidates
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput) :
    Finset FullereneProperRotationAxisEnd :=
  (input.faces.toFinset.image FullereneProperRotationAxisEnd.ring) ∪
    ((molecularFullereneCageEdges molecule input.carrier).image
      FullereneProperRotationAxisEnd.bond) ∪
    (input.carrier.image FullereneProperRotationAxisEnd.atom)

/-- The raw end-cell universe contains exactly named faces, canonical cage edges, and cage atoms. -/
@[simp] theorem mem_molecularFullereneProperRotationAxisEndCandidates_iff
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (axisEnd : FullereneProperRotationAxisEnd) :
    axisEnd ∈ molecularFullereneProperRotationAxisEndCandidates molecule input ↔
      match axisEnd with
      | .ring face => face ∈ input.faces
      | .bond edge => edge ∈ molecularFullereneCageEdges molecule input.carrier
      | .atom atom => atom ∈ input.carrier := by
  cases axisEnd <;>
    simp [molecularFullereneProperRotationAxisEndCandidates]

/-- Independent meaning of an end cell fixed setwise by a proper rotation.  A ring is preserved up
to cyclic rotation; a bond bisected by the axis has its endpoints exchanged; an atom on the axis
is fixed. -/
def MolecularFullereneProperRotationAxisEndJudgment
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input))
    (axisEnd : FullereneProperRotationAxisEnd) : Prop :=
  MolecularFullereneProperRotationSymmetryJudgment molecule input symmetry ∧
    match axisEnd with
    | .ring face =>
        face ∈ input.faces ∧
          List.IsRotated (mapMolecularFullereneFace input symmetry face) face
    | .bond edge =>
        edge ∈ molecularFullereneCageEdges molecule input.carrier ∧
          mapMolecularFullereneCarrierAtom input symmetry edge.1 = edge.2 ∧
          mapMolecularFullereneCarrierAtom input symmetry edge.2 = edge.1
    | .atom atom =>
        atom ∈ input.carrier ∧
          mapMolecularFullereneCarrierAtom input symmetry atom = atom

noncomputable instance molecularFullereneProperRotationAxisEndJudgmentDecidable
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input))
    (axisEnd : FullereneProperRotationAxisEnd) :
    Decidable (MolecularFullereneProperRotationAxisEndJudgment
      molecule input symmetry axisEnd) :=
  Classical.propDecidable _

/-- All and only end cells invariant under one particular proper reference symmetry. -/
noncomputable def molecularFullereneProperRotationAxisEnds
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input)) :
    Finset FullereneProperRotationAxisEnd :=
  (molecularFullereneProperRotationAxisEndCandidates molecule input).filter
    fun axisEnd =>
      decide (MolecularFullereneProperRotationAxisEndJudgment
        molecule input symmetry axisEnd)

/-- Exact invariant-end enumeration for a fixed carrier permutation. -/
@[simp] theorem mem_molecularFullereneProperRotationAxisEnds_iff
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input))
    (axisEnd : FullereneProperRotationAxisEnd) :
    axisEnd ∈ molecularFullereneProperRotationAxisEnds molecule input symmetry ↔
      MolecularFullereneProperRotationAxisEndJudgment
        molecule input symmetry axisEnd := by
  constructor
  · intro present
    exact of_decide_eq_true (Finset.mem_filter.mp present).2
  · intro judged
    apply Finset.mem_filter.mpr
    refine ⟨?_, by simpa only [decide_eq_true_eq] using judged⟩
    rw [mem_molecularFullereneProperRotationAxisEndCandidates_iff]
    cases axisEnd <;> exact judged.2.1

/-- The invariant-end set is nonempty exactly when the rotation has a named invariant ring,
bisected cage bond, or fixed cage atom. -/
theorem molecularFullereneProperRotationAxisEnds_nonempty_iff
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input)) :
    (molecularFullereneProperRotationAxisEnds molecule input symmetry).Nonempty ↔
      ∃ axisEnd,
        MolecularFullereneProperRotationAxisEndJudgment
          molecule input symmetry axisEnd := by
  constructor
  · rintro ⟨axisEnd, present⟩
    exact ⟨axisEnd,
      (mem_molecularFullereneProperRotationAxisEnds_iff
        molecule input symmetry axisEnd).mp present⟩
  · rintro ⟨axisEnd, judged⟩
    exact ⟨axisEnd,
      (mem_molecularFullereneProperRotationAxisEnds_iff
        molecule input symmetry axisEnd).mpr judged⟩

/-- A permutation rejected by the proper-rotation judgment has no admitted axis ends. -/
theorem molecularFullereneProperRotationAxisEnds_eq_empty_of_not_judged
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input))
    (notJudged : ¬MolecularFullereneProperRotationSymmetryJudgment
      molecule input symmetry) :
    molecularFullereneProperRotationAxisEnds molecule input symmetry = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro axisEnd present
  have judged :=
    (mem_molecularFullereneProperRotationAxisEnds_iff
      molecule input symmetry axisEnd).mp present
  exact notJudged judged.1

/-! ## Deduplicated proper axes -/

/-- A proper rotation axis is represented extensionally by its nonempty finite set of invariant
ring/bond/atom end cells.  This groups different nonidentity rotations about the same geometric
axis, including a higher-order generator and its lower-order powers. -/
abbrev MolecularFullereneProperRotationAxis :=
  Finset FullereneProperRotationAxisEnd

/-- Every distinct nonempty invariant end-cell set generated by an admitted proper symmetry. -/
noncomputable def molecularFullereneProperRotationAxes
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput) :
    Finset MolecularFullereneProperRotationAxis :=
  ((molecularFullereneProperRotationSymmetries molecule input).image fun symmetry =>
    molecularFullereneProperRotationAxisEnds molecule input symmetry).filter
      Finset.Nonempty

/-- Exact axis grouping: an end-cell set is present exactly when it is nonempty and is the exact
invariant set of at least one independently admitted proper symmetry. -/
@[simp] theorem mem_molecularFullereneProperRotationAxes_iff
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (axis : MolecularFullereneProperRotationAxis) :
    axis ∈ molecularFullereneProperRotationAxes molecule input ↔
      axis.Nonempty ∧
        ∃ symmetry,
          MolecularFullereneProperRotationSymmetryJudgment molecule input symmetry ∧
            molecularFullereneProperRotationAxisEnds molecule input symmetry = axis := by
  constructor
  · intro present
    have filtered := Finset.mem_filter.mp present
    rcases Finset.mem_image.mp filtered.1 with ⟨symmetry, symmetryPresent, axisEq⟩
    exact ⟨filtered.2, symmetry,
      (mem_molecularFullereneProperRotationSymmetries_iff
        molecule input symmetry).mp symmetryPresent,
      axisEq⟩
  · rintro ⟨nonempty, symmetry, judged, axisEq⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨symmetry, ?_, axisEq⟩, nonempty⟩
    exact (mem_molecularFullereneProperRotationSymmetries_iff
      molecule input symmetry).mpr judged

/-- The deduplicated proper-axis universe is nonempty exactly when some admitted proper symmetry
has a named invariant end cell. -/
theorem molecularFullereneProperRotationAxes_nonempty_iff
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput) :
    (molecularFullereneProperRotationAxes molecule input).Nonempty ↔
      ∃ symmetry,
        MolecularFullereneProperRotationSymmetryJudgment molecule input symmetry ∧
          (molecularFullereneProperRotationAxisEnds molecule input symmetry).Nonempty := by
  constructor
  · rintro ⟨axis, present⟩
    rcases (mem_molecularFullereneProperRotationAxes_iff
      molecule input axis).mp present with
      ⟨_axisNonempty, symmetry, judged, axisEq⟩
    exact ⟨symmetry, judged, axisEq.symm ▸ _axisNonempty⟩
  · rintro ⟨symmetry, judged, endsNonempty⟩
    exact ⟨molecularFullereneProperRotationAxisEnds molecule input symmetry,
      (mem_molecularFullereneProperRotationAxes_iff molecule input
        (molecularFullereneProperRotationAxisEnds molecule input symmetry)).mpr
          ⟨endsNonempty, symmetry, judged, rfl⟩⟩

/-- Every enumerated axis has at least one invariant named surface cell by construction. -/
theorem molecularFullereneProperRotationAxis_ends_nonempty
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (axis : MolecularFullereneProperRotationAxis)
    (present : axis ∈ molecularFullereneProperRotationAxes molecule input) :
    axis.Nonempty :=
  (mem_molecularFullereneProperRotationAxes_iff molecule input axis).mp present |>.1

/-! ## Proper-axis order -/

/-- Orders of every admitted rotation whose invariant end-cell set is exactly one grouped axis. -/
noncomputable def molecularFullereneProperRotationAxisOrders
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (axis : MolecularFullereneProperRotationAxis) : Finset ℕ :=
  ((molecularFullereneProperRotationSymmetries molecule input).filter fun symmetry =>
    molecularFullereneProperRotationAxisEnds molecule input symmetry = axis).image
      orderOf

/-- Exact order membership for a grouped proper axis. -/
@[simp] theorem mem_molecularFullereneProperRotationAxisOrders_iff
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (axis : MolecularFullereneProperRotationAxis)
    (axisOrder : ℕ) :
    axisOrder ∈ molecularFullereneProperRotationAxisOrders molecule input axis ↔
      ∃ symmetry,
        MolecularFullereneProperRotationSymmetryJudgment molecule input symmetry ∧
          molecularFullereneProperRotationAxisEnds molecule input symmetry = axis ∧
          orderOf symmetry = axisOrder := by
  constructor
  · intro present
    rcases Finset.mem_image.mp present with ⟨symmetry, symmetryPresent, orderEq⟩
    have filtered := Finset.mem_filter.mp symmetryPresent
    exact ⟨symmetry,
      (mem_molecularFullereneProperRotationSymmetries_iff
        molecule input symmetry).mp filtered.1,
      filtered.2,
      orderEq⟩
  · rintro ⟨symmetry, judged, axisEq, orderEq⟩
    apply Finset.mem_image.mpr
    exact ⟨symmetry,
      Finset.mem_filter.mpr
        ⟨(mem_molecularFullereneProperRotationSymmetries_iff
          molecule input symmetry).mpr judged, axisEq⟩,
      orderEq⟩

/-- Highest rotational order represented on one grouped axis; absent exactly when the proposed
end-cell set is not generated by any admitted proper symmetry. -/
noncomputable def molecularFullereneProperRotationAxisOrder?
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (axis : MolecularFullereneProperRotationAxis) : Option ℕ :=
  if nonempty :
      (molecularFullereneProperRotationAxisOrders molecule input axis).Nonempty then
    some ((molecularFullereneProperRotationAxisOrders molecule input axis).max' nonempty)
  else
    none

/-- Exact maximum-order selection for one grouped proper axis. -/
@[simp] theorem molecularFullereneProperRotationAxisOrder?_eq_some_iff
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (axis : MolecularFullereneProperRotationAxis)
    (axisOrder : ℕ) :
    molecularFullereneProperRotationAxisOrder? molecule input axis = some axisOrder ↔
      axisOrder ∈ molecularFullereneProperRotationAxisOrders molecule input axis ∧
        ∀ otherOrder ∈ molecularFullereneProperRotationAxisOrders molecule input axis,
          otherOrder ≤ axisOrder := by
  classical
  let orders := molecularFullereneProperRotationAxisOrders molecule input axis
  change (if nonempty : orders.Nonempty then some (orders.max' nonempty) else none) =
      some axisOrder ↔
    axisOrder ∈ orders ∧ ∀ otherOrder ∈ orders, otherOrder ≤ axisOrder
  by_cases nonempty : orders.Nonempty
  · rw [dif_pos nonempty]
    constructor
    · intro computed
      have maximumEq : orders.max' nonempty = axisOrder := Option.some.inj computed
      subst axisOrder
      exact ⟨orders.max'_mem nonempty,
        fun otherOrder otherPresent => orders.le_max' otherOrder otherPresent⟩
    · rintro ⟨present, greatest⟩
      apply congrArg some
      exact Nat.le_antisymm
        (greatest (orders.max' nonempty) (orders.max'_mem nonempty))
        (orders.le_max' axisOrder present)
  · rw [dif_neg nonempty]
    constructor
    · intro impossible
      cases impossible
    · rintro ⟨present, _greatest⟩
      exact False.elim (nonempty ⟨axisOrder, present⟩)

/-- Refusal is exactly absence of any admitted proper rotation with this invariant end-cell set. -/
@[simp] theorem molecularFullereneProperRotationAxisOrder?_eq_none_iff
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (axis : MolecularFullereneProperRotationAxis) :
    molecularFullereneProperRotationAxisOrder? molecule input axis = none ↔
      ¬∃ symmetry,
        MolecularFullereneProperRotationSymmetryJudgment molecule input symmetry ∧
          molecularFullereneProperRotationAxisEnds molecule input symmetry = axis := by
  classical
  let orders := molecularFullereneProperRotationAxisOrders molecule input axis
  change (if nonempty : orders.Nonempty then some (orders.max' nonempty) else none) = none ↔
    ¬∃ symmetry,
      MolecularFullereneProperRotationSymmetryJudgment molecule input symmetry ∧
        molecularFullereneProperRotationAxisEnds molecule input symmetry = axis
  by_cases nonempty : orders.Nonempty
  · rw [dif_pos nonempty]
    constructor
    · intro impossible
      cases impossible
    · intro noSymmetry
      rcases nonempty with ⟨axisOrder, orderPresent⟩
      rcases (mem_molecularFullereneProperRotationAxisOrders_iff
        molecule input axis axisOrder).mp orderPresent with
        ⟨symmetry, judged, axisEq, _orderEq⟩
      exact False.elim (noSymmetry ⟨symmetry, judged, axisEq⟩)
  · rw [dif_neg nonempty]
    constructor
    · intro _computed symmetryExists
      rcases symmetryExists with ⟨symmetry, judged, axisEq⟩
      have orderPresent : orderOf symmetry ∈ orders := by
        apply (mem_molecularFullereneProperRotationAxisOrders_iff
          molecule input axis (orderOf symmetry)).mpr
        exact ⟨symmetry, judged, axisEq, rfl⟩
      exact nonempty ⟨orderOf symmetry, orderPresent⟩
    · intro _noSymmetry
      rfl

/-- Every successfully selected grouped-axis order is genuinely nontrivial. -/
theorem molecularFullereneProperRotationAxisOrder?_gt_one_of_eq_some
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (axis : MolecularFullereneProperRotationAxis)
    (axisOrder : ℕ)
    (computed : molecularFullereneProperRotationAxisOrder?
      molecule input axis = some axisOrder) :
    1 < axisOrder := by
  have orderPresent :=
    (molecularFullereneProperRotationAxisOrder?_eq_some_iff
      molecule input axis axisOrder).mp computed |>.1
  rcases (mem_molecularFullereneProperRotationAxisOrders_iff
    molecule input axis axisOrder).mp orderPresent with
    ⟨symmetry, judged, _axisEq, orderEq⟩
  simpa [orderEq] using judged.order_gt_one molecule input symmetry

end

end BlueBookP93.Cyclic
end TetraStereo.OneCenter
