import TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerSingleton
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! A singleton reference at the current atom is decisive before all later marker rows.
The proof inspects one successful-build constructor, never the child marker tables. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactImmediateMark

open CertifiedLocalizedCIPInput DeclarativeCIP.PromotedCanonical
open LocalizedMarkedRetainedPromotedKey
open LocalizedMarkedRetainedSparsePromotedKey (sparseCompareAt?_eq)
open LocalizedChemicalRingJointMarkerSingleton (compareJoint_singleton_eq_sparse)

variable (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}

/-- A scalar promoted build records its own reference bit as its first singleton row. -/
theorem build_marker_head (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (reference : input.Atom) (W D fuel : Nat)
    (cursor : input.LocalizedRerootCursor carrierFuel) (key : PromotedKey input)
    (built : build? input target view reference W D fuel cursor = some key) :
    key.marker.head? = some [referenceBit input reference cursor] := by
  cases fuel <;> simp only [build?, Option.bind_eq_bind, Option.bind_eq_some_iff] at built
  · obtain ⟨prior, _, children, _, rest⟩ := built
    split at rest
    · cases Option.some.inj rest
      rfl
    · cases rest
  · obtain ⟨prior, _, children, _, keys, _, same⟩ := built
    cases Option.some.inj same
    rfl

/-- After an ordinary tie, unequal first marker bits decide without inspecting the tail. -/
theorem compareKeys_gt_of_marker_heads (left right : PromotedKey input)
    (ordinaryTie : (input.compareLocalizedRerootCompoundThroughRule5 left.prior right.prior).ordering = .eq)
    (leftBit rightBit : Nat) (leftHead : left.marker.head? = some [leftBit])
    (rightHead : right.marker.head? = some [rightBit]) (greater : rightBit < leftBit) :
    compareKeys input left right = .gt := by
  cases hl : left.marker with
  | nil => simp [hl] at leftHead
  | cons firstL tailL =>
      cases hr : right.marker with
      | nil => simp [hr] at rightHead
      | cons firstR tailR =>
          have firstLeft : firstL = [leftBit] := by simpa [hl] using leftHead
          have firstRight : firstR = [rightBit] := by simpa [hr] using rightHead
          have bits : compare leftBit rightBit = .gt := compare_gt_iff_gt.mpr greater
          have rows : compare [leftBit] [rightBit] = .gt := by
            rw [List.compare_cons_cons, bits]
            rfl
          simp only [compareKeys, ordinaryTie, Ordering.eq_then, hl, hr, firstLeft, firstRight]
          rw [List.compare_cons_cons, rows]
          rfl

/-- Actual scalar and singleton-joint comparisons are strict when the only changed earliest
observation is the current reference bit. The ordinary tie is explicit local input to this
algebraic lemma; concrete applications must derive it from their actual keys. -/
theorem compareJoint_gt_of_ordinary_tie_and_root_bits
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (reference : input.Atom) (W D : Nat)
    (left right : input.LocalizedRerootCursor carrierFuel)
    (leftValid : input.LocalizedRerootCursorValid left)
    (rightValid : input.LocalizedRerootCursorValid right)
    (leftKey rightKey : input.LocalizedRerootCompoundRule45Key)
    (leftBuilt : ordinaryKey? input target view left = some leftKey)
    (rightBuilt : ordinaryKey? input target view right = some rightKey)
    (ordinaryTie : (input.compareLocalizedRerootCompoundThroughRule5 leftKey rightKey).ordering = .eq)
    (bits : referenceBit input reference right < referenceBit input reference left) :
    LocalizedChemicalRingJointMarkerKey.compareJointAt? input target view [reference] W D left right = some .gt := by
  obtain ⟨l, hl⟩ := build?_exists input target view reference W D left leftValid
  obtain ⟨r, hr⟩ := build?_exists input target view reference W D right rightValid
  have lp : l.prior = leftKey := Option.some.inj
    ((build?_prior input target view reference W D _ left l hl).symm.trans leftBuilt)
  have rp : r.prior = rightKey := Option.some.inj
    ((build?_prior input target view reference W D _ right r hr).symm.trans rightBuilt)
  have priorTie : (input.compareLocalizedRerootCompoundThroughRule5 l.prior r.prior).ordering = .eq := by
    simpa only [lp, rp] using ordinaryTie
  have compared := compareKeys_gt_of_marker_heads input l r priorTie _ _
    (build_marker_head input target view reference W D _ left l hl)
    (build_marker_head input target view reference W D _ right r hr) bits
  rw [compareJoint_singleton_eq_sparse, sparseCompareAt?_eq]
  simp only [compareAt?, hl, hr, Option.bind_eq_bind, Option.bind_some, compared]

end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactImmediateMark

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactImmediateMark.build_marker_head
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactImmediateMark.compareKeys_gt_of_marker_heads
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactImmediateMark.compareJoint_gt_of_ordinary_tie_and_root_bits
