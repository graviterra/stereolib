import TetraStereo.OneCenter.LocalizedContextFrameCompilationFromSkeleton
import TetraStereo.OneCenter.LocalizedSimpleBondFourLigandFrames
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
Cyclic single-bond context-frame compilation at an arbitrary real detected carrier occurrence.

`exists_contextFrameCompilation_of_skeleton` already compiles every stage and compound callback
from a `ContextFrameSkeleton`, with no acyclicity premise. This module supplies the missing
skeleton at a carrier occurrence whose provenance is `realAtom`, including a nonroot address,
then reuses that compiler. `centerComputed` and `frameComputed` are derived.

`localizedOccurrenceDescriptorCenter?` returns `some` only for a real-atom node whose current
atom is a tetrahedral center. A duplicate of a detected atom — a ring duplicate or a
multiple-bond duplicate — returns `none`. That `none` is not a frame obligation: the ring
endpoint branches on this recognition and must return `none` there, rather than demand a
skeleton or a compilation.
-/

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

/-- Every carrier occurrence stores a history that ends at its original root. A nonroot
occurrence's parent frame is active simple, so the endpoint follows that parent chain back to
the official root node, whose history is the singleton `[root]`. No acyclic walk is used. A
duplicate occurrence has the same endpoint and remains non-real: descriptor recognition still
returns `none` for it, and no frame is demanded there. -/
theorem frameCarrierOccurrence_history_getLast_eq_root
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    occurrence.1.node.history.getLast? = some occurrence.1.root := by
  suffices
      ∀ n (occurrence : input.LocalizedCIPOccurrence fuel),
        occurrence.1.address.length = n →
          occurrence.1.node.history.getLast? = some occurrence.1.root from
    this occurrence.1.address.length occurrence rfl
  intro n
  induction n with
  | zero =>
      intro occurrence lengthZero
      cases addressShape : occurrence.1.address with
      | nil =>
          have rootFrame :=
            input.declarativeLocalizedOccurrence_eq_root_of_address_nil
              ((input.mem_localizedOccurrences_iff fuel occurrence.1).mp occurrence.2)
              addressShape
          rw [rootFrame]
          simp [OfficialCIPNode.root]
      | cons _ _ =>
          rw [addressShape, List.length_cons] at lengthZero
          exact absurd lengthZero (Nat.succ_ne_zero _)
  | succ n inductionHypothesis =>
      intro occurrence lengthSucc
      have nonroot : occurrence.1.address ≠ [] := by
        intro addressNil
        have lengthZero : occurrence.1.address.length = 0 := by simp [addressNil]
        omega
      obtain ⟨certificate⟩ :=
        input.exists_localizedParentFrameHistory occurrence nonroot
      have parentLength : certificate.parent.1.address.length = n := by
        have step := certificate.parent_address_length input
        omega
      have parentLast :
          certificate.parent.1.node.history.getLast? = some occurrence.1.root := by
        rw [← certificate.parent_root]
        exact inductionHypothesis certificate.parent parentLength
      rw [certificate.history_eq, List.getLast?_cons, parentLast]
      rfl

/-- A carrier occurrence that is not a real atom is not a descriptor-center source.
`localizedOccurrenceDescriptorCenter?` returns `none` for a ring duplicate or a multiple-bond
duplicate of a detected atom. That result does not demand a four-ligand frame. -/
theorem localizedOccurrenceDescriptorCenter?_eq_none_of_not_realAtom
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (notReal : target.1.node.provenance ≠ OfficialCIPNodeProvenance.realAtom) :
    input.localizedOccurrenceDescriptorCenter? target = none := by
  unfold localizedOccurrenceDescriptorCenter? realTetrahedralCenterAtNode?
  exact if_neg notReal

end CertifiedLocalizedCIPInput

namespace LocalizedRuleMajorReference
open CertifiedLocalizedCIPInput DeclarativeCIP
noncomputable section
open scoped Classical

set_option maxHeartbeats 4000000

/-- On a simple-bonded certified input, every real detected carrier occurrence has an actual
four-ligand frame skeleton. The occurrence may sit at any carrier address, including a nonroot
path on a ring. Acyclicity is not assumed. Real-atom provenance is required: a duplicate of a
detected atom makes `localizedOccurrenceDescriptorCenter?` return `none`, and this skeleton is
not demanded for that duplicate. `centerComputed` and the executable frame computation are
derived from that provenance and from `targetUnit`. -/
theorem exists_cyclicContextFrameSkeleton
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (target : input.certified.LocalizedCIPOccurrence
      (LocalizedUniversalReference.carrierFuel input))
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.1 = unit.1) :
    Nonempty (ContextFrameSkeleton input target unit targetUnit) := by
  have centerMember : unit.1.atom ∈ input.certified.tetrahedralCenterSet := by
    change unit.1.atom ∈ input.certified.moleculeGraph.tetrahedralCenterSet
    exact (input.certified.moleculeGraph.mem_tetrahedralCenterSet unit.1.atom).2
      ((input.certified.moleculeGraph.isTetrahedralCenter_iff_neighborFinset_card
        unit.1.atom).2 unit.2)
  let center : input.certified.TetrahedralCenter := ⟨unit.1.atom, centerMember⟩
  obtain ⟨current, currentObserved⟩ :=
    input.certified.localizedRerootCursor_current_exists
      ({ occurrence := target, previous? := none } :
        input.certified.LocalizedRerootCursor (LocalizedUniversalReference.carrierFuel input))
  have currentHead : target.1.node.history.head? = some current := by
    have headEq := input.certified.declarativeLocalizedOccurrence_node_history_head_eq_current
      ((input.certified.mem_localizedOccurrences_iff
        (LocalizedUniversalReference.carrierFuel input) target.1).mp target.2)
    rw [currentObserved] at headEq
    exact headEq
  have rootLast : target.1.node.history.getLast? = some target.1.root :=
    input.certified.frameCarrierOccurrence_history_getLast_eq_root target
  have unitAtomCurrent := input.certified.molecularFrameUnit_atom_eq_current target.1
    currentHead rootLast
  have unitAtomEq : unit.1.atom = current := by
    calc
      unit.1.atom = (input.certified.molecularFrameUnit target.1).atom :=
        (congrArg OccurrenceUnit.atom targetUnit).symm
      _ = current := unitAtomCurrent
  have targetCurrent : target.1.node.current? = some center.1 := by
    rw [currentObserved]
    exact congrArg some unitAtomEq.symm
  have centerReal : input.certified.RealTetrahedralCenterNode target.1.node center :=
    ⟨real, targetCurrent⟩
  have centerComputed : input.certified.localizedOccurrenceDescriptorCenter? target =
      some center :=
    (input.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff target center).2 centerReal
  have enough : input.certified.certified.input.molecule.atomCount ≤
      LocalizedUniversalReference.carrierFuel input := globalCarrierFuel_adequate input
  obtain ⟨frame, alpha, frameComputed, ligandAt⟩ :=
    input.certified.exists_simpleBond_localizedOccurrenceFourLigandFrame_and_ligandPermutation_detected
      singleBonded enough target center centerReal
  have noDoubleFrameComputed :
      input.certified.localizedNoDoubleFourLigandFrameExec? target = some frame := by
    rw [input.certified.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?
      target]
    exact frameComputed
  let targetCursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input) :=
    ⟨target, none⟩
  have childAt (index : Fin 4) : frame.cursorAt index ∈
      input.certified.executableLocalizedRerootChildren targetCursor := by
    rw [← input.certified.localizedOccurrenceFourLigandFrame_cursors_eq_executable
      target frame frameComputed]
    exact List.get_mem frame.cursors (Fin.cast frame.length_eq.symm index)
  exact ⟨{
    center := center
    centerEq := rfl
    centerComputed := centerComputed
    frame := frame
    frameComputed := noDoubleFrameComputed
    detectedLigandPermutation := alpha
    ligandAt := ligandAt
    childAt := childAt }⟩

/-- Every real detected carrier occurrence compiles through the actual finite evaluator.
The six stage builds and the compound callback come from
`exists_contextFrameCompilation_of_skeleton`; this theorem only supplies the cyclic skeleton.
A duplicate of a detected atom is outside this statement: recognition returns `none`, and the
ring endpoint must return `none` rather than demand this compilation. -/
theorem exists_cyclicContextFrameCompilation
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (target : input.certified.LocalizedCIPOccurrence
      (LocalizedUniversalReference.carrierFuel input))
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.1 = unit.1) :
    Nonempty (ContextFrameCompilation input target unit targetUnit) := by
  obtain ⟨skeleton⟩ :=
    exists_cyclicContextFrameSkeleton input singleBonded target real unit targetUnit
  exact exists_contextFrameCompilation_of_skeleton input target unit targetUnit skeleton

/-- Chosen compilation at one real detected carrier occurrence. Apply this only when the
occurrence provenance is `realAtom`. If `localizedOccurrenceDescriptorCenter?` returns `none`,
including for a duplicate of a detected atom, the ring endpoint returns `none` and does not
demand this frame. -/
def cyclicContextFrameCompilation
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (target : input.certified.LocalizedCIPOccurrence
      (LocalizedUniversalReference.carrierFuel input))
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.1 = unit.1) :
    ContextFrameCompilation input target unit targetUnit :=
  Classical.choice
    (exists_cyclicContextFrameCompilation input singleBonded target real unit targetUnit)

end
end LocalizedRuleMajorReference
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.frameCarrierOccurrence_history_getLast_eq_root
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceDescriptorCenter?_eq_none_of_not_realAtom
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.exists_cyclicContextFrameSkeleton
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.exists_cyclicContextFrameCompilation
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.cyclicContextFrameCompilation
