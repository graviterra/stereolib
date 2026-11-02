import TetraStereo.OneCenter.LocalizedOccurrenceCarrier
import TetraStereo.OneCenter.LocalizedParentFrameHistory
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

































namespace OfficialCIPNode

variable {V : Type*} [DecidableEq V]

/-- `childProvenance` is the real-atom provenance exactly at copy index zero of an atom that has
not yet occurred on the parent branch.  Equivalently, a generated child is a real atom iff it is
the unique zero copy of a fresh graph edge; positive copy indices are multiple-bond duplicates
and repeated atoms are ring duplicates. -/
theorem childProvenance_eq_realAtom_iff
    (node : OfficialCIPNode V) (next : V) (copyIndex : Nat) :
    node.childProvenance next copyIndex = OfficialCIPNodeProvenance.realAtom ↔
      copyIndex = 0 ∧ next ∉ node.history := by
  cases copyIndex with
  | zero =>
      by_cases visited : next ∈ node.history
      · simp [childProvenance, visited]
      · simp [childProvenance, visited]
  | succ copyIndex =>
      simp [childProvenance]

end OfficialCIPNode

namespace CertifiedLocalizedCIPInput

/-- **Real provenance implies active simple, from the actual occurrence derivation.**  Every
derived molecule-wide carrier occurrence with real-atom provenance has a duplicate-free stored
history.  The root case is the singleton atom history; every other occurrence is the `extend`
of its certified carrier parent, and real provenance forces the fresh zero copy. -/
theorem declarativeLocalizedOccurrence_activeSimple_of_provenance_real
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {occurrence : input.LocalizedCIPOccurrenceFrame}
    (derived : input.DeclarativeLocalizedOccurrence fuel occurrence)
    (real : occurrence.node.provenance = OfficialCIPNodeProvenance.realAtom) :
    occurrence.node.ActiveSimple := by
  constructor
  · exact real
  · by_cases rootAddress : occurrence.address = []
    · -- Synthetic/root edge case: the empty address is exactly the atom root frame.
      have rootFrame :=
        input.declarativeLocalizedOccurrence_eq_root_of_address_nil derived rootAddress
      rw [rootFrame]
      simp [OfficialCIPNode.root]
    · -- Non-root case: invert the actual carrier parent frame.
      have present : occurrence ∈ input.localizedOccurrences fuel :=
        (input.mem_localizedOccurrences_iff fuel occurrence).mpr derived
      obtain ⟨parent, _parentPresent, _parentRoot, _parentAddress, _parentRemaining,
        parentActive, parentExtend, _current, _currentEq, _historyEq⟩ :=
        input.exists_parentFrame_of_mem_localizedOccurrences present rootAddress
      obtain ⟨next, copyIndex, targetExtend⟩ := parentExtend
      -- Real provenance of the child forces the zero copy of a fresh atom.
      have childProvenance : parent.node.childProvenance next copyIndex =
          OfficialCIPNodeProvenance.realAtom := by
        rw [← OfficialCIPNode.extend_provenance parent.node next copyIndex, ← targetExtend]
        exact real
      have nextFresh : next ∉ parent.node.history :=
        ((OfficialCIPNode.childProvenance_eq_realAtom_iff
          parent.node next copyIndex).mp childProvenance).2
      rw [targetExtend, OfficialCIPNode.extend_history]
      exact List.nodup_cons.mpr ⟨nextFresh, parentActive.2⟩

/-- Membership form of `declarativeLocalizedOccurrence_activeSimple_of_provenance_real`. -/
theorem activeSimple_of_mem_localizedOccurrences_of_provenance_real
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {occurrence : input.LocalizedCIPOccurrenceFrame}
    (present : occurrence ∈ input.localizedOccurrences fuel)
    (real : occurrence.node.provenance = OfficialCIPNodeProvenance.realAtom) :
    occurrence.node.ActiveSimple :=
  input.declarativeLocalizedOccurrence_activeSimple_of_provenance_real
    ((input.mem_localizedOccurrences_iff fuel occurrence).mp present) real

/-- **General carrier theorem.**  Every member of the finite occurrence carrier with real-atom
provenance is active simple.  No center recognition, history assumption, address assumption, or
finiteness-side condition is needed beyond carrier membership and real provenance. -/
theorem localizedCIPOccurrence_activeSimple_of_provenance_real
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (real : occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom) :
    occurrence.1.node.ActiveSimple :=
  input.activeSimple_of_mem_localizedOccurrences_of_provenance_real occurrence.2 real

/-- A successful `RealTetrahedralCenterNode` recognition at a carrier occurrence yields an
`ActiveSimple` node.  This is the proof-facing form matching
`localizedOccurrenceDescriptorCenter?_eq_some_iff`. -/
theorem realTetrahedralCenterNode_activeSimple
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (center : input.TetrahedralCenter)
    (meaning : input.RealTetrahedralCenterNode target.1.node center) :
    target.1.node.ActiveSimple :=
  input.localizedCIPOccurrence_activeSimple_of_provenance_real target meaning.1





theorem localizedOccurrenceDescriptorCenter?_activeSimple
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (center : input.TetrahedralCenter)
    (computed : input.localizedOccurrenceDescriptorCenter? target = some center) :
    target.1.node.ActiveSimple :=
  input.realTetrahedralCenterNode_activeSimple target center
    ((input.localizedOccurrenceDescriptorCenter?_eq_some_iff target center).mp computed)

/-- Fully unpacked structure of a successful descriptor-center recognition: real provenance, the
exact center atom, and a duplicate-free branch history. -/
theorem localizedOccurrenceDescriptorCenter?_node_structure
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (center : input.TetrahedralCenter)
    (computed : input.localizedOccurrenceDescriptorCenter? target = some center) :
    target.1.node.provenance = OfficialCIPNodeProvenance.realAtom ∧
      target.1.node.current? = some center.1 ∧
      target.1.node.history.Nodup := by
  have meaning :=
    (input.localizedOccurrenceDescriptorCenter?_eq_some_iff target center).mp computed
  have active :=
    input.localizedOccurrenceDescriptorCenter?_activeSimple target center computed
  exact ⟨meaning.1, meaning.2, active.2⟩

/-- Projection form: descriptor-center success gives the real-provenance/history-nodup pair
exactly as `ActiveSimple` is defined. -/
theorem localizedOccurrenceDescriptorCenter?_provenance_and_history_nodup
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (center : input.TetrahedralCenter)
    (computed : input.localizedOccurrenceDescriptorCenter? target = some center) :
    target.1.node.provenance = OfficialCIPNodeProvenance.realAtom ∧
      target.1.node.history.Nodup :=
  input.localizedOccurrenceDescriptorCenter?_activeSimple target center computed





theorem localizedOccurrenceDescriptorCenter?_eq_none_of_not_activeSimple
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (inactive : ¬ target.1.node.ActiveSimple) :
    input.localizedOccurrenceDescriptorCenter? target = none := by
  cases computed : input.localizedOccurrenceDescriptorCenter? target with
  | none => rfl
  | some center =>
      exact absurd
        (input.localizedOccurrenceDescriptorCenter?_activeSimple target center computed)
        inactive

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter







assert_kernel_only TetraStereo.OneCenter.OfficialCIPNode.childProvenance_eq_realAtom_iff
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.declarativeLocalizedOccurrence_activeSimple_of_provenance_real
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.activeSimple_of_mem_localizedOccurrences_of_provenance_real
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedCIPOccurrence_activeSimple_of_provenance_real
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realTetrahedralCenterNode_activeSimple
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceDescriptorCenter?_activeSimple
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceDescriptorCenter?_node_structure
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceDescriptorCenter?_provenance_and_history_nodup
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceDescriptorCenter?_eq_none_of_not_activeSimple
