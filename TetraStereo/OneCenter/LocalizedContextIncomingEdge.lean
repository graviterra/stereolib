import TetraStereo.OneCenter.LocalizedAcyclicRerootNeighborCorrespondence
import TetraStereo.OneCenter.LocalizedRerootChildrenExecutable
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Actual child cursors supply their physical incoming cut edge. This includes the arm that
heads toward the retained outer root; no outward-only address condition is required. -/

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

theorem executableLocalizedRerootChild_atom_adjacent
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target child : input.LocalizedRerootCursor carrierFuel)
    (present : child ∈ input.executableLocalizedRerootChildren target)
    {targetAtom childAtom : input.Atom}
    (targetCurrent : target.occurrence.1.node.current? = some targetAtom)
    (childCurrent : child.occurrence.1.node.current? = some childAtom) :
    input.moleculeGraph.Adj targetAtom childAtom := by
  have derived := input.executableLocalizedRerootChildren_declarative target
  have intended : child.occurrence.1 ∈ input.intendedLocalizedRerootChildFrames target := by
    rw [← derived.1]
    exact List.mem_map.mpr ⟨child, present, rfl⟩
  have neighbor := input.mem_localizedRerootNeighborFrames_of_mem_intended
    target child.occurrence.1 intended
  obtain ⟨framePresent, sameRoot, classified⟩ :=
    (input.mem_localizedRerootNeighborFrames_iff target.occurrence.1 child.occurrence.1).mp neighbor
  rcases classified with parentCase | childCase
  · have nonroot : target.occurrence.1.address ≠ [] := by
      intro empty
      rw [empty] at parentCase
      simp at parentCase
    obtain ⟨certificate⟩ := input.exists_localizedParentFrameHistory target.occurrence nonroot
    have frameEq : child.occurrence.1 = certificate.parent.1 :=
      input.declarativeLocalizedOccurrence_functional_at_root_address
        ((input.mem_localizedOccurrences_iff carrierFuel child.occurrence.1).mp framePresent)
        ((input.mem_localizedOccurrences_iff carrierFuel certificate.parent.1).mp certificate.parent.2)
        (sameRoot.trans certificate.parent_root.symm)
        (parentCase.2.trans certificate.parent_address.symm)
    obtain ⟨parentCurrent, parentObserved, adjacent⟩ :=
      input.parentFrame_current_adjacent targetCurrent nonroot certificate
    rw [frameEq] at childCurrent
    have equal : childAtom = parentCurrent := Option.some.inj (childCurrent.symm.trans parentObserved)
    rwa [equal]
  · have nonempty : child.occurrence.1.address ≠ [] := by
      intro empty
      rw [empty] at childCase
      simp at childCase
    apply input.outwardChildFrame_current_adjacent targetCurrent child.occurrence.1 neighbor
      (child.occurrence.1.address.getLast nonempty) ?_ childCurrent
    calc child.occurrence.1.address = child.occurrence.1.address.dropLast ++
          [child.occurrence.1.address.getLast nonempty] :=
        (List.dropLast_append_getLast nonempty).symm
      _ = target.occurrence.1.address ++ [child.occurrence.1.address.getLast nonempty] := by
        rw [childCase.2]

/-- Every actual child carries a valid incoming cut whose two endpoints are observed real
atoms and are physically adjacent. All bookkeeping premises for expansion faithfulness are
derived from child membership. -/
theorem executableLocalizedRerootChild_incomingData
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (target child : input.LocalizedRerootCursor carrierFuel)
    (present : child ∈ input.executableLocalizedRerootChildren target) :
    ∃ targetAtom childAtom : input.Atom,
      target.occurrence.1.node.current? = some targetAtom ∧
      child.occurrence.1.node.current? = some childAtom ∧
      child.previous? = some target.occurrence ∧
      child.occurrence.1.root = target.occurrence.1.root ∧
      input.LocalizedRerootCursorValid child ∧
      input.moleculeGraph.Adj targetAtom childAtom := by
  obtain ⟨targetAtom, _, targetCurrent, _⟩ :=
    input.carrierOccurrence_realPath singleBonded acyclic target.occurrence
  obtain ⟨childAtom, _, childCurrent, _⟩ :=
    input.carrierOccurrence_realPath singleBonded acyclic child.occurrence
  have derived := input.executableLocalizedRerootChildren_declarative target
  exact ⟨targetAtom, childAtom, targetCurrent, childCurrent,
    input.executableLocalizedRerootChildren_previous target child present,
    input.localizedRerootChildren_root_eq target child _ derived present,
    input.localizedRerootChild_valid target child _ derived present,
    input.executableLocalizedRerootChild_atom_adjacent target child present targetCurrent childCurrent⟩

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.executableLocalizedRerootChild_atom_adjacent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.executableLocalizedRerootChild_incomingData
