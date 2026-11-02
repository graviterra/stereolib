import TetraStereo.OneCenter.LocalizedActualFrameChildClassification
import TetraStereo.OneCenter.LocalizedRuleMajorSeparatedArmLocality
import TetraStereo.OneCenter.LocalizedSimpleBondFourLigandFrames
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Auxiliary read support inside one final-root branch

Retained locality contains `LigandBranchReaches` only for a final-root outward
ligand cursor, and that containment is an atom walk. An auxiliary target inside
the same occurrence branch needs a path statement: an outward frame arm, not
the real parent, consults only occurrences whose address extends the branch
address and whose history keeps the branch history as a suffix. Rings may share
atoms, so the map key is the original-root path stored by `molecularFrameUnit`,
not the atom.

The real parent slot is derived from the computed frame. If that slot is
Rule-1a separated, agreement on the branch path alone gives the actual
rule-major descriptor. Separation stays an intermediate premise.
-/

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

open DeclarativeCIP

/-- `target` lies in the occurrence branch entered at `branch`: same original
root, and the branch address is a carrier prefix of the target address. -/
def RootBranchContains
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (branch target : input.LocalizedCIPOccurrence fuel) : Prop :=
  branch.1.root = target.1.root ∧ branch.1.address <+: target.1.address

/-- A descriptor-map unit lies on the branch path when it keeps the branch's
original root and its atom path extends the branch unit path. This is the key
`molecularView` reads. It does not require the atom to be unique. -/
def OccurrenceUnitExtendsRootBranch
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (branch : input.LocalizedCIPOccurrence fuel)
    (unit : OccurrenceUnit input.Atom) : Prop :=
  unit.root = branch.1.root ∧
    (input.molecularFrameUnit branch.1).path <+: unit.path

private theorem history_eq_of_same_root_address
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (branch desc : input.LocalizedCIPOccurrence fuel)
    (sameRoot : branch.1.root = desc.1.root)
    (sameAddress : branch.1.address = desc.1.address) :
    branch.1.node.history = desc.1.node.history := by
  have frameEq := input.declarativeLocalizedOccurrence_functional_at_root_address
    ((input.mem_localizedOccurrences_iff fuel branch.1).mp branch.2)
    ((input.mem_localizedOccurrences_iff fuel desc.1).mp desc.2)
    sameRoot sameAddress
  exact congrArg (fun frame => frame.node.history) frameEq

private theorem address_prefix_dropLast
    {α : Type} {branch desc : List α}
    (prefixAddr : branch <+: desc)
    (shorter : branch.length < desc.length) :
    branch <+: desc.dropLast := by
  obtain ⟨tail, addrEq⟩ := prefixAddr
  have tailNe : tail ≠ [] := by
    intro empty
    have lengthEq := congrArg List.length addrEq
    simp [empty] at lengthEq
    omega
  rw [← addrEq, List.dropLast_append_of_ne_nil tailNe]
  exact List.prefix_append branch tail.dropLast

/-- An address descendant on the same original root keeps the ancestor history
as a suffix. A ring-duplicate step prepends the repeated atom and still
lengthens the history, so the suffix survives that leaf. -/
theorem history_suffix_of_rootBranch
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (branch desc : input.LocalizedCIPOccurrence fuel)
    (sameRoot : branch.1.root = desc.1.root)
    (prefixAddr : branch.1.address <+: desc.1.address) :
    branch.1.node.history <:+ desc.1.node.history := by
  have motive : ∀ n, ∀ desc : input.LocalizedCIPOccurrence fuel,
      desc.1.address.length = n →
      branch.1.root = desc.1.root →
      branch.1.address <+: desc.1.address →
      branch.1.node.history <:+ desc.1.node.history := by
    intro n
    induction n with
    | zero =>
        intro desc hlen sameRoot' prefixAddr'
        have descEmpty : desc.1.address = [] := List.eq_nil_of_length_eq_zero hlen
        obtain ⟨tail, addrEq⟩ := prefixAddr'
        have appendEmpty : branch.1.address ++ tail = [] := by
          simpa [descEmpty] using addrEq
        have branchEmpty : branch.1.address = [] :=
          (List.append_eq_nil_iff.mp appendEmpty).1
        have sameAddress : branch.1.address = desc.1.address := by
          simp [branchEmpty, descEmpty]
        rw [input.history_eq_of_same_root_address branch desc sameRoot' sameAddress]
    | succ n ih =>
        intro desc hlen sameRoot' prefixAddr'
        by_cases equalLen : branch.1.address.length = desc.1.address.length
        · have sameAddress := List.IsPrefix.eq_of_length prefixAddr' equalLen
          rw [input.history_eq_of_same_root_address branch desc sameRoot' sameAddress]
        · have shorter : branch.1.address.length < desc.1.address.length :=
            lt_of_le_of_ne (List.IsPrefix.length_le prefixAddr') equalLen
          have nonroot : desc.1.address ≠ [] :=
            List.ne_nil_of_length_pos (by omega)
          obtain ⟨certificate⟩ := input.exists_localizedParentFrameHistory desc nonroot
          have parentRoot : branch.1.root = certificate.parent.1.root :=
            sameRoot'.trans certificate.parent_root.symm
          have parentPrefix : branch.1.address <+: certificate.parent.1.address := by
            rw [certificate.parent_address]
            exact address_prefix_dropLast prefixAddr' shorter
          have parentLen : certificate.parent.1.address.length = n := by
            have step := certificate.parent_address_length input
            omega
          have parentSuffix := ih certificate.parent parentLen parentRoot parentPrefix
          have stepSuffix : certificate.parent.1.node.history <:+
              desc.1.node.history := by
            refine ⟨[certificate.current], ?_⟩
            simpa using certificate.history_eq.symm
          exact parentSuffix.trans stepSuffix
  exact motive desc.1.address.length desc rfl sameRoot prefixAddr

/-- The unit read by `molecularView` extends the branch unit exactly when the
history suffix and original root do. -/
theorem occurrenceUnit_extends_of_rootBranch
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (branch desc : input.LocalizedCIPOccurrence fuel)
    (sameRoot : branch.1.root = desc.1.root)
    (suffix : branch.1.node.history <:+ desc.1.node.history) :
    input.OccurrenceUnitExtendsRootBranch branch (input.molecularFrameUnit desc.1) := by
  obtain ⟨extra, histEq⟩ := suffix
  have branchNe : branch.1.node.history ≠ [] := by
    have lengthEq := input.carrierOccurrence_history_length_eq_address_succ branch
    exact List.ne_nil_of_length_pos (by omega)
  have revEq : desc.1.node.history.reverse =
      branch.1.node.history.reverse ++ extra.reverse := by
    simp [← histEq, List.reverse_append]
  have revNe : branch.1.node.history.reverse ≠ [] := by
    simpa [List.reverse_eq_nil_iff] using branchNe
  have tailEq : desc.1.node.history.reverse.tail =
      branch.1.node.history.reverse.tail ++ extra.reverse := by
    rw [revEq, List.tail_append_of_ne_nil revNe]
  refine ⟨?_, ?_⟩
  · simp [molecularFrameUnit, sameRoot]
  · simp [molecularFrameUnit, tailEq, List.prefix_append]

/-- Every cursor reached from an outward child of a target inside the branch
stays inside the branch, including a ring-duplicate terminal at the first
step. The cursor is a strict depth dependency of the target and of the branch. -/
theorem outwardReachable_rootBranch
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (branch target start cursor : input.LocalizedRerootCursor fuel)
    (inside : input.RootBranchContains branch.occurrence target.occurrence)
    (outward : OutwardRerootCursor input target.occurrence start)
    (form : IsLocalizedActualFrameOutwardCursor input target.occurrence start)
    (reachable : Relation.ReflTransGen (E input) start cursor) :
    input.RootBranchContains branch.occurrence cursor.occurrence ∧
      branch.occurrence.1.node.history <:+ cursor.occurrence.1.node.history ∧
      input.LocalizedDepthDependency cursor.occurrence target.occurrence ∧
      input.LocalizedDepthDependency cursor.occurrence branch.occurrence := by
  have reached := input.outward_reachable_cursor target.occurrence start cursor
    outward reachable
  have addrPrefix := input.address_isPrefix_of_outward_reachable target.occurrence
    start cursor outward reachable
  obtain ⟨_slot, startAddr⟩ := form
  have targetPrefix : target.occurrence.1.address <+: start.occurrence.1.address := by
    rw [startAddr]
    exact List.prefix_append _ _
  have branchToCursor := inside.2.trans (targetPrefix.trans addrPrefix)
  have rootEq : branch.occurrence.1.root = cursor.occurrence.1.root :=
    inside.1.trans reached.2.1.1.symm
  have targetDepth := reached.2.1
  have branchDepth : input.LocalizedDepthDependency cursor.occurrence
      branch.occurrence := by
    refine ⟨rootEq.symm, ?_⟩
    have startLonger : target.occurrence.1.address.length <
        start.occurrence.1.address.length := by
      rw [startAddr]
      simp
    have cursorAtLeast : start.occurrence.1.address.length ≤
        cursor.occurrence.1.address.length := List.IsPrefix.length_le addrPrefix
    have branchShorter : branch.occurrence.1.address.length ≤
        target.occurrence.1.address.length := List.IsPrefix.length_le inside.2
    omega
  exact ⟨⟨rootEq, branchToCursor⟩,
    input.history_suffix_of_rootBranch branch.occurrence cursor.occurrence
      rootEq branchToCursor,
    targetDepth, branchDepth⟩

/-- A real map consult on that outward arm is a strict depth dependency, and
the unit it reads extends the branch path. -/
theorem outwardConsult_unit_extends_rootBranch
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (branch target start : input.LocalizedRerootCursor fuel)
    (inside : input.RootBranchContains branch.occurrence target.occurrence)
    (outward : OutwardRerootCursor input target.occurrence start)
    (form : IsLocalizedActualFrameOutwardCursor input target.occurrence start)
    (unit : DetectedOccurrence input.moleculeGraph)
    (consulted : input.ReachableArmDescriptorConsult target.occurrence start unit) :
    input.OccurrenceUnitExtendsRootBranch branch.occurrence unit.1 ∧
      ∃ cursor, Relation.ReflTransGen (E input) start cursor ∧
        input.LocalizedDepthDependency cursor.occurrence target.occurrence ∧
        input.LocalizedDepthDependency cursor.occurrence branch.occurrence ∧
        branch.occurrence.1.node.history <:+ cursor.occurrence.1.node.history := by
  obtain ⟨cursor, reachable, dependency, _real, unitEq⟩ := consulted
  have stayed := input.outwardReachable_rootBranch branch target start cursor
    inside outward form reachable
  refine ⟨?_, cursor, reachable, dependency, stayed.2.2.2, stayed.2.1⟩
  rw [← unitEq]
  exact input.occurrenceUnit_extends_of_rootBranch branch.occurrence cursor.occurrence
    stayed.1.1 stayed.2.1

/-- The real parent slot of a non-root computed frame. The cursor is the
canonical parent of the derived parent-frame certificate, not a chosen
address. Every other slot is an outward child. -/
theorem actualFrame_parentIndex
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (nonroot : target.1.address ≠ []) :
    ∃ index : Fin 4, ∃ certificate : input.LocalizedParentFrameHistory target,
      frame.cursorAt index =
        { occurrence := certificate.parent, previous? := some target } ∧
      IsLocalizedActualFrameParentCursor input target (frame.cursorAt index) ∧
      ∀ other : Fin 4, other ≠ index →
        IsLocalizedActualFrameOutwardCursor input target (frame.cursorAt other) ∧
          OutwardRerootCursor input target (frame.cursorAt other) := by
  obtain ⟨certificate⟩ := input.exists_localizedParentFrameHistory target nonroot
  have parentNeighbor := certificate.parent_mem_neighborFrames input
  rw [← input.localizedOccurrenceFourLigandFrame_cursors_map_eq_neighborFrames
    target frame computed] at parentNeighbor
  obtain ⟨cursor, cursorMem, occEq⟩ := List.mem_map.mp parentNeighbor
  obtain ⟨rawIndex, rawGet⟩ := List.mem_iff_get.mp cursorMem
  let index : Fin 4 := Fin.cast frame.length_eq rawIndex
  have cursorAtEq : frame.cursorAt index = cursor := by
    unfold LocalizedOccurrenceFourLigandFrame.cursorAt
    dsimp only [index]
    rw [show Fin.cast frame.length_eq.symm (Fin.cast frame.length_eq rawIndex) = rawIndex by
      exact Fin.ext rfl]
    exact rawGet
  have present : frame.cursorAt index ∈ frame.cursors :=
    List.get_mem frame.cursors (Fin.cast frame.length_eq.symm index)
  have isParent : IsLocalizedActualFrameParentCursor input target
      (frame.cursorAt index) := by
    unfold IsLocalizedActualFrameParentCursor
    rw [cursorAtEq, occEq, certificate.parent_address]
  obtain ⟨parentCertificate, parentEq⟩ :=
    input.localizedOccurrenceFourLigandFrame_parent_cursor_eq target frame computed
      (frame.cursorAt index) present isParent
  refine ⟨index, parentCertificate, parentEq, isParent, ?_⟩
  intro other otherNe
  cases input.localizedOccurrenceFourLigandFrame_cursorAt_classification
      target frame computed other with
  | inl parentCase =>
      exfalso
      obtain ⟨_certificate, _cursorEq, parentCursor⟩ := parentCase
      have sameCursor := input.localizedOccurrenceFourLigandFrame_parent_cursor_unique
        target frame computed (frame.cursorAt index) (frame.cursorAt other)
        present (List.get_mem _ _) isParent parentCursor
      exact otherNe ((input.localizedOccurrenceFourLigandFrame_cursorAt_injective
        target frame computed sameCursor).symm)
  | inr outwardCase =>
      obtain ⟨form, _rootEq, _valid, outward⟩ := outwardCase
      exact ⟨form, outward⟩

/-- A root-address target has no parent slot. The one-branch descriptor
theorem does not apply there. -/
theorem rootAddress_no_parentIndex
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (rootAddress : target.1.address = []) (index : Fin 4) :
    ¬ IsLocalizedActualFrameParentCursor input target (frame.cursorAt index) :=
  input.localizedOccurrenceFourLigandFrame_root_no_parent_cursor target frame
    computed rootAddress index

/-- Agreement on branch-path units, plus Rule-1a separation of the derived
parent slot, gives the same actual descriptor. Maps may differ off the branch. -/
theorem ruleMajorDescriptor?_eq_of_rootBranchParentSeparated
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (branch target : input.LocalizedCIPOccurrence carrierFuel)
    (inside : input.RootBranchContains branch target)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (nonroot : target.1.address ≠ [])
    (separated : ∀ index, IsLocalizedActualFrameParentCursor input target
        (frame.cursorAt index) →
      input.ArmConstitutionalRule1aSeparated frame index)
    (agree : ∀ unit, input.OccurrenceUnitExtendsRootBranch branch unit.1 →
      map₁ unit = map₂ unit) :
    input.ruleMajorDescriptor? target (input.molecularView map₁ target) =
      input.ruleMajorDescriptor? target (input.molecularView map₂ target) := by
  obtain ⟨index, _certificate, _parentEq, isParent, others⟩ :=
    input.actualFrame_parentIndex target frame computed nonroot
  have agreeArms : ∀ other, other ≠ index →
      ∀ unit, input.ReachableArmDescriptorConsult target (frame.cursorAt other) unit →
        map₁ unit = map₂ unit := by
    intro other otherNe unit consulted
    have pack := others other otherNe
    let branchCursor : input.LocalizedRerootCursor carrierFuel :=
      { occurrence := branch, previous? := none }
    let targetCursor : input.LocalizedRerootCursor carrierFuel :=
      { occurrence := target, previous? := none }
    have extended := input.outwardConsult_unit_extends_rootBranch
      branchCursor targetCursor (frame.cursorAt other) inside pack.2 pack.1 unit consulted
    exact agree unit extended.1
  exact input.ruleMajorDescriptor?_eq_of_compiledSeparatedArm target map₁ map₂
    frame computed index (separated index isParent) agreeArms

theorem ruleMajorDescriptorExec?_eq_of_rootBranchParentSeparated
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (branch target : input.LocalizedCIPOccurrence carrierFuel)
    (inside : input.RootBranchContains branch target)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (nonroot : target.1.address ≠ [])
    (separated : ∀ index, IsLocalizedActualFrameParentCursor input target
        (frame.cursorAt index) →
      input.ArmConstitutionalRule1aSeparated frame index)
    (agree : ∀ unit, input.OccurrenceUnitExtendsRootBranch branch unit.1 →
      map₁ unit = map₂ unit) :
    input.ruleMajorDescriptorExec? target (input.molecularView map₁ target) =
      input.ruleMajorDescriptorExec? target (input.molecularView map₂ target) := by
  rw [input.ruleMajorDescriptorExec?_eq target (input.molecularView map₁ target),
    input.ruleMajorDescriptorExec?_eq target (input.molecularView map₂ target)]
  exact input.ruleMajorDescriptor?_eq_of_rootBranchParentSeparated branch target
    inside map₁ map₂ frame computed nonroot separated agree

theorem ruleMajorDescriptor?_eq_of_missingCenter
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (absent : input.localizedOccurrenceDescriptorCenter? target = none) :
    input.ruleMajorDescriptor? target (input.molecularView map₁ target) =
      input.ruleMajorDescriptor? target (input.molecularView map₂ target) := by
  rw [input.ruleMajorDescriptor?_eq_none_of_no_center target
      (input.molecularView map₁ target) absent,
    input.ruleMajorDescriptor?_eq_none_of_no_center target
      (input.molecularView map₂ target) absent]

theorem ruleMajorDescriptorExec?_eq_of_missingCenter
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (absent : input.localizedOccurrenceDescriptorCenter? target = none) :
    input.ruleMajorDescriptorExec? target (input.molecularView map₁ target) =
      input.ruleMajorDescriptorExec? target (input.molecularView map₂ target) := by
  rw [input.ruleMajorDescriptorExec?_eq target (input.molecularView map₁ target),
    input.ruleMajorDescriptorExec?_eq target (input.molecularView map₂ target)]
  exact input.ruleMajorDescriptor?_eq_of_missingCenter target map₁ map₂ absent

/-- A duplicate or placeholder target has no center, so both descriptors refuse. -/
theorem ruleMajorDescriptor?_eq_of_not_realTarget
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (notReal : target.1.node.provenance ≠ OfficialCIPNodeProvenance.realAtom) :
    input.ruleMajorDescriptor? target (input.molecularView map₁ target) =
      input.ruleMajorDescriptor? target (input.molecularView map₂ target) :=
  input.ruleMajorDescriptor?_eq_of_missingCenter target map₁ map₂
    (input.localizedOccurrenceDescriptorCenter?_eq_none_of_not_realAtom target notReal)

theorem ruleMajorDescriptorExec?_eq_of_not_realTarget
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (notReal : target.1.node.provenance ≠ OfficialCIPNodeProvenance.realAtom) :
    input.ruleMajorDescriptorExec? target (input.molecularView map₁ target) =
      input.ruleMajorDescriptorExec? target (input.molecularView map₂ target) := by
  rw [input.ruleMajorDescriptorExec?_eq target (input.molecularView map₁ target),
    input.ruleMajorDescriptorExec?_eq target (input.molecularView map₂ target)]
  exact input.ruleMajorDescriptor?_eq_of_not_realTarget target map₁ map₂ notReal

theorem ruleMajorDescriptor?_eq_of_missingFrame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (absent : input.localizedOccurrenceFourLigandFrame? target = none) :
    input.ruleMajorDescriptor? target (input.molecularView map₁ target) =
      input.ruleMajorDescriptor? target (input.molecularView map₂ target) :=
  input.ruleMajorDescriptor?_eq_of_absentFrame target map₁ map₂ absent

theorem ruleMajorDescriptorExec?_eq_of_missingFrame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (absent : input.localizedOccurrenceFourLigandFrame? target = none) :
    input.ruleMajorDescriptorExec? target (input.molecularView map₁ target) =
      input.ruleMajorDescriptorExec? target (input.molecularView map₂ target) :=
  input.ruleMajorDescriptorExec?_eq_of_absentFrame target map₁ map₂ absent

end CertifiedLocalizedCIPInput

namespace LocalizedRuleMajorReference

open CertifiedLocalizedCIPInput DeclarativeCIP

/-- Cyclic compilation supplies the frame. The parent slot is derived from that
frame. `SimpleBonded`, real provenance, and the detected unit are the compiler
hypotheses. Rule-1a separation of the derived parent remains the case premise. -/
theorem ruleMajorDescriptor?_eq_of_cyclicRootBranch
    (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (branch target : input.certified.LocalizedCIPOccurrence (carrierFuel input))
    (inside : input.certified.RootBranchContains branch target)
    (nonroot : target.1.address ≠ [])
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.1 = unit.1)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.certified.moleculeGraph))
    (separated : ∀ frame, input.certified.localizedNoDoubleFourLigandFrameExec? target =
        some frame →
      ∀ index, IsLocalizedActualFrameParentCursor input.certified target
          (frame.cursorAt index) →
        input.certified.ArmConstitutionalRule1aSeparated frame index)
    (agree : ∀ unit, input.certified.OccurrenceUnitExtendsRootBranch branch unit.1 →
      map₁ unit = map₂ unit) :
    input.certified.ruleMajorDescriptor? target (input.certified.molecularView map₁ target) =
      input.certified.ruleMajorDescriptor? target
        (input.certified.molecularView map₂ target) := by
  let compilation := cyclicContextFrameCompilation input singleBonded target real unit targetUnit
  have frameComputed : input.certified.localizedOccurrenceFourLigandFrame? target =
      some compilation.frame := by
    rw [← input.certified.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?
      target]
    exact compilation.frameComputed
  exact input.certified.ruleMajorDescriptor?_eq_of_rootBranchParentSeparated branch target
    inside map₁ map₂ compilation.frame frameComputed nonroot
    (fun index parentCursor =>
      separated compilation.frame compilation.frameComputed index parentCursor)
    agree

theorem ruleMajorDescriptorExec?_eq_of_cyclicRootBranch
    (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (branch target : input.certified.LocalizedCIPOccurrence (carrierFuel input))
    (inside : input.certified.RootBranchContains branch target)
    (nonroot : target.1.address ≠ [])
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.1 = unit.1)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.certified.moleculeGraph))
    (separated : ∀ frame, input.certified.localizedNoDoubleFourLigandFrameExec? target =
        some frame →
      ∀ index, IsLocalizedActualFrameParentCursor input.certified target
          (frame.cursorAt index) →
        input.certified.ArmConstitutionalRule1aSeparated frame index)
    (agree : ∀ unit, input.certified.OccurrenceUnitExtendsRootBranch branch unit.1 →
      map₁ unit = map₂ unit) :
    input.certified.ruleMajorDescriptorExec? target
        (input.certified.molecularView map₁ target) =
      input.certified.ruleMajorDescriptorExec? target
        (input.certified.molecularView map₂ target) := by
  rw [input.certified.ruleMajorDescriptorExec?_eq target
      (input.certified.molecularView map₁ target),
    input.certified.ruleMajorDescriptorExec?_eq target
      (input.certified.molecularView map₂ target)]
  exact ruleMajorDescriptor?_eq_of_cyclicRootBranch input singleBonded branch target
    inside nonroot real unit targetUnit map₁ map₂ separated agree

end LocalizedRuleMajorReference

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RootBranchContains
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OccurrenceUnitExtendsRootBranch
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.history_suffix_of_rootBranch
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.occurrenceUnit_extends_of_rootBranch
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.outwardReachable_rootBranch
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.outwardConsult_unit_extends_rootBranch
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualFrame_parentIndex
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rootAddress_no_parentIndex
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajorDescriptor?_eq_of_rootBranchParentSeparated
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajorDescriptorExec?_eq_of_rootBranchParentSeparated
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajorDescriptor?_eq_of_missingCenter
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajorDescriptorExec?_eq_of_missingCenter
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajorDescriptor?_eq_of_not_realTarget
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajorDescriptorExec?_eq_of_not_realTarget
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajorDescriptor?_eq_of_missingFrame
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajorDescriptorExec?_eq_of_missingFrame
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ruleMajorDescriptor?_eq_of_cyclicRootBranch
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ruleMajorDescriptorExec?_eq_of_cyclicRootBranch
