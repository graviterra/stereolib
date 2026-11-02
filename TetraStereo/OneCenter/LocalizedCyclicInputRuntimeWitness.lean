import TetraStereo.OneCenter.LocalizedCyclicInputWitness
import TetraStereo.OneCenter.LocalizedCyclicContextFrameCompilation
import TetraStereo.OneCenter.LocalizedContextCyclicReaderBridge
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-!
# Standard-fuel runtime instantiation of the approved cyclic input

The approved witness places the real root, the detected centers at atoms 2 and 4, and the
terminal `ringDuplicate` in `localizedOccurrences` at fuel `atomCount`. The rule-major runtime
uses `LocalizedRuleMajorReference.carrierFuel`, which is `atomCount + 1`.

`carrierOccurrence_legitimate` keeps the same root, address, and node.
`legitimateOccurrence_mem_localizedOccurrences_of_fuel` places that node at every fuel covering
the address. Their composition is the lift below. Frame compilation and the cyclic reader are
the accepted generic theorems: this file does not execute the reference fixed point and does not
emit a closed `R`/`S` label.

The parser converter leaves `AuthoritativeChemicalInput.spatial?` absent. A later nontrivial
descriptor example needs `spatial? = some { positions : List CartesianPoint3 }` with one point
per expanded atom. This module does not invent those points.
-/

namespace TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness

open TetraStereo.OneCenter
open LocalizedCyclicInputWitness
open LocalizedRuleMajorReference
open CertifiedLocalizedCIPInput
open DeclarativeCIP

noncomputable section

/-- A carrier occurrence remains the same root, address, and node at every larger fuel that
covers its address. The remaining depth is the sharp budget `higher + 1 - address.length`. -/
theorem localizedCarrier_persists_at_fuel
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    {low higher : Nat}
    (occurrence : input.LocalizedCIPOccurrence low)
    (enough : occurrence.1.address.length ≤ higher) :
    { root := occurrence.1.root
      address := occurrence.1.address
      node := occurrence.1.node
      remaining := higher + 1 - occurrence.1.address.length } ∈
      input.localizedOccurrences higher :=
  input.legitimateOccurrence_mem_localizedOccurrences_of_fuel
    (input.carrierOccurrence_legitimate singleBonded occurrence) enough

theorem carrierFuel_eq :
    carrierFuel cyclicReferenceInput =
      cyclicCertified.certified.input.molecule.atomCount + 1 :=
  rfl

theorem standardFuel_eq_ten : carrierFuel cyclicReferenceInput = 10 := by
  rw [carrierFuel_eq, atomCount_eq]

/-- The approved nine-atom source has no three-dimensional coordinate channel. -/
theorem source_spatial_absent : cyclicSource.spatial? = none := by
  cases semanticObserved : cyclicExpanded.toSemanticMolecule? with
  | none =>
      simp [cyclicSource, RawMolecule.toAuthoritativeChemicalInput?, semanticObserved]
  | some _ =>
      simp [cyclicSource, RawMolecule.toAuthoritativeChemicalInput?, semanticObserved]

/-- The parser diagram on this source also carries no drawing coordinates. -/
theorem source_diagram_coordinates_absent :
    ∀ diagram, cyclicSource.diagram? = some diagram → diagram.atomPositions? = none := by
  intro diagram observed
  have diagramEq :=
    cyclicExpanded.toAuthoritativeChemicalInput?_diagram cyclicSource source_conversion
  have same : diagram = cyclicExpanded.toDiagramConfiguration :=
    Option.some.inj (observed.symm.trans diagramEq)
  subst same
  rfl

def standardOf
    (occurrence : cyclicCertified.LocalizedCIPOccurrence
      cyclicCertified.certified.input.molecule.atomCount) :
    Occurrence cyclicReferenceInput :=
  ⟨{ root := occurrence.1.root
     address := occurrence.1.address
     node := occurrence.1.node
     remaining := carrierFuel cyclicReferenceInput + 1 - occurrence.1.address.length },
   by
     have legit := cyclicCertified.carrierOccurrence_legitimate input_simpleBonded occurrence
     exact localizedCarrier_persists_at_fuel cyclicCertified input_simpleBonded occurrence
       (Nat.le_succ_of_le
         (cyclicCertified.legitimateOccurrence_address_length_le_atomCount legit))⟩

theorem standardOf_root
    (occurrence : cyclicCertified.LocalizedCIPOccurrence
      cyclicCertified.certified.input.molecule.atomCount) :
    (standardOf occurrence).1.root = occurrence.1.root :=
  rfl

theorem standardOf_address
    (occurrence : cyclicCertified.LocalizedCIPOccurrence
      cyclicCertified.certified.input.molecule.atomCount) :
    (standardOf occurrence).1.address = occurrence.1.address :=
  rfl

theorem standardOf_node
    (occurrence : cyclicCertified.LocalizedCIPOccurrence
      cyclicCertified.certified.input.molecule.atomCount) :
    (standardOf occurrence).1.node = occurrence.1.node :=
  rfl

theorem standardOf_history
    (occurrence : cyclicCertified.LocalizedCIPOccurrence
      cyclicCertified.certified.input.molecule.atomCount) :
    (standardOf occurrence).1.node.history = occurrence.1.node.history :=
  rfl

theorem standardOf_provenance
    (occurrence : cyclicCertified.LocalizedCIPOccurrence
      cyclicCertified.certified.input.molecule.atomCount) :
    (standardOf occurrence).1.node.provenance = occurrence.1.node.provenance :=
  rfl

theorem standardOf_current
    (occurrence : cyclicCertified.LocalizedCIPOccurrence
      cyclicCertified.certified.input.molecule.atomCount) :
    (standardOf occurrence).1.node.current? = occurrence.1.node.current? :=
  rfl

theorem standardOf_remaining
    (occurrence : cyclicCertified.LocalizedCIPOccurrence
      cyclicCertified.certified.input.molecule.atomCount) :
    (standardOf occurrence).1.remaining = occurrence.1.remaining + 1 := by
  have derived :=
    (cyclicCertified.mem_localizedOccurrences_iff
      cyclicCertified.certified.input.molecule.atomCount occurrence.1).mp occurrence.2
  have grade := cyclicCertified.declarativeLocalizedOccurrence_depthGrade derived
  have bound :=
    cyclicCertified.legitimateOccurrence_address_length_le_atomCount
      (cyclicCertified.carrierOccurrence_legitimate input_simpleBonded occurrence)
  have lifted :
      (standardOf occurrence).1.remaining =
        cyclicCertified.certified.input.molecule.atomCount + 1 + 1 -
          occurrence.1.address.length :=
    rfl
  omega

theorem standardOf_recognizer
    (occurrence : cyclicCertified.LocalizedCIPOccurrence
      cyclicCertified.certified.input.molecule.atomCount) :
    cyclicReferenceInput.certified.localizedOccurrenceDescriptorCenter? (standardOf occurrence) =
      cyclicCertified.localizedOccurrenceDescriptorCenter? occurrence :=
  rfl

abbrev standardRoot : Occurrence cyclicReferenceInput := standardOf rootOccurrence
abbrev standardArm : Occurrence cyclicReferenceInput := standardOf armOccurrence
abbrev standardClosing : Occurrence cyclicReferenceInput := standardOf closingOccurrence
abbrev standardDuplicate : Occurrence cyclicReferenceInput := standardOf duplicateOccurrence

theorem standardRoot_source : standardRoot.1.root = A0 := by
  rw [standardOf_root]
  exact rootRecognized.2.2.2.1

theorem standardRoot_address : standardRoot.1.address = [] := by
  rw [standardOf_address]
  exact rootRecognized.2.2.1

theorem standardRoot_history : standardRoot.1.node.history = [A0] := by
  have derived :=
    (cyclicCertified.mem_localizedOccurrences_iff _ standardRoot.1).mp standardRoot.2
  have frameEq :=
    cyclicCertified.declarativeLocalizedOccurrence_eq_root_of_address_nil derived
      standardRoot_address
  have nodeEq : standardRoot.1.node = OfficialCIPNode.root standardRoot.1.root :=
    congrArg LocalizedCIPOccurrenceFrame.node frameEq
  rw [nodeEq, standardRoot_source]
  rfl

theorem standardRoot_provenance :
    standardRoot.1.node.provenance = OfficialCIPNodeProvenance.realAtom := by
  rw [standardOf_provenance]
  exact ((cyclicCertified.localizedOccurrenceDescriptorCenter?_eq_some_iff rootOccurrence
    rootCenter).mp rootRecognized.1).1

theorem standardRoot_current : standardRoot.1.node.current? = some A0 := by
  rw [standardOf_current]
  have current :=
    ((cyclicCertified.localizedOccurrenceDescriptorCenter?_eq_some_iff rootOccurrence
      rootCenter).mp rootRecognized.1).2
  rw [rootRecognized.2.1] at current
  exact current

theorem standardRoot_recognizer :
    cyclicReferenceInput.certified.localizedOccurrenceDescriptorCenter? standardRoot =
      some rootCenter := by
  rw [standardOf_recognizer]
  exact rootRecognized.1

private theorem frameAtom_of_current
    (occurrence : Occurrence cyclicReferenceInput) {atom : cyclicCertified.Atom}
    (current : occurrence.1.node.current? = some atom) :
    (cyclicCertified.molecularFrameUnit occurrence.1).atom = atom := by
  obtain ⟨cursorAtom, cursorCurrent⟩ :=
    cyclicCertified.localizedRerootCursor_current_exists
      (⟨occurrence, none⟩ :
        cyclicCertified.LocalizedRerootCursor (carrierFuel cyclicReferenceInput))
  have cursorEq : cursorAtom = atom := by
    rw [cursorCurrent] at current
    exact Option.some.inj current
  have derived :=
    (cyclicCertified.mem_localizedOccurrences_iff _ occurrence.1).mp occurrence.2
  have headEq :=
    cyclicCertified.declarativeLocalizedOccurrence_node_history_head_eq_current derived
  have head : occurrence.1.node.history.head? = some cursorAtom := by
    rw [cursorCurrent] at headEq
    exact headEq
  have last :=
    cyclicCertified.carrierOccurrence_history_getLast_eq_root input_simpleBonded occurrence
  rw [cyclicCertified.molecularFrameUnit_atom_eq_current occurrence.1 head last, cursorEq]

private theorem root_center_detected :
    IsDetectedCenter cyclicCertified.moleculeGraph
      (cyclicCertified.molecularFrameUnit standardRoot.1).atom := by
  rw [frameAtom_of_current standardRoot standardRoot_current]
  exact degreeFourCentersOnCycle.1

def rootDetectedUnit : DetectedOccurrence cyclicCertified.moleculeGraph :=
  ⟨cyclicCertified.molecularFrameUnit standardRoot.1, root_center_detected⟩

theorem standardRoot_unit :
    rootDetectedUnit.1 = (⟨A0, []⟩ : OccurrenceUnit cyclicCertified.Atom) := by
  have spec : rootDetectedUnit.1 =
      ⟨standardRoot.1.root, standardRoot.1.node.history.reverse.tail⟩ :=
    rfl
  rw [spec, standardRoot_source, standardRoot_history]
  rfl

theorem standardRoot_unit_target :
    cyclicReferenceInput.certified.molecularFrameUnit standardRoot.1 = rootDetectedUnit.1 :=
  rfl

def standardRootCompilation :
    ContextFrameCompilation cyclicReferenceInput standardRoot rootDetectedUnit
      standardRoot_unit_target :=
  cyclicContextFrameCompilation cyclicReferenceInput input_simpleBonded standardRoot
    standardRoot_provenance rootDetectedUnit standardRoot_unit_target

theorem standardRoot_frame_stage_compound :
    cyclicReferenceInput.certified.localizedOccurrenceDescriptorCenter? standardRoot =
      some standardRootCompilation.center ∧
    standardRootCompilation.center = rootCenter ∧
    cyclicReferenceInput.certified.localizedNoDoubleFourLigandFrameExec? standardRoot =
      some standardRootCompilation.frame ∧
    (∀ index,
      cyclicReferenceInput.certified.buildActualRuleMajorCompoundRule45KeyExec? standardRoot
        (contextOccurrenceView cyclicReferenceInput standardRoot)
        (2 * (carrierFuel cyclicReferenceInput + 1))
        (standardRootCompilation.frame.cursorAt index) =
        some (standardRootCompilation.compounds index)) ∧
    (∀ index, (standardRootCompilation.stages index).widthBound ≤
      standardRootCompilation.W) ∧
    (∀ index, (standardRootCompilation.stages index).depthBound ≤
      standardRootCompilation.D) := by
  refine ⟨standardRootCompilation.centerComputed, ?_, standardRootCompilation.frameComputed,
    standardRootCompilation.compoundBuilt, standardRootCompilation.widthBound,
    standardRootCompilation.depthBound⟩
  have computed := standardRootCompilation.centerComputed
  rw [standardRoot_recognizer] at computed
  exact (Option.some.inj computed).symm

theorem standardArm_source : standardArm.1.root = A0 := by
  rw [standardOf_root]
  exact armRecognizedNonroot.2.2.2.2.1

theorem standardArm_address : standardArm.1.address ≠ [] := by
  rw [standardOf_address]
  exact armRecognizedNonroot.2.2.2.1

theorem standardArm_distinct : A2 ≠ A0 :=
  armRecognizedNonroot.2.2.1

private theorem standardArm_current_source :
    armOccurrence.1.node.current? = some A2 := by
  have current :=
    ((cyclicCertified.localizedOccurrenceDescriptorCenter?_eq_some_iff armOccurrence
      armCenter).mp armRecognizedNonroot.1).2
  rw [armRecognizedNonroot.2.1] at current
  exact current

theorem standardArm_history :
    standardArm.1.node.history = armOccurrence.1.node.history ∧
    standardArm.1.node.history.head? = some A2 ∧
    standardArm.1.node.history.getLast? = some A0 := by
  refine ⟨standardOf_history armOccurrence, ?_, ?_⟩
  · have headEq :=
      cyclicCertified.declarativeLocalizedOccurrence_node_history_head_eq_current
        ((cyclicCertified.mem_localizedOccurrences_iff _ standardArm.1).mp standardArm.2)
    rw [headEq, standardOf_current, standardArm_current_source]
  · rw [cyclicCertified.carrierOccurrence_history_getLast_eq_root input_simpleBonded standardArm,
      standardArm_source]

theorem standardArm_provenance :
    standardArm.1.node.provenance = OfficialCIPNodeProvenance.realAtom := by
  rw [standardOf_provenance]
  exact ((cyclicCertified.localizedOccurrenceDescriptorCenter?_eq_some_iff armOccurrence
    armCenter).mp armRecognizedNonroot.1).1

theorem standardArm_current : standardArm.1.node.current? = some A2 := by
  rw [standardOf_current]
  exact standardArm_current_source

theorem standardArm_recognizer :
    cyclicReferenceInput.certified.localizedOccurrenceDescriptorCenter? standardArm =
      some armCenter := by
  rw [standardOf_recognizer]
  exact armRecognizedNonroot.1

private theorem arm_center_detected :
    IsDetectedCenter cyclicCertified.moleculeGraph
      (cyclicCertified.molecularFrameUnit standardArm.1).atom := by
  rw [frameAtom_of_current standardArm standardArm_current]
  exact degreeFourCentersOnCycle.2.1

def armDetectedUnit : DetectedOccurrence cyclicCertified.moleculeGraph :=
  ⟨cyclicCertified.molecularFrameUnit standardArm.1, arm_center_detected⟩

theorem standardArm_unit :
    armDetectedUnit.1 = cyclicCertified.molecularFrameUnit standardArm.1 ∧
    armDetectedUnit.1.root = A0 ∧
    armDetectedUnit.1.atom = A2 := by
  refine ⟨rfl, ?_, ?_⟩
  · have spec : armDetectedUnit.1.root = standardArm.1.root := rfl
    rw [spec, standardArm_source]
  · simpa [armDetectedUnit] using frameAtom_of_current standardArm standardArm_current

theorem standardArm_unit_target :
    cyclicReferenceInput.certified.molecularFrameUnit standardArm.1 = armDetectedUnit.1 :=
  rfl

def standardArmCompilation :
    ContextFrameCompilation cyclicReferenceInput standardArm armDetectedUnit
      standardArm_unit_target :=
  cyclicContextFrameCompilation cyclicReferenceInput input_simpleBonded standardArm
    standardArm_provenance armDetectedUnit standardArm_unit_target

theorem standardArm_frame_stage_compound :
    cyclicReferenceInput.certified.localizedOccurrenceDescriptorCenter? standardArm =
      some standardArmCompilation.center ∧
    standardArmCompilation.center = armCenter ∧
    cyclicReferenceInput.certified.localizedNoDoubleFourLigandFrameExec? standardArm =
      some standardArmCompilation.frame ∧
    (∀ index,
      cyclicReferenceInput.certified.buildActualRuleMajorCompoundRule45KeyExec? standardArm
        (contextOccurrenceView cyclicReferenceInput standardArm)
        (2 * (carrierFuel cyclicReferenceInput + 1))
        (standardArmCompilation.frame.cursorAt index) =
        some (standardArmCompilation.compounds index)) ∧
    (∀ index, (standardArmCompilation.stages index).widthBound ≤ standardArmCompilation.W) ∧
    (∀ index, (standardArmCompilation.stages index).depthBound ≤ standardArmCompilation.D) := by
  refine ⟨standardArmCompilation.centerComputed, ?_, standardArmCompilation.frameComputed,
    standardArmCompilation.compoundBuilt, standardArmCompilation.widthBound,
    standardArmCompilation.depthBound⟩
  have computed := standardArmCompilation.centerComputed
  rw [standardArm_recognizer] at computed
  exact (Option.some.inj computed).symm

theorem standardClosing_source : standardClosing.1.root = A0 := by
  rw [standardOf_root]
  exact closingRecognizedNonroot.2.2.2.2.1

theorem standardClosing_address : standardClosing.1.address ≠ [] := by
  rw [standardOf_address]
  exact closingRecognizedNonroot.2.2.2.1

theorem standardClosing_distinct : A4 ≠ A0 :=
  closingRecognizedNonroot.2.2.1

private theorem standardClosing_current_source :
    closingOccurrence.1.node.current? = some A4 := by
  have current :=
    ((cyclicCertified.localizedOccurrenceDescriptorCenter?_eq_some_iff closingOccurrence
      closingCenter).mp closingRecognizedNonroot.1).2
  rw [closingRecognizedNonroot.2.1] at current
  exact current

theorem standardClosing_history :
    standardClosing.1.node.history = closingOccurrence.1.node.history ∧
    standardClosing.1.node.history.head? = some A4 ∧
    standardClosing.1.node.history.getLast? = some A0 := by
  refine ⟨standardOf_history closingOccurrence, ?_, ?_⟩
  · have headEq :=
      cyclicCertified.declarativeLocalizedOccurrence_node_history_head_eq_current
        ((cyclicCertified.mem_localizedOccurrences_iff _ standardClosing.1).mp standardClosing.2)
    rw [headEq, standardOf_current, standardClosing_current_source]
  · rw [cyclicCertified.carrierOccurrence_history_getLast_eq_root input_simpleBonded
        standardClosing, standardClosing_source]

theorem standardClosing_provenance :
    standardClosing.1.node.provenance = OfficialCIPNodeProvenance.realAtom := by
  rw [standardOf_provenance]
  exact ((cyclicCertified.localizedOccurrenceDescriptorCenter?_eq_some_iff closingOccurrence
    closingCenter).mp closingRecognizedNonroot.1).1

theorem standardClosing_current : standardClosing.1.node.current? = some A4 := by
  rw [standardOf_current]
  exact standardClosing_current_source

theorem standardClosing_recognizer :
    cyclicReferenceInput.certified.localizedOccurrenceDescriptorCenter? standardClosing =
      some closingCenter := by
  rw [standardOf_recognizer]
  exact closingRecognizedNonroot.1

private theorem closing_center_detected :
    IsDetectedCenter cyclicCertified.moleculeGraph
      (cyclicCertified.molecularFrameUnit standardClosing.1).atom := by
  rw [frameAtom_of_current standardClosing standardClosing_current]
  exact degreeFourCentersOnCycle.2.2.1

def closingDetectedUnit : DetectedOccurrence cyclicCertified.moleculeGraph :=
  ⟨cyclicCertified.molecularFrameUnit standardClosing.1, closing_center_detected⟩

theorem standardClosing_unit :
    closingDetectedUnit.1 = cyclicCertified.molecularFrameUnit standardClosing.1 ∧
    closingDetectedUnit.1.root = A0 ∧
    closingDetectedUnit.1.atom = A4 := by
  refine ⟨rfl, ?_, ?_⟩
  · have spec : closingDetectedUnit.1.root = standardClosing.1.root := rfl
    rw [spec, standardClosing_source]
  · simpa [closingDetectedUnit] using
      frameAtom_of_current standardClosing standardClosing_current

theorem standardClosing_unit_target :
    cyclicReferenceInput.certified.molecularFrameUnit standardClosing.1 =
      closingDetectedUnit.1 :=
  rfl

def standardClosingCompilation :
    ContextFrameCompilation cyclicReferenceInput standardClosing closingDetectedUnit
      standardClosing_unit_target :=
  cyclicContextFrameCompilation cyclicReferenceInput input_simpleBonded standardClosing
    standardClosing_provenance closingDetectedUnit standardClosing_unit_target

theorem standardClosing_frame_stage_compound :
    cyclicReferenceInput.certified.localizedOccurrenceDescriptorCenter? standardClosing =
      some standardClosingCompilation.center ∧
    standardClosingCompilation.center = closingCenter ∧
    cyclicReferenceInput.certified.localizedNoDoubleFourLigandFrameExec? standardClosing =
      some standardClosingCompilation.frame ∧
    (∀ index,
      cyclicReferenceInput.certified.buildActualRuleMajorCompoundRule45KeyExec?
        standardClosing
        (contextOccurrenceView cyclicReferenceInput standardClosing)
        (2 * (carrierFuel cyclicReferenceInput + 1))
        (standardClosingCompilation.frame.cursorAt index) =
        some (standardClosingCompilation.compounds index)) ∧
    (∀ index, (standardClosingCompilation.stages index).widthBound ≤
      standardClosingCompilation.W) ∧
    (∀ index, (standardClosingCompilation.stages index).depthBound ≤
      standardClosingCompilation.D) := by
  refine ⟨standardClosingCompilation.centerComputed, ?_,
    standardClosingCompilation.frameComputed, standardClosingCompilation.compoundBuilt,
    standardClosingCompilation.widthBound, standardClosingCompilation.depthBound⟩
  have computed := standardClosingCompilation.centerComputed
  rw [standardClosing_recognizer] at computed
  exact (Option.some.inj computed).symm

theorem standardDuplicate_source : standardDuplicate.1.root = A0 := by
  rw [standardOf_root]
  exact ringDuplicateCarrier.2.2.2.1

theorem standardDuplicate_address : standardDuplicate.1.address ≠ [] := by
  rw [standardOf_address]
  exact ringDuplicateCarrier.2.2.1

theorem standardDuplicate_provenance :
    standardDuplicate.1.node.provenance = OfficialCIPNodeProvenance.ringDuplicate 0 := by
  rw [standardOf_provenance]
  exact ringDuplicateCarrier.1

theorem standardDuplicate_current : standardDuplicate.1.node.current? = some A0 := by
  rw [standardOf_current]
  exact ringDuplicateCarrier.2.1

theorem standardDuplicate_history :
    standardDuplicate.1.node.history = duplicateOccurrence.1.node.history ∧
    standardDuplicate.1.node.history.head? = some A0 ∧
    standardDuplicate.1.node.history.getLast? = some A0 := by
  refine ⟨standardOf_history duplicateOccurrence, ?_, ?_⟩
  · have headEq :=
      cyclicCertified.declarativeLocalizedOccurrence_node_history_head_eq_current
        ((cyclicCertified.mem_localizedOccurrences_iff _ standardDuplicate.1).mp
          standardDuplicate.2)
    rw [headEq, standardDuplicate_current]
  · rw [cyclicCertified.carrierOccurrence_history_getLast_eq_root input_simpleBonded
        standardDuplicate, standardDuplicate_source]

theorem standardDuplicate_notReal :
    standardDuplicate.1.node.provenance ≠ OfficialCIPNodeProvenance.realAtom := by
  intro equal
  have provenance := standardDuplicate_provenance
  rw [equal] at provenance
  cases provenance

theorem standardDuplicate_recognizer :
    cyclicReferenceInput.certified.localizedOccurrenceDescriptorCenter? standardDuplicate =
      none :=
  cyclicCertified.localizedOccurrenceDescriptorCenter?_eq_none_of_not_realAtom
    standardDuplicate standardDuplicate_notReal

theorem standardDuplicate_referenceState_none :
    referenceState cyclicReferenceInput standardDuplicate = none :=
  referenceState_none_of_not_real cyclicReferenceInput standardDuplicate
    standardDuplicate_notReal

end

assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.localizedCarrier_persists_at_fuel
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.carrierFuel_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardFuel_eq_ten
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.source_spatial_absent
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.source_diagram_coordinates_absent
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardOf_root
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardOf_address
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardOf_node
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardOf_history
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardOf_provenance
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardOf_current
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardOf_remaining
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardOf_recognizer
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardRoot_source
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardRoot_address
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardRoot_history
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardRoot_provenance
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardRoot_current
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardRoot_recognizer
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardRoot_unit
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardRoot_unit_target
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardRoot_frame_stage_compound
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardArm_source
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardArm_address
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardArm_distinct
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardArm_history
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardArm_provenance
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardArm_current
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardArm_recognizer
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardArm_unit
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardArm_unit_target
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardArm_frame_stage_compound
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardClosing_source
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardClosing_address
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardClosing_distinct
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardClosing_history
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardClosing_provenance
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardClosing_current
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardClosing_recognizer
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardClosing_unit
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardClosing_unit_target
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardClosing_frame_stage_compound
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardDuplicate_source
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardDuplicate_address
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardDuplicate_provenance
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardDuplicate_current
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardDuplicate_history
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardDuplicate_notReal
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardDuplicate_recognizer
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness.standardDuplicate_referenceState_none

end TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness
