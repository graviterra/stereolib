import TetraStereo.OneCenter.SmilesTetrahedral
import TetraStereo.OneCenter.LocalizedGenericMarkedRecalculation
import TetraStereo.OneCenter.LocalizedContextCyclicReaderBridge
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# A raw auxiliary state read at retained carrier occurrences

The experimental marked evaluator stores its generated facts in a raw `OccurrenceAuxState`: each
fact is keyed by the raw occurrence history (current atom first, original root last) and the raw
provenance. The retained-context machinery reads labels through `molecularReader`, which consults a
`DescriptorMap` indexed by detected occurrence units `⟨root, path⟩`. Those two coordinates are the
same data: the raw history of a real occurrence is `(root :: path).reverse`.

This module defines the executable adapter. `rawStateDescriptorMap` assigns every detected unit the
tetrahedral descriptor of the raw fact stored at its exact history (`R`/`S` for uppercase facts,
`r`/`s` for lowercase facts), or nothing. `rawStateView` and `rawStateReader` are the executable
dependency view and reader of that state at one target. They are proved equal, as functions, to
`molecularView` and `molecularReader` of that descriptor map, so every retained-context theorem
stated for an arbitrary tetrahedral molecular reader applies to a raw state. At a real detected
carrier cursor that is a strict depth dependency of the target, the reader is exactly the raw
`factAt?` lookup of the history-matched raw node, and the marked evaluator's own `factOf` facts
read back as their labels.

This is a *filtered* molecular reading of the raw state, not an equality with the raw occurrence
operations: both paths reject non-real provenance. This reader additionally discards facts at
non-detected or non-dependency occurrences (including a fact stored at the target itself), which
the raw `occurrenceNodePriority` can read.
Agreement with actual generated snapshots therefore needs a separate derivation that queried raw
facts sit at detected real occurrences strictly deeper than the target.

Scope: the raw state is an arbitrary fixed list. No chemical correctness of its facts, no reference
selection, no comparison outcome and no descriptor is asserted here.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedRetainedStateReader

open CertifiedLocalizedCIPInput DeclarativeCIP

/-- The raw occurrence key of a certified occurrence unit. The raw history lists the current atom
first and ends at the original root; the certified path omits the root and runs root-to-atom. -/
def rawOccurrenceKey {n : Nat} (unit : OccurrenceUnit (Fin n)) : CanonicalOccurrenceKey :=
  { history := ((unit.root :: unit.path).reverse).map Fin.val
    provenance := RawMolecule.CanonicalNodeProvenance.realAtom }

/-- The tetrahedral descriptor of one raw fact. -/
def factDescriptor (fact : OccurrenceAuxFact) : Descriptor :=
  match fact.uppercase, fact.descriptor with
  | true, RS.R => .R
  | true, RS.S => .S
  | false, RS.R => .r
  | false, RS.S => .s

/-- The localized auxiliary label of one raw fact. -/
def factLabel (fact : OccurrenceAuxFact) : LocalizedAuxiliaryLabel :=
  if fact.uppercase then .chiral fact.descriptor
  else .pseudoasymmetric (pseudoRSOfRS fact.descriptor)

theorem factDescriptor_tetrahedral (fact : OccurrenceAuxFact) :
    (factDescriptor fact).IsTetrahedral := by
  rcases fact with ⟨key, atom, descriptor, uppercase, positions⟩
  cases uppercase <;> cases descriptor <;> trivial

theorem factDescriptor_toLocalizedLabel (fact : OccurrenceAuxFact) :
    (factDescriptor fact).toLocalizedLabel = some (factLabel fact) := by
  rcases fact with ⟨key, atom, descriptor, uppercase, positions⟩
  cases uppercase <;> cases descriptor <;> rfl

/-- The marked evaluator's own fact at a node reads back as the label it recorded. -/
theorem factLabel_factOf (node : RawMolecule.CanonicalBranchNode)
    (label : LocalizedTetrahedralRSPseudoDescriptor) :
    factLabel (LocalizedGenericMarkedRecalculation.factOf node label) = label := by
  cases label with
  | chiral raw => rfl
  | pseudoasymmetric pseudo => cases pseudo <;> rfl

/-- The raw fact stored at one occurrence unit, if any. -/
def rawStateFact? (state : OccurrenceAuxState) {n : Nat} (unit : OccurrenceUnit (Fin n)) :
    Option OccurrenceAuxFact :=
  state.find? fun fact => fact.key == rawOccurrenceKey unit

/-- The label read from a raw state at one occurrence unit. -/
def rawStateLabel? (state : OccurrenceAuxState) {n : Nat} (unit : OccurrenceUnit (Fin n)) :
    Option LocalizedAuxiliaryLabel :=
  (rawStateFact? state unit).map factLabel

variable (input : CertifiedLocalizedCIPInput)

/-- The descriptor map determined by a raw auxiliary state on the certified input's detected
occurrence units. -/
def rawStateDescriptorMap (state : OccurrenceAuxState) :
    DescriptorMap (DetectedOccurrence input.moleculeGraph) :=
  fun unit => (rawStateFact? state unit.1).map factDescriptor

theorem rawStateDescriptorMap_tetrahedral (state : OccurrenceAuxState) :
    ∀ unit value, rawStateDescriptorMap input state unit = some value → value.IsTetrahedral := by
  intro unit value observed
  unfold rawStateDescriptorMap at observed
  obtain ⟨fact, _, rfl⟩ := Option.map_eq_some_iff.1 observed
  exact factDescriptor_tetrahedral fact

theorem rawStateDescriptorMap_bind (state : OccurrenceAuxState)
    (unit : DetectedOccurrence input.moleculeGraph) :
    (rawStateDescriptorMap input state unit).bind Descriptor.toLocalizedLabel =
      rawStateLabel? state unit.1 := by
  unfold rawStateDescriptorMap rawStateLabel?
  cases rawStateFact? state unit.1 with
  | none => rfl
  | some fact => simp [factDescriptor_toLocalizedLabel]

/-- Executable dependency view of a raw state at one target: real detected sources read the raw
fact at their exact unit, every other source reads nothing. -/
def rawStateView (state : OccurrenceAuxState) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) : input.LocalizedDependencyView target :=
  fun source _ =>
    if source.1.node.provenance = OfficialCIPNodeProvenance.realAtom then
      if IsDetectedCenter input.moleculeGraph (input.molecularFrameUnit source.1).atom then
        rawStateLabel? state (input.molecularFrameUnit source.1)
      else none
    else none

/-- The executable view is the molecular view of the raw-state descriptor map. -/
theorem rawStateView_eq_molecularView (state : OccurrenceAuxState) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) :
    rawStateView input state target = input.molecularView (rawStateDescriptorMap input state) target := by
  funext source dependency
  unfold rawStateView molecularView
  by_cases real : source.1.node.provenance = OfficialCIPNodeProvenance.realAtom
  · rw [if_pos real, if_pos real]
    by_cases detected :
        IsDetectedCenter input.moleculeGraph (input.molecularFrameUnit source.1).atom
    · rw [if_pos detected, dif_pos detected, rawStateDescriptorMap_bind]
    · rw [if_neg detected, dif_neg detected]
  · rw [if_neg real, if_neg real]

/-- Executable reader of a raw state at one target: the production dependency reader specialized
to the raw-state view. -/
def rawStateReader (state : OccurrenceAuxState) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) :
    input.LocalizedRerootCursor fuel → Option LocalizedAuxiliaryLabel :=
  input.localizedDependencyLabel target (rawStateView input state target)

/-- **The raw-state reader is the molecular reader of the raw-state descriptor map.** -/
theorem rawStateReader_eq_molecularReader (state : OccurrenceAuxState) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) :
    rawStateReader input state target =
      input.molecularReader (rawStateDescriptorMap input state) target := by
  unfold rawStateReader molecularReader
  rw [rawStateView_eq_molecularView]

/-! ## Readback at raw nodes -/

private theorem reverse_cons_tail_of_getLast {α : Type} {history : List α} {root : α}
    (last : history.getLast? = some root) :
    (root :: history.reverse.tail).reverse = history := by
  have nonempty : history ≠ [] := by
    intro empty
    simp [empty] at last
  have headEq : history.reverse.head? = some root := by
    have raw := (List.getLast?_reverse (l := history.reverse)).symm
    rw [List.reverse_reverse] at raw
    exact raw.trans last
  have cons : history.reverse = root :: history.reverse.tail := by
    cases reverseEq : history.reverse with
    | nil =>
        exact absurd (by simpa using congrArg List.reverse reverseEq) nonempty
    | cons head tail =>
        have headRoot : head = root := by
          have headSome : history.reverse.head? = some head := by simp [reverseEq]
          exact Option.some.inj (headSome.symm.trans headEq)
        subst headRoot
        rfl
  rw [← cons, List.reverse_reverse]

/-- A raw node with the certified history and real provenance has the raw key of the certified
unit. The only requirement is that the certified history ends at its stored root. -/
theorem rawOccurrenceKey_eq_canonicalOccurrenceKey {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (last : occurrence.1.node.history.getLast? = some occurrence.1.root)
    (node : RawMolecule.CanonicalBranchNode)
    (historyEq : node.history = occurrence.1.node.history.map Fin.val)
    (real : node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom) :
    rawOccurrenceKey (input.molecularFrameUnit occurrence.1) = canonicalOccurrenceKey node := by
  unfold rawOccurrenceKey canonicalOccurrenceKey molecularFrameUnit
  rw [historyEq, real]
  simp only [reverse_cons_tail_of_getLast last]

/-- At a history-matched real raw node, the unit lookup is the raw `factAt?` lookup. -/
theorem rawStateFact?_eq_factAt? (state : OccurrenceAuxState) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (last : occurrence.1.node.history.getLast? = some occurrence.1.root)
    (node : RawMolecule.CanonicalBranchNode)
    (historyEq : node.history = occurrence.1.node.history.map Fin.val)
    (real : node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom) :
    rawStateFact? state (input.molecularFrameUnit occurrence.1) = state.factAt? node := by
  unfold rawStateFact? OccurrenceAuxState.factAt?
  rw [rawOccurrenceKey_eq_canonicalOccurrenceKey input occurrence last node historyEq real]

/-- The reader at a real detected dependency reads the unit's raw label. -/
theorem rawStateReader_of_real (state : OccurrenceAuxState) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (cursor : input.LocalizedRerootCursor fuel)
    (dependency : input.LocalizedDepthDependency cursor.occurrence target)
    (real : cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (detected : IsDetectedCenter input.moleculeGraph
      (input.molecularFrameUnit cursor.occurrence.1).atom) :
    rawStateReader input state target cursor =
      rawStateLabel? state (input.molecularFrameUnit cursor.occurrence.1) := by
  unfold rawStateReader localizedDependencyLabel rawStateView
  rw [dif_pos dependency, if_pos real, if_pos detected]

/-- A non-real cursor, including a ring-duplicate leaf, reads nothing. -/
theorem rawStateReader_of_not_real (state : OccurrenceAuxState) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (cursor : input.LocalizedRerootCursor fuel)
    (notReal : cursor.occurrence.1.node.provenance ≠ OfficialCIPNodeProvenance.realAtom) :
    rawStateReader input state target cursor = none := by
  unfold rawStateReader localizedDependencyLabel rawStateView
  by_cases dependency : input.LocalizedDepthDependency cursor.occurrence target
  · rw [dif_pos dependency, if_neg notReal]
  · rw [dif_neg dependency]

/-- A cursor outside the target's strict dependencies reads nothing. -/
theorem rawStateReader_of_not_dependency (state : OccurrenceAuxState) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (cursor : input.LocalizedRerootCursor fuel)
    (notDependency : ¬ input.LocalizedDepthDependency cursor.occurrence target) :
    rawStateReader input state target cursor = none := by
  unfold rawStateReader localizedDependencyLabel
  rw [dif_neg notDependency]

/-- **Raw readback on a simple-bonded carrier.** At a real detected dependency whose raw node has
the certified history, the retained reader returns the label of the raw `factAt?` fact. -/
theorem rawStateReader_eq_factAt?_label (singleBonded : input.moleculeGraph.SimpleBonded)
    (state : OccurrenceAuxState) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (cursor : input.LocalizedRerootCursor fuel)
    (dependency : input.LocalizedDepthDependency cursor.occurrence target)
    (real : cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (detected : IsDetectedCenter input.moleculeGraph
      (input.molecularFrameUnit cursor.occurrence.1).atom)
    (node : RawMolecule.CanonicalBranchNode)
    (historyEq : node.history = cursor.occurrence.1.node.history.map Fin.val)
    (rawReal : node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom) :
    rawStateReader input state target cursor = (state.factAt? node).map factLabel := by
  rw [rawStateReader_of_real input state target cursor dependency real detected]
  unfold rawStateLabel?
  rw [rawStateFact?_eq_factAt? input state cursor.occurrence
    (input.carrierOccurrence_history_getLast_eq_root singleBonded cursor.occurrence) node
    historyEq rawReal]

end TetraStereo.OneCenter.LocalizedMarkedRetainedStateReader

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedStateReader.factDescriptor_tetrahedral
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedStateReader.factDescriptor_toLocalizedLabel
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedStateReader.factLabel_factOf
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedStateReader.rawStateDescriptorMap_tetrahedral
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedStateReader.rawStateDescriptorMap_bind
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedStateReader.rawStateView_eq_molecularView
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedStateReader.rawStateReader_eq_molecularReader
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedStateReader.rawOccurrenceKey_eq_canonicalOccurrenceKey
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedStateReader.rawStateFact?_eq_factAt?
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedStateReader.rawStateReader_of_real
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedStateReader.rawStateReader_of_not_real
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedStateReader.rawStateReader_of_not_dependency
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedStateReader.rawStateReader_eq_factAt?_label
