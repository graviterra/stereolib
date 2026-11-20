import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootFrame
import TetraStereo.OneCenter.LocalizedChemicalRingCachedOperations
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Read the sparse raw fact list before testing detected-center membership. The equality
includes every failure and every raw state; the optimization supplies no auxiliary facts. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootReader

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedMarkedRetainedStateReader
open LocalizedChemicalRingJointPreparedDoubleC3ExactCarrier (input)
open LocalizedChemicalRingJointPreparedDoubleC3ExactRootSlice (reader)
open LocalizedChemicalRingJointPreparedDoubleC3ExactRootFrame (target frame)

def factFirstView (sourceInput : CertifiedLocalizedCIPInput) (state : OccurrenceAuxState)
    {fuel : Nat} (sourceTarget : sourceInput.LocalizedCIPOccurrence fuel) :
    sourceInput.LocalizedDependencyView sourceTarget :=
  fun source _ =>
    match rawStateLabel? state (sourceInput.molecularFrameUnit source.1) with
    | none => none
    | some label =>
        if source.1.node.provenance = OfficialCIPNodeProvenance.realAtom then
          if IsDetectedCenter sourceInput.moleculeGraph
              (sourceInput.molecularFrameUnit source.1).atom then some label else none
        else none

theorem factFirstView_eq (sourceInput : CertifiedLocalizedCIPInput) (state : OccurrenceAuxState)
    {fuel : Nat} (sourceTarget : sourceInput.LocalizedCIPOccurrence fuel) :
    factFirstView sourceInput state sourceTarget = rawStateView sourceInput state sourceTarget := by
  funext source dependency
  unfold factFirstView rawStateView
  cases rawStateLabel? state (sourceInput.molecularFrameUnit source.1) <;> split_ifs <;> rfl

def prior (state : OccurrenceAuxState) (cursor : input.LocalizedRerootCursor 26) :
    Option input.LocalizedRerootCompoundRule45Key :=
  let view := factFirstView input state target
  input.buildRuleMajorCompoundRule45KeyWith?
    (LocalizedChemicalRingCachedOperations.stageCompiler input reader target view
      (input.localizedDependencyLabel target view) 54) cursor

theorem prior_eq (state : OccurrenceAuxState) (cursor : input.LocalizedRerootCursor 26) :
    prior state cursor = LocalizedChemicalRingCachedOperations.compound input reader target
      (rawStateView input state target) 54 cursor := by
  simp only [prior, factFirstView_eq, LocalizedChemicalRingCachedOperations.compound]

def before (state : OccurrenceAuxState) (left right : Fin 4) : Option Ordering :=
  (do
    let leftKey ← prior state (frame.cursorAt left)
    let rightKey ← prior state (frame.cursorAt right)
    some (localizedOccurrenceRule45ComparisonRecord
      (input.compareLocalizedRerootCompoundThroughRule5 leftKey rightKey))).map
    ConstitutionalDescriptorHierarchyComparison.ordering

theorem before_eq (state : OccurrenceAuxState) (left right : Fin 4) :
    before state left right =
      LocalizedChemicalRingCachedOperations.before input reader state target frame left right := by
  simp only [before, prior_eq, LocalizedChemicalRingCachedOperations.before]
  rfl

end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootReader

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootReader.factFirstView_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootReader.prior_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootReader.before_eq
