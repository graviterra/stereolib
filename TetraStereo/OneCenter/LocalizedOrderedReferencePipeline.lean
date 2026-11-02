import TetraStereo.OneCenter.LocalizedActualOrderedEvaluatorPreservation
import TetraStereo.OneCenter.LocalizedNoDoubleDescriptorExecutable
import TetraStereo.OneCenter.LocalizedRerootCompoundOrderedBuilder
import TetraStereo.OneCenter.LocalizedRerootCompoundRule45Executable
import TetraStereo.OneCenter.LocalizedUniversalReferencePipeline

set_option autoImplicit false

namespace TetraStereo.OneCenter.LocalizedOrderedReference

open CertifiedLocalizedCIPInput
open TetraStereo.Certificate.Dependency

/-! A callable, whole-molecule runtime for the ordered bare Rule-4/5 evaluator.  The ordered
proof-facing builder is noncomputable because it uses the proof-carrying child enumerator.  This
module reuses its executable cumulative/compound builders, applies the existing ordered-key
projection, and reconstructs only the small comparison and geometry tail as executable defs. -/

abbrev Input := LocalizedUniversalReference.Input
abbrev carrierFuel (input : Input) : Nat := LocalizedUniversalReference.carrierFuel input
abbrev Occurrence (input : Input) :=
  input.certified.LocalizedCIPOccurrence (carrierFuel input)
abbrev Facts (input : Input) :=
  List (Fact (Occurrence input) LocalizedAuxiliaryLabel)
abbrev Nodes (input : Input) :=
  List (Node (Occurrence input) LocalizedAuxiliaryLabel)
abbrev Report := List (Nat × Option LocalizedAuxiliaryLabel)

end TetraStereo.OneCenter.LocalizedOrderedReference

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-! ## Executable ordered compound keys -/

/-- Executable ordered compound key: run the existing executable Rule-4/5 key builder, then apply
the established outcome ordering to its complete no/one/two-reference key. -/
def buildCompoundRule45KeyOrderedExec?
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (rerootFuel : Nat) (cursor : input.LocalizedRerootCursor fuel) :
    Option input.LocalizedRerootCompoundRule45Key :=
  (input.buildLocalizedRerootCompoundRule45KeyExec?
    target view rerootFuel cursor).map input.outcomeOrdered45

/-- The executable ordered key is exactly the proof-facing ordered builder, including its
fail-closed `none` result. -/
theorem buildCompoundRule45KeyOrderedExec?_eq
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (rerootFuel : Nat) (cursor : input.LocalizedRerootCursor fuel) :
    input.buildCompoundRule45KeyOrderedExec?
        target view rerootFuel cursor =
      input.buildLocalizedRerootCompoundRule45KeyOrdered?
        target view rerootFuel cursor := by
  unfold buildCompoundRule45KeyOrderedExec?
  calc
    (input.buildLocalizedRerootCompoundRule45KeyExec?
      target view rerootFuel cursor).map input.outcomeOrdered45 =
        (input.buildLocalizedRerootCompoundRule45Key?
          target view rerootFuel cursor).map input.outcomeOrdered45 := by
            rw [← input.buildLocalizedRerootCompoundRule45Key?_eq_buildLocalizedRerootCompoundRule45KeyExec?]
    _ = input.buildLocalizedRerootCompoundRule45KeyOrdered?
        target view rerootFuel cursor :=
          (input.buildLocalizedRerootCompoundRule45KeyOrdered?_eq_map
            target view rerootFuel cursor).symm

/-! ## Executable ordered comparison and safe four-ligand order -/

/-- Pairwise comparison from executable ordered compound keys. -/
def compareThroughRule5OrderedExecAt?
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame fuel)
    (left right : Fin 4) :
    Option ConstitutionalDescriptorHierarchyComparison := do
  let rerootFuel := localizedOccurrenceRerootEvaluationFuel fuel
  let leftKey ← input.buildCompoundRule45KeyOrderedExec?
    target view rerootFuel (frame.cursorAt left)
  let rightKey ← input.buildCompoundRule45KeyOrderedExec?
    target view rerootFuel (frame.cursorAt right)
  some (localizedOccurrenceRule45ComparisonRecord
    (input.compareLocalizedRerootCompoundThroughRule5 leftKey rightKey))

theorem compareThroughRule5OrderedExecAt?_eq
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame fuel)
    (left right : Fin 4) :
    input.compareThroughRule5OrderedExecAt? target view frame left right =
      input.compareLocalizedOccurrenceThroughRule5OrderedAt?
        target view frame left right := by
  unfold compareThroughRule5OrderedExecAt?
    compareLocalizedOccurrenceThroughRule5OrderedAt?
  simp only [input.buildCompoundRule45KeyOrderedExec?_eq]

/-- Computational version of the strict-pair test used by the ordered safe sort. -/
def orderedPairStrictExecOf
    (compareAt : Fin 4 → Fin 4 →
      Option ConstitutionalDescriptorHierarchyComparison)
    (left right : Fin 4) : Bool :=
  match compareAt left right with
  | none => false
  | some result => result.ordering == Ordering.gt

/-- Computational all-pairs coherence check used by the ordered safe sort. -/
def orderedCoherentExecOf
    (compareAt : Fin 4 → Fin 4 →
      Option ConstitutionalDescriptorHierarchyComparison) : List (Fin 4) → Bool
  | [] => true
  | left :: rest =>
      rest.all (orderedPairStrictExecOf compareAt left) &&
        orderedCoherentExecOf compareAt rest

theorem orderedCoherentExecOf_eq
    (compareAt : Fin 4 → Fin 4 →
      Option ConstitutionalDescriptorHierarchyComparison) :
    ∀ order, orderedCoherentExecOf compareAt order = orderCoherentOf compareAt order
  | [] => rfl
  | left :: rest => by
      simp only [orderedCoherentExecOf, orderCoherentOf,
        orderedCoherentExecOf_eq compareAt rest]
      congr 1

/-- Computational stable sort followed by the ordered evaluator's all-pairs coherence gate. -/
def safeTrackedOrderOrderedExecOf
    (compareAt : Fin 4 → Fin 4 →
      Option ConstitutionalDescriptorHierarchyComparison) :
    Option TrackedLocalizedLigandOrder := do
  let tracked ← sortFourLocalizedLigandsTracked compareAt
  if orderedCoherentExecOf compareAt tracked.highestFirst then some tracked else none

theorem safeTrackedOrderOrderedExecOf_eq
    (compareAt : Fin 4 → Fin 4 →
      Option ConstitutionalDescriptorHierarchyComparison) :
    safeTrackedOrderOrderedExecOf compareAt = safeTrackedOrderOf compareAt := by
  unfold safeTrackedOrderOrderedExecOf safeTrackedOrderOf
  cases hsort : sortFourLocalizedLigandsTracked compareAt with
  | none => rfl
  | some tracked =>
      change (if orderedCoherentExecOf compareAt tracked.highestFirst then some tracked else none) =
        (if orderCoherentOf compareAt tracked.highestFirst then some tracked else none)
      rw [orderedCoherentExecOf_eq compareAt tracked.highestFirst]

def safeRule45TrackedOrderOrderedExec?
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame fuel) :
    Option TrackedLocalizedLigandOrder :=
  safeTrackedOrderOrderedExecOf
    (input.compareThroughRule5OrderedExecAt? target view frame)

theorem safeRule45TrackedOrderOrderedExec?_eq
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame fuel) :
    input.safeRule45TrackedOrderOrderedExec? target view frame =
      input.safeLocalizedOccurrenceRule45TrackedOrderOrdered?
        target view frame := by
  unfold safeRule45TrackedOrderOrderedExec?
    safeLocalizedOccurrenceRule45TrackedOrderOrdered?
  have hcompare :
      input.compareThroughRule5OrderedExecAt? target view frame =
        input.compareLocalizedOccurrenceThroughRule5OrderedAt? target view frame := by
    funext left right
    exact input.compareThroughRule5OrderedExecAt?_eq target view frame left right
  calc
    safeTrackedOrderOrderedExecOf
        (input.compareThroughRule5OrderedExecAt? target view frame) =
      safeTrackedOrderOf (input.compareThroughRule5OrderedExecAt? target view frame) :=
        safeTrackedOrderOrderedExecOf_eq _
    _ = safeTrackedOrderOf
        (input.compareLocalizedOccurrenceThroughRule5OrderedAt? target view frame) := by
          rw [hcompare]

/-! ## Executable ordered descriptor -/

def spatialEvidenceOrderedExec?
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target) :
    Option (input.LocalizedOccurrenceRule45SpatialEvidence fuel) := do
  let center ← input.localizedOccurrenceDescriptorCenter? target
  let frame ← input.localizedNoDoubleFourLigandFrameExec? target
  let tracked ← input.safeRule45TrackedOrderOrderedExec? target view frame
  let points ← tracked.highestFirst.mapM fun index =>
    input.localizedRerootCursorSpatialPoint? (frame.cursorAt index)
  some { center := center, frame := frame, tracked := tracked, points := points }

theorem spatialEvidenceOrderedExec?_eq
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target) :
    input.spatialEvidenceOrderedExec? target view =
      input.localizedOccurrenceRule45SpatialEvidenceOrdered? target view := by
  unfold spatialEvidenceOrderedExec? localizedOccurrenceRule45SpatialEvidenceOrdered?
  rw [input.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?]
  simp_rw [input.safeRule45TrackedOrderOrderedExec?_eq]

/-- Executable ordered bare Rule-4/5 descriptor. -/
def descriptorOrderedExec?
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target) :
    Option LocalizedAuxiliaryLabel := do
  let evidence ← input.spatialEvidenceOrderedExec? target view
  let raw ← descriptorOfPriorityOrderedPoints? evidence.points
  some (classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons)

/-- The computational ordered callback has the exact same optional result as the proof-facing
ordered evaluator at every state view. -/
theorem descriptorOrderedExec?_eq
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target) :
    input.descriptorOrderedExec? target view =
      input.localizedOccurrenceRule45DescriptorOrdered? target view := by
  unfold descriptorOrderedExec? localizedOccurrenceRule45DescriptorOrdered?
  rw [input.spatialEvidenceOrderedExec?_eq]

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput

namespace TetraStereo.OneCenter.LocalizedOrderedReference

open CertifiedLocalizedCIPInput
open TetraStereo.Certificate.Dependency

/-! ## Generic ranked run and molecular report -/

def runtimeSemantics (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    input.LocalizedAuxiliaryRuleSemantics fuel where
  DeclarativeDerivation state target outcome :=
    input.descriptorOrderedExec? target
      (input.localizedDependencyView state target) = outcome
  executableRule := fun target view => input.descriptorOrderedExec? target view
  derivation_executable_iff := fun _ _ _ => Iff.rfl

def runtimeSystem (input : Input) :=
  input.certified.localizedCertificateSystem (carrierFuel input)
    (runtimeSemantics input.certified (carrierFuel input))

def dependencies (input : Input) :=
  input.certified.localizedCertificateDependencies (carrierFuel input)

def referenceNodes (input : Input) : Nodes input :=
  input.certified.localizedCertificateNodes (carrierFuel input)
    (runtimeSemantics input.certified (carrierFuel input))

def referenceFacts (input : Input) : Facts input :=
  input.certified.localizedCertificateFacts (carrierFuel input)
    (runtimeSemantics input.certified (carrierFuel input))

def referenceState (input : Input) :
    input.certified.LocalizedAuxiliaryState (carrierFuel input) :=
  lookup (referenceFacts input)

def report (input : Input) (facts : Facts input) : Report :=
  input.certified.canonicalTetrahedralCenters.map fun center =>
    (center.val.val, lookup facts
      (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center))

/-- Callable report over a certified localized input.  Unlike the noncomputable mathematical
evaluator, this runs the executable ordered callback through the generic finite ranked producer. -/
def analyze (input : Input) : Report := report input (referenceFacts input)

theorem reference_check (input : Input) :
    check (runtimeSystem input) (dependencies input) (referenceNodes input) =
      some (referenceFacts input) :=
  input.certified.localizedCertificate_check (carrierFuel input)
    (runtimeSemantics input.certified (carrierFuel input))

theorem reference_model (input : Input) :
    (runtimeSystem input).CIPModel (referenceState input) :=
  input.certified.localizedCertificateFacts_cipModel (carrierFuel input)
    (runtimeSemantics input.certified (carrierFuel input))

theorem reference_eq_boundedIteration (input : Input) :
    referenceState input = input.certified.evaluateLocalizedOccurrences (carrierFuel input)
      (runtimeSemantics input.certified (carrierFuel input)).executableRule := by
  have model := reference_model input
  unfold runtimeSystem localizedCertificateSystem at model
  rw [input.certified.localizedAuxiliaryOccurrenceSystemExecutableRoot_eq_old] at model
  exact (input.certified.evaluateLocalizedOccurrences_eq_model (carrierFuel input)
    (runtimeSemantics input.certified (carrierFuel input)) model).symm

theorem runtimeSemantics_executableRule_eq_ordered
    (input : Input) :
    (runtimeSemantics input.certified (carrierFuel input)).executableRule =
      (input.certified.localizedOccurrenceRule45OrderedAuxiliarySemantics
        (carrierFuel input)).executableRule := by
  funext target view
  exact input.certified.descriptorOrderedExec?_eq target view

theorem referenceState_eq_orderedReferenceState (input : Input) :
    referenceState input = input.certified.orderedReferenceState (carrierFuel input) := by
  rw [reference_eq_boundedIteration]
  have evaluatorEq := runtimeSemantics_executableRule_eq_ordered input
  unfold CertifiedLocalizedCIPInput.orderedReferenceState
    CertifiedLocalizedCIPInput.evaluateLocalizedOccurrences
  rw [evaluatorEq]

theorem report_centers (input : Input) (facts : Facts input) :
    (report input facts).map Prod.fst =
      input.certified.canonicalTetrahedralCenters.map (fun center => center.val.val) := by
  simp only [report, List.map_map, Function.comp_def]

/-- The callable molecular report is the ordered evaluator's label at every canonical detected
top occurrence; the full `Option LocalizedAuxiliaryLabel` preserves lowercase pseudo labels. -/
theorem analyze_eq_orderedReferenceReport (input : Input) :
    analyze input = input.certified.canonicalTetrahedralCenters.map fun center =>
      (center.val.val, input.certified.orderedReferenceState (carrierFuel input)
        (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center)) := by
  unfold analyze report
  apply List.map_congr_left
  intro center _
  apply Prod.ext
  · rfl
  · simpa [referenceState] using congrFun (referenceState_eq_orderedReferenceState input)
      (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center)

end TetraStereo.OneCenter.LocalizedOrderedReference
