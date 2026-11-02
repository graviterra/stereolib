import TetraStereo.OneCenter.LocalizedRetainedCursorTransport
import TetraStereo.OneCenter.LocalizedCyclicContextFrameCompilation
import TetraStereo.OneCenter.LocalizedActualMolecularEvidenceRefinement
import TetraStereo.OneCenter.LocalizedRuleMajorReferencePipeline
import TetraStereo.OneCenter.LocalizedContextCyclicReaderBridge
import TetraStereo.OneCenter.LocalizedRootBranchAuxiliaryLocality
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-!
# Generated-state transport along one molecular automorphism

The descriptor-map key is an `OccurrenceUnit`: original root plus atom path. `molecularFrameUnit`
reads that path from `history.reverse.tail`. One `moleculeGraph.Aut` maps the root and the path.
`LocalizedDepthDependency` is preserved by the accepted occurrence transport.

`transportGeneratedState` and `transportDescriptorMap` are pullbacks. On a `SimpleBonded` input the
pulled-back generated map's `molecularReader` matches the pulled-back `referenceState` at every
cursor, by the existing simple-bonded readback. At a strict dependency that common value is the
source occurrence's generated label.

`OneStepDescriptorTransport` is one `ruleMajorDescriptor?` call under dependency-view agreement.
`reference_fixed` and `localizedDepthDependency_wellFounded` turn that call into transport of a
fixed state. The one-step fact is not proved here. `RankedOccurrenceIteration` has no automorphism
lemma; this file does not rebuild that engine. No acyclicity, unique-nearest, supplied label, or
desired whole-state equality is assumed.
-/

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

open DeclarativeCIP MoleculeGraph

noncomputable section

def transportOccurrenceUnit {Atom : Type*} (e : Equiv.Perm Atom) (unit : OccurrenceUnit Atom) :
    OccurrenceUnit Atom :=
  ⟨e unit.root, unit.path.map e⟩

theorem transportOccurrenceUnit_atom {Atom : Type*} (e : Equiv.Perm Atom)
    (unit : OccurrenceUnit Atom) :
    (transportOccurrenceUnit e unit).atom = e unit.atom := by
  simp only [transportOccurrenceUnit, OccurrenceUnit.atom, List.getLast?_map]
  cases h : unit.path.getLast? with
  | none => simp [h]
  | some atom => simp [h]

private theorem occurrenceUnit_eq_of_fields {Atom : Type*} {root₁ root₂ : Atom}
    {path₁ path₂ : List Atom} (hroot : root₁ = root₂) (hpath : path₁ = path₂) :
    (⟨root₁, path₁⟩ : OccurrenceUnit Atom) = ⟨root₂, path₂⟩ := by
  cases hroot
  cases hpath
  rfl

theorem transportOccurrenceUnit_symm_apply {Atom : Type*} (e : Equiv.Perm Atom)
    (unit : OccurrenceUnit Atom) :
    transportOccurrenceUnit e.symm (transportOccurrenceUnit e unit) = unit := by
  have eta : unit = ⟨unit.root, unit.path⟩ := rfl
  unfold transportOccurrenceUnit
  rw [eta]
  exact occurrenceUnit_eq_of_fields (Equiv.symm_apply_apply e unit.root)
    (by simp [List.map_map, Equiv.symm_apply_apply])

private theorem history_reverse_cons {α : Type*} {atoms : List α} {root : α}
    (headEq : atoms.head? = some root) : atoms = root :: atoms.tail := by
  cases atoms with
  | nil => simp at headEq
  | cons atom rest =>
      simp at headEq
      subst headEq
      rfl

private theorem history_reverse_tail_map {Atom : Type*} [DecidableEq Atom]
    (e : Equiv.Perm Atom) (node : OfficialCIPNode Atom) (root : Atom)
    (last : node.history.getLast? = some root) :
    (mapOfficialNode e node).history.reverse.tail = node.history.reverse.tail.map e := by
  have head : node.history.reverse.head? = some root := by
    simpa [List.head?_reverse] using last
  have hrev : node.history.reverse = root :: node.history.reverse.tail :=
    history_reverse_cons head
  have mappedRev : (mapOfficialNode e node).history.reverse = node.history.reverse.map e := by
    simp only [mapOfficialNode]
    exact List.map_reverse.symm
  rw [mappedRev, hrev]
  simp

variable (input : CertifiedLocalizedCIPInput)

private theorem neighborFinset_map_aut (e : input.moleculeGraph.Aut) (atom : input.Atom) :
    input.moleculeGraph.neighborFinset ((e : Equiv.Perm input.Atom) atom) =
      (input.moleculeGraph.neighborFinset atom).map (e : Equiv.Perm input.Atom).toEmbedding := by
  ext u
  constructor
  · intro present
    have adjacent : input.moleculeGraph.Adj ((e : Equiv.Perm input.Atom) atom) u :=
      (input.moleculeGraph.mem_neighborFinset (v := (e : Equiv.Perm input.Atom) atom) (u := u)).mp
        present
    refine Finset.mem_map.mpr ⟨(e : Equiv.Perm input.Atom).symm u, ?_, ?_⟩
    · have imageAdj :
          input.moleculeGraph.Adj ((e : Equiv.Perm input.Atom) atom)
            ((e : Equiv.Perm input.Atom) ((e : Equiv.Perm input.Atom).symm u)) := by
        simpa [(e : Equiv.Perm input.Atom).apply_symm_apply] using adjacent
      exact (input.moleculeGraph.mem_neighborFinset (v := atom)
        (u := (e : Equiv.Perm input.Atom).symm u)).mpr
        ((MoleculeGraph.Aut.adj_iff input.moleculeGraph e atom
          ((e : Equiv.Perm input.Atom).symm u)).mp imageAdj)
    · simp
  · intro present
    obtain ⟨v, member, rfl⟩ := Finset.mem_map.mp present
    have sourceAdj : input.moleculeGraph.Adj atom v :=
      (input.moleculeGraph.mem_neighborFinset (v := atom) (u := v)).mp member
    exact (input.moleculeGraph.mem_neighborFinset
      (v := (e : Equiv.Perm input.Atom) atom) (u := (e : Equiv.Perm input.Atom) v)).mpr
      ((MoleculeGraph.Aut.adj_iff input.moleculeGraph e atom v).mpr sourceAdj)

theorem isDetectedCenter_transport_iff (e : input.moleculeGraph.Aut) (atom : input.Atom) :
    IsDetectedCenter input.moleculeGraph atom ↔
      IsDetectedCenter input.moleculeGraph ((e : Equiv.Perm input.Atom) atom) := by
  unfold IsDetectedCenter
  rw [input.neighborFinset_map_aut e atom, Finset.card_map]

theorem transportOccurrence_provenance
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    (occ : input.LocalizedCIPOccurrence fuel) :
    (input.transportOccurrence singleBonded e occ).1.node.provenance = occ.1.node.provenance := by
  rw [transportOccurrence_node]
  rfl

theorem molecularFrameUnit_transport
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    (occ : input.LocalizedCIPOccurrence fuel) :
    input.molecularFrameUnit (input.transportOccurrence singleBonded e occ).1 =
      transportOccurrenceUnit (e : Equiv.Perm input.Atom) (input.molecularFrameUnit occ.1) := by
  have mappedTail := history_reverse_tail_map (e : Equiv.Perm input.Atom) occ.1.node occ.1.root
    (input.frameCarrierOccurrence_history_getLast_eq_root occ)
  simp only [molecularFrameUnit, transportOccurrence_root, transportOccurrence_node,
    transportOccurrenceUnit, mappedTail]

theorem molecularFrameUnit_atom_transport
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    (occ : input.LocalizedCIPOccurrence fuel) :
    (input.molecularFrameUnit (input.transportOccurrence singleBonded e occ).1).atom =
      (e : Equiv.Perm input.Atom) (input.molecularFrameUnit occ.1).atom := by
  rw [input.molecularFrameUnit_transport singleBonded e occ]
  exact transportOccurrenceUnit_atom (e : Equiv.Perm input.Atom) (input.molecularFrameUnit occ.1)

def transportDetectedOccurrence (e : input.moleculeGraph.Aut)
    (unit : DetectedOccurrence input.moleculeGraph) : DetectedOccurrence input.moleculeGraph :=
  ⟨transportOccurrenceUnit (e : Equiv.Perm input.Atom) unit.1, by
    rw [transportOccurrenceUnit_atom]
    exact (input.isDetectedCenter_transport_iff e unit.1.atom).mp unit.property⟩

theorem transportDetectedOccurrence_symm_apply (e : input.moleculeGraph.Aut)
    (unit : DetectedOccurrence input.moleculeGraph) :
    input.transportDetectedOccurrence (e⁻¹) (input.transportDetectedOccurrence e unit) = unit := by
  apply Subtype.ext
  have coeInv : ((e⁻¹ : input.moleculeGraph.Aut) : Equiv.Perm input.Atom) =
      (e : Equiv.Perm input.Atom).symm := by
    rw [Subgroup.coe_inv]
    rfl
  simpa [transportDetectedOccurrence, coeInv] using
    transportOccurrenceUnit_symm_apply (e : Equiv.Perm input.Atom) unit.1

def transportDescriptorMap (e : input.moleculeGraph.Aut)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)) :
    DescriptorMap (DetectedOccurrence input.moleculeGraph) :=
  fun unit => descriptorMap (input.transportDetectedOccurrence (e⁻¹) unit)

theorem transportDescriptorMap_transportDetected (e : input.moleculeGraph.Aut)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph) :
    input.transportDescriptorMap e descriptorMap (input.transportDetectedOccurrence e unit) =
      descriptorMap unit := by
  unfold transportDescriptorMap
  exact congrArg descriptorMap (input.transportDetectedOccurrence_symm_apply e unit)

def transportGeneratedState
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    (state : input.LocalizedAuxiliaryState fuel) : input.LocalizedAuxiliaryState fuel :=
  fun occ => state (input.transportOccurrence singleBonded (e⁻¹) occ)

theorem transportGeneratedState_transportOccurrence
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    (state : input.LocalizedAuxiliaryState fuel) (occ : input.LocalizedCIPOccurrence fuel) :
    input.transportGeneratedState singleBonded e state
        (input.transportOccurrence singleBonded e occ) = state occ := by
  unfold transportGeneratedState
  exact congrArg state (input.transportOccurrence_inv_apply singleBonded e occ)

theorem localizedDependencyLabel_transportGeneratedState
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    (state : input.LocalizedAuxiliaryState fuel) (target : input.LocalizedCIPOccurrence fuel)
    (cursor : input.LocalizedRerootCursor fuel) :
    input.localizedDependencyLabel (input.transportOccurrence singleBonded e target)
        (input.localizedDependencyView (input.transportGeneratedState singleBonded e state)
          (input.transportOccurrence singleBonded e target))
        (input.transportCursor singleBonded e cursor) =
      input.localizedDependencyLabel target (input.localizedDependencyView state target) cursor := by
  unfold localizedDependencyLabel localizedDependencyView
  simp only [transportCursor_occurrence]
  by_cases related : input.LocalizedDepthDependency cursor.occurrence target
  · have relatedImage :=
      (input.localizedDepthDependency_transport_iff singleBonded e cursor.occurrence target).mp
        related
    simp only [dif_pos related, dif_pos relatedImage, transportGeneratedState]
    exact congrArg state (input.transportOccurrence_inv_apply singleBonded e cursor.occurrence)
  · have notImage :
        ¬ input.LocalizedDepthDependency
          (input.transportOccurrence singleBonded e cursor.occurrence)
          (input.transportOccurrence singleBonded e target) := by
      intro imageRelated
      exact related
        ((input.localizedDepthDependency_transport_iff singleBonded e cursor.occurrence target).mpr
          imageRelated)
    simp only [dif_neg related, dif_neg notImage]

theorem molecularReader_transport
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (target : input.LocalizedCIPOccurrence fuel) (cursor : input.LocalizedRerootCursor fuel) :
    input.molecularReader (input.transportDescriptorMap e descriptorMap)
        (input.transportOccurrence singleBonded e target)
        (input.transportCursor singleBonded e cursor) =
      input.molecularReader descriptorMap target cursor := by
  unfold molecularReader localizedDependencyLabel
  simp only [transportCursor_occurrence]
  by_cases related : input.LocalizedDepthDependency cursor.occurrence target
  · have relatedImage :=
      (input.localizedDepthDependency_transport_iff singleBonded e cursor.occurrence target).mp
        related
    rw [dif_pos relatedImage, dif_pos related]
    dsimp [molecularView]
    have imageProv :
        (mapOfficialNode (e : Equiv.Perm input.Atom) cursor.occurrence.1.node).provenance =
          cursor.occurrence.1.node.provenance := rfl
    rw [imageProv]
    by_cases real : cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom
    · rw [if_pos real, if_pos real]
      by_cases detected : IsDetectedCenter input.moleculeGraph
          (input.molecularFrameUnit cursor.occurrence.1).atom
      · have detectedImage : IsDetectedCenter input.moleculeGraph
            (input.molecularFrameUnit
              (input.transportOccurrence singleBonded e cursor.occurrence).1).atom := by
          rw [input.molecularFrameUnit_atom_transport singleBonded e cursor.occurrence]
          exact (input.isDetectedCenter_transport_iff e
            (input.molecularFrameUnit cursor.occurrence.1).atom).mp detected
        rw [dif_pos detectedImage, dif_pos detected]
        have unitEq :
            (⟨input.molecularFrameUnit
                (input.transportOccurrence singleBonded e cursor.occurrence).1, detectedImage⟩ :
              DetectedOccurrence input.moleculeGraph) =
            input.transportDetectedOccurrence e
              ⟨input.molecularFrameUnit cursor.occurrence.1, detected⟩ := by
          apply Subtype.ext
          exact input.molecularFrameUnit_transport singleBonded e cursor.occurrence
        rw [unitEq]
        rw [input.transportDescriptorMap_transportDetected e descriptorMap
          ⟨input.molecularFrameUnit cursor.occurrence.1, detected⟩]
      · have notDetectedImage : ¬ IsDetectedCenter input.moleculeGraph
            (input.molecularFrameUnit
              (input.transportOccurrence singleBonded e cursor.occurrence).1).atom := by
          intro imageDetected
          have imageDetected' : IsDetectedCenter input.moleculeGraph
              ((e : Equiv.Perm input.Atom)
                (input.molecularFrameUnit cursor.occurrence.1).atom) := by
            rw [← input.molecularFrameUnit_atom_transport singleBonded e cursor.occurrence]
            exact imageDetected
          exact detected ((input.isDetectedCenter_transport_iff e
            (input.molecularFrameUnit cursor.occurrence.1).atom).mpr imageDetected')
        rw [dif_neg notDetectedImage, dif_neg detected]
    · rw [if_neg real, if_neg real]
  · have notImage :
        ¬ input.LocalizedDepthDependency
          (input.transportOccurrence singleBonded e cursor.occurrence)
          (input.transportOccurrence singleBonded e target) := by
      intro imageRelated
      exact related
        ((input.localizedDepthDependency_transport_iff singleBonded e cursor.occurrence target).mpr
          imageRelated)
    rw [dif_neg notImage, dif_neg related]

/-- Path membership travels with the atom path. Address prefixes stay on the source because slot
numbers are the locality gap. -/
theorem occurrenceUnitExtendsRootBranch_transport
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    (branch : input.LocalizedCIPOccurrence fuel) (unit : OccurrenceUnit input.Atom)
    (extendsBranch : input.OccurrenceUnitExtendsRootBranch branch unit) :
    input.OccurrenceUnitExtendsRootBranch (input.transportOccurrence singleBonded e branch)
      (transportOccurrenceUnit (e : Equiv.Perm input.Atom) unit) := by
  obtain ⟨rootEq, pathPrefix⟩ := extendsBranch
  obtain ⟨tail, tailEq⟩ := pathPrefix
  constructor
  · simp [transportOccurrenceUnit, transportOccurrence_root, rootEq]
  · rw [input.molecularFrameUnit_transport singleBonded e branch]
    refine ⟨tail.map (e : Equiv.Perm input.Atom), ?_⟩
    simp [transportOccurrenceUnit, List.map_append, ← tailEq]

/-- One evaluator step. Agreement is only on strict dependencies of this target. -/
def OneStepDescriptorTransport
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) (fuel : Nat)
    (adjust : Option LocalizedAuxiliaryLabel → Option LocalizedAuxiliaryLabel) : Prop :=
  ∀ (target : input.LocalizedCIPOccurrence fuel)
    (sourceView : input.LocalizedDependencyView target)
    (imageView : input.LocalizedDependencyView (input.transportOccurrence singleBonded e target)),
    (∀ (source : input.LocalizedCIPOccurrence fuel)
      (dependency : input.LocalizedDepthDependency source target),
      imageView (input.transportOccurrence singleBonded e source)
          ((input.localizedDepthDependency_transport_iff singleBonded e source target).mp
            dependency) =
        adjust (sourceView source dependency)) →
    input.ruleMajorDescriptor? (input.transportOccurrence singleBonded e target) imageView =
      adjust (input.ruleMajorDescriptor? target sourceView)

theorem fixedAuxiliaryState_transport_of_oneStep
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) (fuel : Nat)
    (adjust : Option LocalizedAuxiliaryLabel → Option LocalizedAuxiliaryLabel)
    (state : input.LocalizedAuxiliaryState fuel)
    (fixed : ∀ target : input.LocalizedCIPOccurrence fuel,
      input.ruleMajorDescriptor? target (input.localizedDependencyView state target) = state target)
    (oneStep : input.OneStepDescriptorTransport singleBonded e fuel adjust)
    (target : input.LocalizedCIPOccurrence fuel) :
    state (input.transportOccurrence singleBonded e target) = adjust (state target) := by
  refine @WellFounded.induction _ _
      (input.localizedDepthDependency_wellFounded fuel)
      (fun occurrence =>
        state (input.transportOccurrence singleBonded e occurrence) = adjust (state occurrence))
      target ?_
  intro target ih
  calc
    state (input.transportOccurrence singleBonded e target)
        = input.ruleMajorDescriptor? (input.transportOccurrence singleBonded e target)
            (input.localizedDependencyView state
              (input.transportOccurrence singleBonded e target)) :=
          (fixed (input.transportOccurrence singleBonded e target)).symm
    _ = adjust (input.ruleMajorDescriptor? target (input.localizedDependencyView state target)) :=
          oneStep target (input.localizedDependencyView state target)
            (input.localizedDependencyView state (input.transportOccurrence singleBonded e target))
            (fun source dependency => by
              simp only [localizedDependencyView]
              exact ih source dependency)
    _ = adjust (state target) := congrArg adjust (fixed target)

end

end CertifiedLocalizedCIPInput

namespace LocalizedRuleMajorReference

open DeclarativeCIP CertifiedLocalizedCIPInput

noncomputable section

theorem molecularReader_transportGenerated_eq_dependencyLabel (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (e : input.certified.moleculeGraph.Aut) (target : Occurrence input)
    (cursor : input.certified.LocalizedRerootCursor (carrierFuel input)) :
    input.certified.molecularReader
        (input.certified.transportDescriptorMap e (descriptorMap input))
        (input.certified.transportOccurrence singleBonded e target)
        (input.certified.transportCursor singleBonded e cursor) =
      input.certified.localizedDependencyLabel
        (input.certified.transportOccurrence singleBonded e target)
        (input.certified.localizedDependencyView
          (input.certified.transportGeneratedState singleBonded e (referenceState input))
          (input.certified.transportOccurrence singleBonded e target))
        (input.certified.transportCursor singleBonded e cursor) := by
  rw [input.certified.molecularReader_transport singleBonded e (descriptorMap input) target cursor,
    input.certified.localizedDependencyLabel_transportGeneratedState singleBonded e
      (referenceState input) target cursor]
  exact congrFun (molecularReader_eq_generatedReader_of_simpleBonded input singleBonded target)
    cursor

theorem transportedMolecularReader_eq_sourceReference_of_dependency (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (e : input.certified.moleculeGraph.Aut) (target : Occurrence input)
    (cursor : input.certified.LocalizedRerootCursor (carrierFuel input))
    (dependency : input.certified.LocalizedDepthDependency cursor.occurrence target) :
    input.certified.molecularReader
        (input.certified.transportDescriptorMap e (descriptorMap input))
        (input.certified.transportOccurrence singleBonded e target)
        (input.certified.transportCursor singleBonded e cursor) =
      referenceState input cursor.occurrence := by
  rw [input.certified.molecularReader_transport singleBonded e (descriptorMap input) target cursor]
  have sourceReader := congrFun
    (molecularReader_eq_generatedReader_of_simpleBonded input singleBonded target) cursor
  rw [sourceReader]
  unfold CertifiedLocalizedCIPInput.localizedDependencyLabel
    CertifiedLocalizedCIPInput.localizedDependencyView
  rw [dif_pos dependency]

theorem referenceState_transport_of_oneStep (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (e : input.certified.moleculeGraph.Aut)
    (adjust : Option LocalizedAuxiliaryLabel → Option LocalizedAuxiliaryLabel)
    (oneStep : input.certified.OneStepDescriptorTransport singleBonded e (carrierFuel input) adjust)
    (target : Occurrence input) :
    referenceState input (input.certified.transportOccurrence singleBonded e target) =
      adjust (referenceState input target) :=
  input.certified.fixedAuxiliaryState_transport_of_oneStep singleBonded e (carrierFuel input) adjust
    (referenceState input) (fun occurrence => reference_fixed input occurrence) oneStep target

end

end LocalizedRuleMajorReference

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.transportOccurrenceUnit
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.transportOccurrenceUnit_atom
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.transportOccurrenceUnit_symm_apply
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.isDetectedCenter_transport_iff
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.transportOccurrence_provenance
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.molecularFrameUnit_transport
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.molecularFrameUnit_atom_transport
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.transportDetectedOccurrence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.transportDetectedOccurrence_symm_apply
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.transportDescriptorMap
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.transportDescriptorMap_transportDetected
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.transportGeneratedState
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.transportGeneratedState_transportOccurrence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedDependencyLabel_transportGeneratedState
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.molecularReader_transport
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.occurrenceUnitExtendsRootBranch_transport
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OneStepDescriptorTransport
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.fixedAuxiliaryState_transport_of_oneStep
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.molecularReader_transportGenerated_eq_dependencyLabel
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.transportedMolecularReader_eq_sourceReference_of_dependency
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.referenceState_transport_of_oneStep
