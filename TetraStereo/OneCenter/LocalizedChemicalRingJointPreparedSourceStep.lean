import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceKeys
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedExecution
import TetraStereo.OneCenter.LocalizedChemicalRingFrameReadback
import TetraStereo.OneCenter.LocalizedChemicalRingOrderingTransport
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# A fully source-cut one-step descriptor operator and its realization

This module states an independent, source-only one-step descriptor prescription for the
jointly marked prepared C.I.P. evaluator, and proves that the actual prepared evaluator
computes exactly this prescription.

## The specification

The specification is parametrized by

* `single : input.moleculeGraph.SimpleBonded`, the localized covalent bond reading of the
  molecular graph used by the source cut keys;
* `family : Geometry → List input.Atom → DescriptorMap (DetectedOccurrence input.moleculeGraph)`,
  a *candidate descriptor-map family*: an arbitrary function assigning to a geometry and an
  ordered list of reference atoms a candidate descriptor map.  The family is a parameter of
  the specification; no execution-level state appears in it;
* the molecular target occurrence `target`;
* a plain four-ligand occurrence frame `frame` (a frame of raw carrier nodes), and
* a geometry `geom` and an ordered reference context `references`.

The prescription is:

1. For every slot `slot : Fin 4`, form the fully source-cut key
   `sourceKeys(input, single, family geom references, target, frame, references, W, D, slot)`
   with molecular window width/depth `allCutWidth`/`allCutDepth` and joint-marker thresholds
   `W = retainedCarrierFuel input`, `D = 2 * (retainedCarrierFuel input + 1)`.
   These keys depend on the molecule graph, the target occurrence, the raw occurrence frame,
   the candidate map at `(geom, references)` and the reference context only.
2. Rank all four slots by strict decreasing key order (`keyOrder`, the stable insertion sort
   induced by the key comparison).  Strictness means `Function.Injective` of *all four* keys,
   not merely uniqueness of the maximal key.
3. If the four keys are pairwise distinct, read the orientation (determinant/handedness) of
   the four ranked raw frame atoms in the given geometry.  The determinant is *not* a key
   tiebreaker: it is evaluated only after the full strict ranking, from the ranked atoms.
4. Otherwise, determine *all* tied classes of the sorted key list (every maximal run of equal
   keys, not only the greatest class).  For each slot in a tied class, form the *extended*
   reference context `references ++ [reference]`, where `reference` is the raw molecular atom
   of that slot in the frame, recompute the candidate map from the family *at that extended
   context and the same geometry*, recompute the four source cut keys in that extended context,
   and read the orientation of the resulting ranking in the same geometry if those four keys
   are again pairwise distinct; if not, that slot contributes no outcome.  The outcomes of all
   selected slots are combined by the consensus operation.
5. The one-step descriptor is formed by `caseFromMirror?` from the raw outcome at `geom` and
   the raw outcome computed independently at `mirror geom`; the mirrored side regenerates its
   own candidate map from the family at `(mirror geom, references)` (and at the corresponding
   extended contexts for its own tied-class reference choices).

No execution-level notion (`generated`, `preparedFacts`, `preparedDescriptor?`,
`rawStateDescriptorMap`, `rawStateFrames`, `buildJoint?`, `referenceState`) occurs in the
specification.  In particular, the specification does not call the compiled key machinery or
the fallback machinery of the evaluator.

## The realization

The main theorem `preparedDescriptor_eq_sourceDescriptor` proves that, for the actual
generated descriptor-map family
`generatedFamily input mol depth node geom references = rawStateDescriptorMap input
(generated input mol depth geom node references)`, the actual prepared descriptor
`preparedDescriptor? mol (jointOperations input mol) depth geom [] (references.map Fin.val)
node` equals `sourceDescriptor` evaluated at the molecular target occurrence and the plain
molecular occurrence frame of an `OccurrenceData` for the node.  The theorem
`reached_preparedDescriptor_eq_sourceDescriptor` removes the `OccurrenceData` parameter for
any admitted reached real detected occurrence, existentially exhibiting the target occurrence
and its molecular frame, exactly as the evaluator exhibits them.

The `OccurrenceData` structure is itself a source-level correspondence derived elsewhere
(`occurrenceData_exists`); it is not a candidate state and the specification never inspects
it.  `OccurrenceData` is used only in the realization proof to identify the plain molecular
frame and the molecular atom map of the occurrence with the ones appearing in the actual
execution.

This closes the local one-step execution: it does not assert well-foundedness or existence
of a global generated-map solution, and it does not assert any IUPAC normative policy.  No
assumption about a desired output, a comparator, an ordering, injectivity of the keys, or a
reader correspondence is used.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStep

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedGenericMarkedRecalculation (Geometry mirror readback? consensus caseFromMirror?)
open LocalizedChemicalRingJointMarkerRanking (RefinedKey)
open LocalizedChemicalRingJointPreparedSourceKeys (sourceKeys)
open LocalizedChemicalRingJointMarkerFrameExecution
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData referenceAt rank)
open LocalizedChemicalRingCompletenessMarked (enumeration)
open LocalizedMarkedRetainedOrdinaryRanking (keyOrder adjacentBy)
open LocalizedChemicalRingOrderingTransport (tiedEntries)
open LocalizedChemicalRingFrameReadback (atomAt)
open LocalizedMarkedRetainedMolecularSelection (retainedCarrierFuel)
open LocalizedChemicalRingJointPreparedExecution
open LocalizedChemicalRingJointMarkerOperations
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedMarkedCarrierLookup (lookup?)
open LocalizedChemicalRingPreparedContextRecursion (preparedDescriptor?)

noncomputable section
open scoped Classical

abbrev Node := RawMolecule.CanonicalBranchNode

variable (input : CertifiedLocalizedCIPInput)

/-! ## The candidate family -/

/-- A candidate descriptor-map family: a geometry and an ordered list of reference atoms
determine a candidate descriptor map.  This is the only state-like object of the source
specification. -/
abbrev DescriptorFamily :=
  Geometry → List input.Atom → DescriptorMap (DetectedOccurrence input.moleculeGraph)

/-- The raw molecular atom carried by a plain occurrence frame slot. -/
def frameAtom? (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (slot : Fin 4) : Option input.Atom :=
  (frame.cursorAt slot).occurrence.1.node.current?

/-- The four fully source-cut keys at a plain frame, a candidate family, a geometry and an
ordered reference context. -/
def sourceKeysAt (single : input.moleculeGraph.SimpleBonded) (family : DescriptorFamily input)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (geom : Geometry) (references : List input.Atom) : Fin 4 → RefinedKey :=
  fun slot =>
    sourceKeys input single (family geom references) target frame references
      (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) slot

/-! ## The source one-step operator -/

/-- All tied classes of a keyed slot list: the slots whose key agrees with the key of some
other slot.  This is `tiedEntries` applied to the strict decreasing key order; it selects
every tied run, not only the greatest one. -/
def sourceSelectedSlots (keys : Fin 4 → RefinedKey) : List (Fin 4) :=
  tiedEntries false (keyOrder keys (List.finRange 4))
    (adjacentBy (fun a b => some (compare (keys a) (keys b)))
      (keyOrder keys (List.finRange 4)))

/-- The source orientation reading: rank the four slots by decreasing key and read the
orientation of the raw frame atoms in that ranked order, in the given geometry. -/
def sourceReading (geom : Geometry)
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (keys : Fin 4 → RefinedKey) : Option RS :=
  ((keyOrder keys (List.finRange 4)).mapM (atomAt input frame)).bind (readback? geom)

/-- The source fallback outcome of one tied-class slot: extend the reference context by the
raw molecular atom of that slot, recompute the candidate map from the family at the extended
context and the same geometry, and take the strict source reading in that extended context
if its four keys are pairwise distinct. -/
def sourceFallback (single : input.moleculeGraph.SimpleBonded)
    (family : DescriptorFamily input)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (geom : Geometry) (references : List input.Atom) (slot : Fin 4) :
    Option RS :=
  (frameAtom? input frame slot).bind fun reference =>
    if Function.Injective
        (sourceKeysAt input single family target frame geom (references ++ [reference])) then
      sourceReading input geom frame
        (sourceKeysAt input single family target frame geom (references ++ [reference]))
    else none

/-- The source one-step operator: strict all-four key ranking gives the determinant reading;
otherwise every tied-class slot contributes its extended-context source fallback outcome, and
the outcomes are combined by consensus. -/
def sourceStep (single : input.moleculeGraph.SimpleBonded) (family : DescriptorFamily input)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (geom : Geometry) (references : List input.Atom) :
    Option RS :=
  if Function.Injective
      (sourceKeysAt input single family target frame geom references) then
    sourceReading input geom frame
      (sourceKeysAt input single family target frame geom references)
  else
    consensus ((sourceSelectedSlots
        (sourceKeysAt input single family target frame geom references)).map
      (sourceFallback input single family target frame geom references))

/-- The source one-step descriptor: both geometry sides are evaluated independently from the
candidate family, and the two raw outcomes are combined by the mirror case analysis. -/
def sourceDescriptor (single : input.moleculeGraph.SimpleBonded)
    (family : DescriptorFamily input)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (geom : Geometry) (references : List input.Atom) :
    Option LocalizedTetrahedralRSPseudoDescriptor :=
  caseFromMirror? (sourceStep input single family target frame geom references)
    (sourceStep input single family target frame (mirror geom) references)

/-- The source descriptor evaluated at the frame selected by the molecular frame execution of
the target occurrence.  This is the form used by the realization statement for reached real
occurrences; the frame lookup is the only execution-level ingredient and it happens outside
the prescription `sourceDescriptor`. -/
def sourceDescriptorExec? (single : input.moleculeGraph.SimpleBonded)
    (family : DescriptorFamily input)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (geom : Geometry) (references : List input.Atom) :
    Option LocalizedTetrahedralRSPseudoDescriptor :=
  (input.localizedNoDoubleFourLigandFrameExec? target).bind fun frame =>
    sourceDescriptor input single family target frame geom references

/-! ## Elementary consequences of the specification -/

theorem sourceSelectedSlots_mem_iff (keys : Fin 4 → RefinedKey) (slot : Fin 4) :
    slot ∈ sourceSelectedSlots keys ↔
      slot ∈ List.finRange 4 ∧
        ∃ other ∈ List.finRange 4, other ≠ slot ∧ keys other = keys slot := by
  exact LocalizedChemicalRingOrderingTransport.tied_sorted_mem compare
    LocalizedChemicalRingJointMarkerRanking.refined_compare_eq_iff keys (List.finRange 4)
    (List.nodup_finRange 4) slot

theorem sourceStep_eq_strict (single : input.moleculeGraph.SimpleBonded)
    (family : DescriptorFamily input)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (geom : Geometry) (references : List input.Atom)
    (injective : Function.Injective
      (sourceKeysAt input single family target frame geom references)) :
    sourceStep input single family target frame geom references =
      sourceReading input geom frame
        (sourceKeysAt input single family target frame geom references) := by
  unfold sourceStep
  rw [if_pos injective]

theorem sourceStep_eq_consensus (single : input.moleculeGraph.SimpleBonded)
    (family : DescriptorFamily input)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (geom : Geometry) (references : List input.Atom)
    (notInjective : ¬ Function.Injective
      (sourceKeysAt input single family target frame geom references)) :
    sourceStep input single family target frame geom references =
      consensus ((sourceSelectedSlots
          (sourceKeysAt input single family target frame geom references)).map
        (sourceFallback input single family target frame geom references)) := by
  unfold sourceStep
  rw [if_neg notInjective]

theorem sourceDescriptor_eq_case (single : input.moleculeGraph.SimpleBonded)
    (family : DescriptorFamily input)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (geom : Geometry) (references : List input.Atom) :
    sourceDescriptor input single family target frame geom references =
      caseFromMirror? (sourceStep input single family target frame geom references)
        (sourceStep input single family target frame (mirror geom) references) := rfl

/-! ## The realized candidate family -/

variable (mol : RawMolecule)

/-- The actual generated descriptor-map family: at a geometry and a reference context it is
the descriptor map of the prepared execution state generated by that context. -/
def generatedFamily (depth : Nat) (node : Node) : DescriptorFamily input :=
  fun geom references =>
    LocalizedMarkedRetainedStateReader.rawStateDescriptorMap input
      (generated input mol depth geom node references)

theorem generatedFamily_apply (depth : Nat) (node : Node) (geom : Geometry)
    (references : List input.Atom) :
    generatedFamily input mol depth node geom references =
      LocalizedMarkedRetainedStateReader.rawStateDescriptorMap input
        (generated input mol depth geom node references) := rfl

/-! ## Unfolding and evaluation lemmas for the specification -/

/-- The tied-class selector is the adjacency selector on the descending key order. -/
theorem sourceSelectedSlots_unfold (keys : Fin 4 → RefinedKey) :
    sourceSelectedSlots keys =
      tiedEntries false (keyOrder keys (List.finRange 4))
        (adjacentBy (fun a b => some (compare (keys a) (keys b)))
          (keyOrder keys (List.finRange 4))) := rfl

/-- Evaluation of the source fallback once the frame atom of the slot is known. -/
theorem sourceFallback_eq_some (single : input.moleculeGraph.SimpleBonded)
    (family : DescriptorFamily input)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (geom : Geometry) (references : List input.Atom) (slot : Fin 4) (reference : input.Atom)
    (atomEq : frameAtom? input frame slot = some reference) :
    sourceFallback input single family target frame geom references slot =
      if Function.Injective
          (sourceKeysAt input single family target frame geom (references ++ [reference])) then
        sourceReading input geom frame
          (sourceKeysAt input single family target frame geom (references ++ [reference]))
      else none := by
  unfold sourceFallback
  rw [atomEq]
  simp only [Option.bind_some]

/-- Evaluation of the source descriptor once the molecular frame execution succeeds. -/
theorem sourceDescriptorExec?_eq_some (single : input.moleculeGraph.SimpleBonded)
    (family : DescriptorFamily input)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (geom : Geometry) (references : List input.Atom)
    (selected : input.localizedNoDoubleFourLigandFrameExec? target = some frame) :
    sourceDescriptorExec? input single family target geom references =
      sourceDescriptor input single family target frame geom references := by
  unfold sourceDescriptorExec?
  rw [selected]
  simp only [Option.bind_some]

/-! ## Realization at an actual detected occurrence -/

variable (single : input.moleculeGraph.SimpleBonded)
  (c : input.detectedMultiCenterMolecule.Center)
  (node : Node) (data : OccurrenceData input mol c node) (depth : Nat)

/-- The frame chosen by the execution for a raw state is the molecular frame of the occurrence
data, independently of the state. -/
theorem rawStateFrames_frame (state : OccurrenceAuxState)
    (unit : DetectedOccurrence input.moleculeGraph)
    (targetUnit : input.molecularFrameUnit data.target.1 = unit.1) :
    (LocalizedMarkedRetainedOrdinaryRanking.rawStateFrames input single state data.target
        data.real unit targetUnit).frame = data.frame := by
  have h := (LocalizedMarkedRetainedOrdinaryRanking.rawStateFrames input single state data.target
    data.real unit targetUnit).frameComputed
  rw [data.frameExec] at h
  exact (Option.some.inj h).symm

/-- Actual joint comparisons of the generated state are the source-key comparisons, at the
plain molecular frame of the occurrence. -/
theorem keys_compare_eq (geom : Geometry) (ctx : List input.Atom) (left right : Fin 4) :
    compare (slotKeys input mol single c node data
        (generated input mol depth geom node ctx) ctx left)
      (slotKeys input mol single c node data
        (generated input mol depth geom node ctx) ctx right) =
    compare (sourceKeysAt input single (generatedFamily input mol depth node)
        data.target data.frame geom ctx left)
      (sourceKeysAt input single (generatedFamily input mol depth node)
        data.target data.frame geom ctx right) := by
  have h := LocalizedChemicalRingJointPreparedSourceKeys.refined_compare_eq_source input single
    (generated input mol depth geom node ctx) data.target data.real
    ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl ctx
    (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) left right
  rw [rawStateFrames_frame input mol single c node data
    (generated input mol depth geom node ctx)
    ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl] at h
  exact h

/-- Strictness of the actual generated keys is strictness of the source keys. -/
theorem keys_injective_iff (geom : Geometry) (ctx : List input.Atom) :
    Function.Injective (fun slot => slotKeys input mol single c node data
        (generated input mol depth geom node ctx) ctx slot) ↔
      Function.Injective (sourceKeysAt input single (generatedFamily input mol depth node)
        data.target data.frame geom ctx) := by
  have keyEq : ∀ a b,
      slotKeys input mol single c node data (generated input mol depth geom node ctx) ctx a =
          slotKeys input mol single c node data (generated input mol depth geom node ctx) ctx b ↔
        sourceKeysAt input single (generatedFamily input mol depth node)
            data.target data.frame geom ctx a =
          sourceKeysAt input single (generatedFamily input mol depth node)
            data.target data.frame geom ctx b := by
    intro a b
    constructor
    · intro equal
      have compared : compare
          (slotKeys input mol single c node data (generated input mol depth geom node ctx) ctx a)
          (slotKeys input mol single c node data (generated input mol depth geom node ctx) ctx b) =
          Ordering.eq :=
        (LocalizedChemicalRingJointMarkerRanking.refined_compare_eq_iff _ _).mpr equal
      rw [keys_compare_eq input mol single c node data depth geom ctx a b] at compared
      exact (LocalizedChemicalRingJointMarkerRanking.refined_compare_eq_iff _ _).mp compared
    · intro equal
      have compared : compare
          (sourceKeysAt input single (generatedFamily input mol depth node)
            data.target data.frame geom ctx a)
          (sourceKeysAt input single (generatedFamily input mol depth node)
            data.target data.frame geom ctx b) = Ordering.eq :=
        (LocalizedChemicalRingJointMarkerRanking.refined_compare_eq_iff _ _).mpr equal
      rw [← keys_compare_eq input mol single c node data depth geom ctx a b] at compared
      exact (LocalizedChemicalRingJointMarkerRanking.refined_compare_eq_iff _ _).mp compared
  exact ⟨fun injective a b equal => injective ((keyEq a b).mpr equal),
    fun injective a b equal => injective ((keyEq a b).mp equal)⟩

/-- The actual descending key order of the generated state is the source-key order at the
plain molecular frame. -/
theorem keyOrder_source_eq (geom : Geometry) (ctx : List input.Atom) :
    keyOrder (sourceKeysAt input single (generatedFamily input mol depth node)
        data.target data.frame geom ctx) (List.finRange 4) =
      keyOrder (fun slot => slotKeys input mol single c node data
        (generated input mol depth geom node ctx) ctx slot) (List.finRange 4) := by
  let unit : DetectedOccurrence input.moleculeGraph :=
    ⟨input.molecularFrameUnit data.target.1, data.detected⟩
  have frameEq : (LocalizedMarkedRetainedOrdinaryRanking.rawStateFrames input single
      (generated input mol depth geom node ctx) data.target data.real unit rfl).frame =
      data.frame :=
    rawStateFrames_frame input mol single c node data
      (generated input mol depth geom node ctx) unit rfl
  have actual := LocalizedChemicalRingJointMarkerRanking.joint_sort_eq input single
    (generated input mol depth geom node ctx) data.target data.real unit rfl ctx
    (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1))
  rw [frameEq] at actual
  have source := LocalizedChemicalRingJointPreparedSourceKeys.joint_sort_eq_source input single
    (generated input mol depth geom node ctx) data.target data.real unit rfl ctx
    (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1))
  rw [frameEq] at source
  exact Option.some.inj (source.symm.trans actual)

/-- The source reading is exactly the actual enumeration readback of the generated state. -/
theorem sourceReading_eq_enumeration (geom : Geometry) (ctx : List input.Atom) :
    sourceReading input geom data.frame
        (sourceKeysAt input single (generatedFamily input mol depth node)
          data.target data.frame geom ctx) =
      readback? geom (enumeration input c (rank input mol c node data
        (fun slot => slotKeys input mol single c node data
          (generated input mol depth geom node ctx) ctx slot))) := by
  have atoms := LocalizedChemicalRingInheritedRefusalCases.ranked_eq input mol c node data
    (fun slot => slotKeys input mol single c node data
      (generated input mol depth geom node ctx) ctx slot)
  rw [data.read.atoms] at atoms
  unfold sourceReading
  rw [keyOrder_source_eq input mol single c node data depth geom ctx, atoms]
  simp only [Option.bind_some]

/-- The actual selected slots are the source tied classes. -/
theorem selectedSlots_unfold (state : OccurrenceAuxState) (references : List input.Atom) :
    LocalizedChemicalRingJointMarkerFrameExecution.selectedSlots input mol single c node data
        state references =
      tiedEntries false
        (keyOrder (slotKeys input mol single c node data state references)
          (List.finRange 4))
        (adjacentBy (fun a b => some (compare
            (slotKeys input mol single c node data state references a)
            (slotKeys input mol single c node data state references b)))
          (keyOrder (slotKeys input mol single c node data state references)
            (List.finRange 4))) := rfl

/-- The source tied classes are the actual selected slots of the generated state. -/
theorem selectedSlots_source_eq (geom : Geometry) (ctx : List input.Atom) :
    sourceSelectedSlots (sourceKeysAt input single (generatedFamily input mol depth node)
        data.target data.frame geom ctx) =
      LocalizedChemicalRingJointMarkerFrameExecution.selectedSlots input mol single c node data
        (generated input mol depth geom node ctx) ctx := by
  rw [sourceSelectedSlots_unfold,
    selectedSlots_unfold input mol single c node data (generated input mol depth geom node ctx) ctx]
  rw [keyOrder_source_eq input mol single c node data depth geom ctx]
  have functionEq : (fun a b => some (compare
        (sourceKeysAt input single (generatedFamily input mol depth node)
          data.target data.frame geom ctx a)
        (sourceKeysAt input single (generatedFamily input mol depth node)
          data.target data.frame geom ctx b))) =
      (fun a b => some (compare
        (slotKeys input mol single c node data
          (generated input mol depth geom node ctx) ctx a)
        (slotKeys input mol single c node data
          (generated input mol depth geom node ctx) ctx b))) := by
    funext a b
    rw [keys_compare_eq input mol single c node data depth geom ctx a b]
  rw [functionEq]

/-- The raw frame atom of a slot is the certified reference atom of that slot. -/
theorem frameAtom_eq_referenceAt (slot : Fin 4) :
    frameAtom? input data.frame slot = some (referenceAt input mol c node data slot) := by
  have h := data.atomAt_eq slot
  change (frameAtom? input data.frame slot).map Fin.val =
    some (referenceAt input mol c node data slot).val at h
  cases found : frameAtom? input data.frame slot with
  | none =>
      rw [found] at h
      simp only [Option.map_none] at h
      cases h
  | some atom =>
      rw [found] at h
      simp only [Option.map_some, Option.some.injEq] at h
      rw [Fin.ext h]

/-- One actual fallback equals the source fallback at the extended reference context. -/
theorem fallback_eq_source
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (geom : Geometry) (references : List input.Atom) (slot : Fin 4) :
    fallback input mol c node data depth geom references slot =
      sourceFallback input single (generatedFamily input mol depth node)
        data.target data.frame geom references slot := by
  rw [LocalizedChemicalRingJointPreparedExecution.fallback_eq input mol agreement admissible
    supported single c node data depth geom references slot]
  rw [sourceFallback_eq_some input single (generatedFamily input mol depth node) data.target
    data.frame geom references slot (referenceAt input mol c node data slot)
    (frameAtom_eq_referenceAt input mol c node data slot)]
  have injective := keys_injective_iff input mol single c node data depth geom
    (references ++ [referenceAt input mol c node data slot])
  have reading := sourceReading_eq_enumeration input mol single c node data depth geom
    (references ++ [referenceAt input mol c node data slot])
  by_cases strict : Function.Injective (fun other => slotKeys input mol single c node data
      (generated input mol depth geom node
        (references ++ [referenceAt input mol c node data slot]))
      (references ++ [referenceAt input mol c node data slot]) other)
  · rw [if_pos strict, if_pos (injective.mp strict)]
    exact reading.symm
  · rw [if_neg strict, if_neg (fun h => strict (injective.mpr h))]

/-- One actual prepared step equals the source step at the plain molecular frame. -/
theorem step_eq_source
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (geom : Geometry) (references : List input.Atom) :
    step input mol node depth geom references =
      sourceStep input single (generatedFamily input mol depth node)
        data.target data.frame geom references := by
  rw [LocalizedChemicalRingJointPreparedExecution.step_eq input mol agreement admissible
    supported single c node data depth geom references]
  unfold sourceStep
  have injective := keys_injective_iff input mol single c node data depth geom references
  have reading := sourceReading_eq_enumeration input mol single c node data depth geom references
  have mapEq : ∀ slots : List (Fin 4),
      slots.map (fallback input mol c node data depth geom references) =
        slots.map (sourceFallback input single (generatedFamily input mol depth node)
          data.target data.frame geom references) := by
    intro slots
    induction slots with
    | nil => rfl
    | cons head tail ih =>
        simp only [List.map_cons]
        rw [ih, fallback_eq_source input mol single c node data depth agreement admissible
          supported geom references head]
  by_cases strict : Function.Injective (fun other => slotKeys input mol single c node data
      (generated input mol depth geom node references) references other)
  · rw [if_pos strict, if_pos (injective.mp strict)]
    exact reading.symm
  · rw [if_neg strict, if_neg (fun h => strict (injective.mpr h))]
    rw [selectedSlots_source_eq input mol single c node data depth geom references]
    rw [mapEq (LocalizedChemicalRingJointMarkerFrameExecution.selectedSlots input mol single c
      node data (generated input mol depth geom node references) references)]

/-- **The actual prepared descriptor is the source descriptor at the molecular frame of the
occurrence data.** -/
theorem preparedDescriptor_eq_sourceDescriptor
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (geom : Geometry) (references : List input.Atom) :
    preparedDescriptor? mol (jointOperations input mol) depth geom [] (references.map Fin.val)
        node =
      sourceDescriptor input single (generatedFamily input mol depth node)
        data.target data.frame geom references := by
  rw [LocalizedChemicalRingJointPreparedExecution.descriptor_eq input mol node depth geom
      references,
    step_eq_source input mol single c node data depth agreement admissible supported geom
      references,
    step_eq_source input mol single c node data depth agreement admissible supported (mirror geom)
      references]
  unfold sourceDescriptor
  rfl

/-- The same realization with the frame lookup inside the source evaluation. -/
theorem preparedDescriptor_eq_sourceDescriptorExec
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (geom : Geometry) (references : List input.Atom) :
    preparedDescriptor? mol (jointOperations input mol) depth geom [] (references.map Fin.val)
        node =
      sourceDescriptorExec? input single (generatedFamily input mol depth node)
        data.target geom references := by
  rw [sourceDescriptorExec?_eq_some input single (generatedFamily input mol depth node)
    data.target data.frame geom references data.frameExec]
  exact preparedDescriptor_eq_sourceDescriptor input mol single c node data depth agreement
    admissible supported geom references

/-- **Every admitted reached real detected occurrence realizes the source descriptor** at the
actual target occurrence and molecular frame exhibited by the evaluator.  The occurrence data is
source correspondence derived elsewhere; it is not part of the source specification. -/
theorem reached_preparedDescriptor_eq_sourceDescriptor
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (c : input.detectedMultiCenterMolecule.Center) (node : Node)
    (reached : Reached mol node) (real : node.provenance = .realAtom)
    (current : node.atom = c.1.val) (depth : Nat) (geom : Geometry)
    (references : List input.Atom) :
    ∃ target : input.LocalizedCIPOccurrence (retainedCarrierFuel input),
      ∃ frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input),
        lookup? input node = some target ∧
        input.localizedNoDoubleFourLigandFrameExec? target = some frame ∧
        preparedDescriptor? mol (jointOperations input mol) depth geom []
            (references.map Fin.val) node =
          sourceDescriptor input single (generatedFamily input mol depth node)
            target frame geom references := by
  obtain ⟨data⟩ := LocalizedChemicalRingInheritedRefusalCases.occurrenceData_exists input mol
    agreement admissible supported single c node reached real current
  exact ⟨data.target, data.frame, data.found, data.frameExec,
    preparedDescriptor_eq_sourceDescriptor input mol single c node data depth agreement
      admissible supported geom references⟩

end

end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStep

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStep.sourceSelectedSlots_mem_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStep.sourceStep_eq_strict
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStep.sourceStep_eq_consensus
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStep.sourceDescriptor_eq_case
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStep.sourceSelectedSlots_unfold
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStep.sourceFallback_eq_some
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStep.sourceDescriptorExec?_eq_some
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStep.rawStateFrames_frame
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStep.keys_compare_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStep.keys_injective_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStep.keyOrder_source_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStep.sourceReading_eq_enumeration
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStep.selectedSlots_unfold
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStep.selectedSlots_source_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStep.frameAtom_eq_referenceAt
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStep.fallback_eq_source
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStep.step_eq_source
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStep.preparedDescriptor_eq_sourceDescriptor
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStep.preparedDescriptor_eq_sourceDescriptorExec
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStep.reached_preparedDescriptor_eq_sourceDescriptor

assert_closure_excludes TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStep.sourceKeysAt
  [TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextStages,
   TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextArm,
   TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.buildJoint?,
   TetraStereo.OneCenter.LocalizedRuleMajorReference.referenceState,
   TetraStereo.OneCenter.LocalizedMarkedRetainedOrdinaryRanking.rawStateFrames]
assert_closure_excludes TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStep.sourceSelectedSlots
  [TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextStages,
   TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextArm,
   TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.buildJoint?,
   TetraStereo.OneCenter.LocalizedRuleMajorReference.referenceState,
   TetraStereo.OneCenter.LocalizedMarkedRetainedOrdinaryRanking.rawStateFrames]
assert_closure_excludes TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStep.sourceReading
  [TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextStages,
   TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextArm,
   TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.buildJoint?,
   TetraStereo.OneCenter.LocalizedRuleMajorReference.referenceState,
   TetraStereo.OneCenter.LocalizedMarkedRetainedOrdinaryRanking.rawStateFrames]
assert_closure_excludes TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStep.sourceFallback
  [TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextStages,
   TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextArm,
   TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.buildJoint?,
   TetraStereo.OneCenter.LocalizedRuleMajorReference.referenceState,
   TetraStereo.OneCenter.LocalizedMarkedRetainedOrdinaryRanking.rawStateFrames]
assert_closure_excludes TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStep.sourceStep
  [TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextStages,
   TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextArm,
   TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.buildJoint?,
   TetraStereo.OneCenter.LocalizedRuleMajorReference.referenceState,
   TetraStereo.OneCenter.LocalizedMarkedRetainedOrdinaryRanking.rawStateFrames]
assert_closure_excludes TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStep.sourceDescriptor
  [TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextStages,
   TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextArm,
   TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.buildJoint?,
   TetraStereo.OneCenter.LocalizedRuleMajorReference.referenceState,
   TetraStereo.OneCenter.LocalizedMarkedRetainedOrdinaryRanking.rawStateFrames]
