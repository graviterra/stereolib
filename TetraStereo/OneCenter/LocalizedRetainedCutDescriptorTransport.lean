import TetraStereo.OneCenter.LocalizedRetainedCutAutomorphism
import TetraStereo.OneCenter.LocalizedRetainedGeneratedCovariance
import TetraStereo.OneCenter.LocalizedRetainedMirrorDescriptorCorrectness
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Descriptor transport on molecular predecessor cuts

A molecular automorphism transports the full retained cut, its contextual reads,
its prior key and its Rule-5 stream. Combining that transport with the proved
physical reflection law yields the complete optional descriptor outcome,
including refusal. The point hypothesis is a volume-sign law.

The general theorem asks for agreement only at reached real reads. Its executable
map-transport corollary derives that agreement for the transported descriptor
map. Neither theorem identifies a generated fixed point with that transported
map; actual-state and branch-local physical transport remain separate joins.
-/

namespace TetraStereo.OneCenter.DeclarativeCIP.RetainedCutAutomorphism

open RetainedOccurrenceCarrier RetainedCutArm
open CertifiedLocalizedCIPInput
open LocalizedRetainedMirrorDescriptorCorrectness
open scoped Classical

noncomputable section
universe u
variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
variable (molecule : MoleculeGraph Atom) {root : Atom}

/-- Full key transport is derived from the prior and common-senior reading. -/
theorem cut_rule5Key (e : molecule.Aut) (focus : Nodes molecule root)
    (incoming : Option (Nodes molecule root)) (anchor : CutAnchor focus incoming)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule)
    (reads : ReadsAgree molecule e imageMap sourceMap unit
      (cutRetainedArm molecule root focus incoming anchor)) (W D : ℕ) :
    retainedCompleteLigandRule5KeyAt molecule imageMap (mapDetected molecule e unit)
        (cutRetainedArm molecule ((e : Equiv.Perm Atom) root) (imageNode e focus)
          (incoming.map (imageNode e)) (cutAnchor_image e focus incoming anchor)) W D =
      retainedCompleteLigandRule5KeyAt molecule sourceMap unit
        (cutRetainedArm molecule root focus incoming anchor) W D := by
  unfold retainedCompleteLigandRule5KeyAt
  rw [cut_priorKey e focus incoming anchor imageMap sourceMap unit reads,
    cut_rule5Readings e focus incoming anchor imageMap sourceMap unit reads]

/-- Physical descriptor transport on four predecessor cuts. All key and
reference transport is derived, rather than supplied as comparison assumptions. -/
theorem cut_completeRootOutcome_transport
    (e : molecule.Aut) (mirror : Bool) (slotPerm : Equiv.Perm (Fin 4))
    (sourceMap imageMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule)
    (focus : Fin 4 → Nodes molecule root)
    (incoming : Fin 4 → Option (Nodes molecule root))
    (anchor : ∀ slot, CutAnchor (focus slot) (incoming slot))
    (reads : ∀ slot, ReadsAgree molecule e imageMap
      (if mirror then sourceMap.reflect else sourceMap) unit
      (cutRetainedArm molecule root (focus slot) (incoming slot) (anchor slot)))
    (sourcePoints imagePoints : Fin 4 → CartesianPoint3) (W D : ℕ)
    (outcome : Option LocalizedAuxiliaryLabel)
    (sign : rationalVolumeSign (slotVolume imagePoints) =
      physicalMirrorFactor mirror * permHandedness slotPerm *
        rationalVolumeSign (slotVolume sourcePoints)) :
    CompleteRootOutcome
        (fun slot => retainedCompleteLigandRule5KeyAt molecule imageMap
          (mapDetected molecule e unit)
          (cutRetainedArm molecule ((e : Equiv.Perm Atom) root)
            (imageNode e (focus (slotPerm⁻¹ slot)))
            ((incoming (slotPerm⁻¹ slot)).map (imageNode e))
            (cutAnchor_image e (focus (slotPerm⁻¹ slot)) (incoming (slotPerm⁻¹ slot))
              (anchor (slotPerm⁻¹ slot)))) W D)
        imagePoints (Option.map (retainedPhysicalLetter mirror) outcome) ↔
      CompleteRootOutcome
        (fun slot => retainedCompleteLigandRule5KeyAt molecule sourceMap unit
          (cutRetainedArm molecule root (focus slot) (incoming slot) (anchor slot)) W D)
        sourcePoints outcome := by
  let graphs : Fin 4 → RootedDigraph Atom :=
    fun slot => cutRetainedArm molecule root (focus slot) (incoming slot) (anchor slot)
  have keyEq : (fun slot => retainedCompleteLigandRule5KeyAt molecule imageMap
      (mapDetected molecule e unit)
      (cutRetainedArm molecule ((e : Equiv.Perm Atom) root)
        (imageNode e (focus (slotPerm⁻¹ slot)))
        ((incoming (slotPerm⁻¹ slot)).map (imageNode e))
        (cutAnchor_image e (focus (slotPerm⁻¹ slot)) (incoming (slotPerm⁻¹ slot))
          (anchor (slotPerm⁻¹ slot)))) W D) =
      retainedImageKey molecule sourceMap unit mirror graphs slotPerm W D := by
    funext slot
    exact cut_rule5Key molecule e (focus (slotPerm⁻¹ slot)) (incoming (slotPerm⁻¹ slot))
      (anchor (slotPerm⁻¹ slot)) imageMap
      (if mirror then sourceMap.reflect else sourceMap) unit
      (reads (slotPerm⁻¹ slot)) W D
  rw [keyEq]
  exact completeRootOutcome_retainedPhysical molecule sourceMap unit mirror graphs slotPerm
    sourcePoints imagePoints W D outcome sign

end

section CertifiedMap

variable (input : CertifiedLocalizedCIPInput)

/-- The declarative and actual occurrence transports retain exactly the same
root and full path, not merely the same current atom. -/
theorem mapDetected_eq_transportDetectedOccurrence
    (e : input.moleculeGraph.Aut) (unit : DetectedOccurrence input.moleculeGraph) :
    mapDetected input.moleculeGraph e unit = input.transportDetectedOccurrence e unit := by
  apply Subtype.ext
  rfl

/-- The transported descriptor map satisfies the reached-read relation on every
retained graph, without an assumed reader correspondence. -/
theorem readsAgree_transportDescriptorMap (e : input.moleculeGraph.Aut)
    (sourceMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph)
    (graph : RootedDigraph input.Atom) :
    ReadsAgree input.moleculeGraph e (input.transportDescriptorMap e sourceMap)
      sourceMap unit graph := by
  intro node steps occurrence real ancestors context
  rw [mapDetected_eq_transportDetectedOccurrence input]
  exact input.transportDescriptorMap_transportDetected e sourceMap occurrence

end CertifiedMap

end TetraStereo.OneCenter.DeclarativeCIP.RetainedCutAutomorphism

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedCutAutomorphism.cut_rule5Key
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedCutAutomorphism.cut_completeRootOutcome_transport
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedCutAutomorphism.mapDetected_eq_transportDetectedOccurrence
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedCutAutomorphism.readsAgree_transportDescriptorMap
