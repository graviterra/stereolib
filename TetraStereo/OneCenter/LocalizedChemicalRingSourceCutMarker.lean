import TetraStereo.OneCenter.LocalizedChemicalRingSourceCutWindows
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceTerminal
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! One deterministic molecular-cut marker, before any evaluator is chosen.
The real-focus branch uses the molecular rerooted parent, source-cut priors and all ordered
marks. The ring-focus branch is the terminal marker. Admissibility, prior windows and graphs
are molecular constructions. Outside admitted cuts the function returns the empty marker;
the actual-input bridge proves that this branch is never used.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingSourceCutMarker

open DeclarativeCIP DeclarativeCIP.RetainedOccurrenceCarrier DeclarativeCIP.RetainedCutArm
open LocalizedRetainedSourceCutFrames LocalizedChemicalRingSourceCutWindows
open LocalizedChemicalRingJointMarkerKey
open LocalizedChemicalRingJointPreparedIndependentModelSourceJointKey

noncomputable section
open scoped Classical
universe u

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom) (root : Atom)

/-- Source-only joint marker at a molecular predecessor cut. The caller supplies a candidate
descriptor map, never compiled trees, comparison callbacks, or desired outputs. -/
def sourceCutMarker (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (focus incoming : CarrierNode Atom) (references : List Atom) (W D : Nat) : JointMarker :=
  match focus with
  | .real path =>
      if admitted : SourceCutAdmissible molecule root (.real path) incoming then
        let arm : RealCutArm molecule root := {
          descriptorMap := descriptorMap
          focus := path
          hfocus := admitted.choose
          incoming := some ⟨incoming, admitted.choose_spec.choose⟩
          anchor := realAnchor admitted.choose_spec.choose_spec
          W := allCutWidth molecule
          D := allCutDepth molecule
          references := references
        }
        arm.markerAt W D references.length arm.graph.root
      else []
  | .ring path atom =>
      if SourceCutAdmissible molecule root (.ring path atom) incoming then
        assembleJointMarker W D references.length
          (references.map fun reference => if atom = reference then 1 else 0) []
      else []

/-- At a real admitted cut the deterministic definition is the concrete real-cut marker. -/
theorem sourceCutMarker_real
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (path : List Atom) (hpath : SimpleFrom molecule root path)
    (incoming : Nodes molecule root) (anchor : RealCutAnchor path hpath (some incoming))
    (references : List Atom) (W D : Nat) :
    sourceCutMarker molecule root descriptorMap (.real path) incoming.1 references W D =
      let arm : RealCutArm molecule root := {
        descriptorMap := descriptorMap, focus := path, hfocus := hpath,
        incoming := some incoming, anchor := anchor,
        W := allCutWidth molecule, D := allCutDepth molecule, references := references }
      arm.markerAt W D references.length arm.graph.root := by
  have admitted : SourceCutAdmissible molecule root (.real path) incoming.1 :=
    ⟨hpath, incoming.2, CutAnchor.realChild (anchor incoming rfl)⟩
  simp only [sourceCutMarker, dif_pos admitted]

/-- The definition is independent of the proof-bearing real-cut packaging. -/
theorem sourceCutMarker_eq_realArm (arm : RealCutArm molecule root)
    (incoming : Nodes molecule root) (incomingEq : arm.incoming = some incoming)
    (widthEq : arm.W = allCutWidth molecule) (depthEq : arm.D = allCutDepth molecule)
    (W D : Nat) :
    sourceCutMarker molecule root arm.descriptorMap (.real arm.focus) incoming.1 arm.references W D =
      arm.markerAt W D arm.references.length arm.graph.root := by
  rcases arm with ⟨descriptorMap, path, hpath, parent, anchor, priorW, priorD, references⟩
  dsimp only at incomingEq widthEq depthEq ⊢
  subst parent
  subst priorW
  subst priorD
  exact sourceCutMarker_real molecule root descriptorMap path hpath incoming anchor references W D

/-- The terminal source marker carries the duplicated atom's ordered reference observations. -/
theorem sourceCutMarker_ring
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    {path : List Atom} {atom : Atom}
    (valid : CarrierNode.Valid molecule root (.ring path atom))
    (references : List Atom) (W D : Nat) :
    sourceCutMarker molecule root descriptorMap (.ring path atom) (.real path) references W D =
      assembleJointMarker W D references.length
        (references.map fun reference => if atom = reference then 1 else 0) [] := by
  have admitted : SourceCutAdmissible molecule root (.ring path atom) (.real path) :=
    ⟨valid, valid.1, CutAnchor.ringParent⟩
  simp only [sourceCutMarker, if_pos admitted]

end
end TetraStereo.OneCenter.LocalizedChemicalRingSourceCutMarker

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSourceCutMarker.sourceCutMarker_real
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSourceCutMarker.sourceCutMarker_eq_realArm
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSourceCutMarker.sourceCutMarker_ring

assert_closure_excludes TetraStereo.OneCenter.LocalizedChemicalRingSourceCutMarker.sourceCutMarker
  [TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextStages,
   TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextArm,
   TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.buildJoint?,
   TetraStereo.OneCenter.LocalizedRuleMajorReference.referenceState]
