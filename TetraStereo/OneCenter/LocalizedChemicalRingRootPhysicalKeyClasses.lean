import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootKeyCovariance
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPromotionCancellation
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Actual root key classes have an independent physical interpretation, without pairwise
proper distinguishability. A class consists exactly of ligands related by a molecular symmetry
fixing the center and retained references and preserving every other center's configuration.
This interprets key ties, not absolute letters or every success/refusal outcome. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingRootPhysicalKeyClasses

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData referenceAt observedGeometry)
open LocalizedChemicalRingJointPreparedExecution (keys)
open LocalizedChemicalRingJointPreparedRootPhysicalTransport (root_history)
open LocalizedChemicalRingJointPreparedRootPromotionCancellation (root_tie_boundaryProper)
open LocalizedChemicalRingJointPreparedRootKeyCovariance (root_current_key_action)
open LocalizedChemicalRingResidualThreeCycleRefusal (slotAction referenceAt_action)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedGenericMarkedRecalculation (structuralDepth)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

/-- Independent physical transport of root ligands; no generated key or label occurs here. -/
def PhysicalTransport (input : CertifiedLocalizedCIPInput)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (c : input.detectedMultiCenterMolecule.Center) (references : List input.Atom)
    (left right : Fin 4) : Prop :=
  ∃ e : input.detectedMultiCenterMolecule.Aut,
    (e : Equiv.Perm input.Atom) c.1 = c.1 ∧
    (e : Equiv.Perm input.Atom) (input.detectedMultiCenterMolecule.ligandAtomAt c left) =
      input.detectedMultiCenterMolecule.ligandAtomAt c right ∧
    (∀ atom ∈ references, (e : Equiv.Perm input.Atom) atom = atom) ∧
    ∀ d : input.detectedMultiCenterMolecule.Center, d ≠ c →
      relativeSign input.detectedMultiCenterMolecule cfg e d = 1

noncomputable section

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
    ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
  (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
  (data : OccurrenceData input mol c node) (reached : Reached mol node)
  (current : node.atom = c.1.val) (rootAddress : data.target.1.address = [])
  (references : List input.Atom) (reflected : Bool)

include agreement admissible supported charge calibrated reached current rootAddress in
/-- Every distinct-slot tie is equivalent to independent physical transport at any root. -/
theorem keys_eq_iff_physicalTransport (left right : Fin 4) (distinct : left ≠ right) :
    keys input mol single c node data (structuralDepth mol node)
        (observedGeometry input reflected) references left =
      keys input mol single c node data (structuralDepth mol node)
        (observedGeometry input reflected) references right ↔
    PhysicalTransport input cfg c references (data.ligandOf left) (data.ligandOf right) := by
  have history := root_history input mol c node data rootAddress current
  constructor
  · intro tied
    obtain ⟨e, fixed, moved, keeps, proper⟩ := root_tie_boundaryProper input mol agreement
      admissible supported single charge cfg calibrated c node data reached rootAddress current
      references reflected left right distinct tied
    refine ⟨e, fixed c.1 (by simp [history]), moved, keeps, ?_⟩
    intro d different
    apply proper d
    rw [history]
    simpa only [List.mem_singleton] using
      (show d.1 ≠ c.1 from fun same => different (Subtype.ext same))
  · rintro ⟨e, fixed, moved, keeps, proper⟩
    have historyFixed : ∀ atom ∈ data.target.1.node.history,
        (e : Equiv.Perm input.Atom) atom = atom := by
      intro atom member
      have same : atom = c.1 := by simpa only [history, List.mem_singleton] using member
      simpa only [same] using fixed
    have properOff : ∀ d : input.detectedMultiCenterMolecule.Center,
        d.1 ∉ data.target.1.node.history →
        relativeSign input.detectedMultiCenterMolecule cfg e d = 1 := by
      intro d outside
      apply proper d
      intro same
      subst d
      exact outside (by simp [history])
    have centerFixed : input.detectedMultiCenterMolecule.centerPerm e c = c := Subtype.ext fixed
    have action : slotAction input mol e c node data left = right := by
      apply data.ligandOf.injective
      apply input.detectedMultiCenterMolecule.ligandAtomAt_injective c
      exact (referenceAt_action input mol e c node data centerFixed left).trans moved
    have preserved := root_current_key_action input mol agreement admissible supported single
      cfg calibrated c node data reached current rootAddress e historyFixed references keeps
      properOff (structuralDepth mol node) reflected left
    rw [action] at preserved
    exact preserved.symm

include agreement admissible supported charge calibrated reached current rootAddress in
/-- Actual strict root priorities are equivalent to absence of every distinct physical transport. -/
theorem keys_injective_iff_no_physicalTransport :
    Function.Injective (keys input mol single c node data (structuralDepth mol node)
      (observedGeometry input reflected) references) ↔
    ∀ left right : Fin 4, left ≠ right →
      ¬ PhysicalTransport input cfg c references (data.ligandOf left) (data.ligandOf right) := by
  constructor
  · intro injective left right distinct transport
    exact distinct (injective ((keys_eq_iff_physicalTransport input mol agreement admissible
      supported single charge cfg calibrated c node data reached current rootAddress references
      reflected left right distinct).mpr transport))
  · intro noTransport left right tied
    by_contra distinct
    exact noTransport left right distinct ((keys_eq_iff_physicalTransport input mol agreement
      admissible supported single charge cfg calibrated c node data reached current rootAddress
      references reflected left right distinct).mp tied)

end
end TetraStereo.OneCenter.LocalizedChemicalRingRootPhysicalKeyClasses

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRootPhysicalKeyClasses.PhysicalTransport
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRootPhysicalKeyClasses.keys_eq_iff_physicalTransport
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRootPhysicalKeyClasses.keys_injective_iff_no_physicalTransport
