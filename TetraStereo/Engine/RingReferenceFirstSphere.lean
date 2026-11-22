import TetraStereo.Engine.RingReachableReferencePolicy

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option Elab.async false

namespace TetraStereo.Engine.RingReferenceFirstSphere
open OneCenter OneCenter.CertifiedLocalizedCIPInput OneCenter.DeclarativeCIP
open RetainedOccurrenceCarrier RetainedCutArm LocalizedRetainedSourceCutFrames
open LocalizedChemicalRingJointPreparedSourceQueries LocalizedChemicalRingInheritedRefusalCases
open LocalizedChemicalRingRegeneratedLifetime RingReachableReferencePolicy
open scoped Classical
noncomputable section

/-- The first occupied entry of the Rule 1a vector is the observed head atom. -/
private def rootZ (column : List (Certificate.CanonicalSphereKey.Key ℤ)) : WithBot ℤ :=
  (((column.getD 0 []).getD 0 []).getD 0 ⊥)

private theorem rootZ_key {A : Type} [Fintype A] [DecidableEq A]
    (graph : RootedDigraph A) (W D : Nat) (observe : ConstitutionalRule → graph.Node → ℤ)
    (n : graph.Node) :
    rootZ (ruleKeyWithObservations graph W D observe n) = (observe .rule1aAtomicNumber n : WithBot ℤ) := by
  rw [ruleKeyWithObservations_eq]
  rfl

private theorem root_label {A : Type} [Fintype A] [DecidableEq A]
    (graph : MoleculeGraph A) (root : A) (f a : CarrierNode A)
    (valid : SourceCutAdmissible graph root f a) :
    let g := sourceCutArm graph root f a
    g.label g.root = CarrierNode.label f := by
  obtain ⟨hf,ha,anchor⟩ := valid
  rw [sourceCutArm_eq graph root (focus := ⟨f,hf⟩) (incoming := ⟨a,ha⟩) anchor]
  cases f <;> rfl

variable {i : CertifiedLocalizedCIPInput} {m : RawMolecule}
variable (single : i.moleculeGraph.SimpleBonded) (frame : FrameFamily i m)

private theorem rootZ_at (q : SourceQuery i m) (j : Fin 4) :
    rootZ (structuralColumn single frame q j) =
      ((Int.ofNat (i.moleculeGraph.atomZ (i.detectedMultiCenterMolecule.ligandAtomAt
        (frame q).1 ((frame q).2.ligandOf j)))) : WithBot ℤ) := by
  let d := (frame q).2
  let cur := d.frame.cursorAt j
  let center := (frame q).1
  let atom := i.detectedMultiCenterMolecule.ligandAtomAt center (d.ligandOf j)
  have current : cur.occurrence.1.node.current? = some atom :=
    Option.map_injective Fin.val_injective (d.atomAt_eq j)
  have frameExec : i.localizedOccurrenceFourLigandFrame? d.target = some d.frame :=
    (i.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame? d.target).symm.trans d.frameExec
  have child : cur ∈ i.executableLocalizedRerootChildren ⟨d.target,none⟩ := by
    rw [← i.localizedOccurrenceFourLigandFrame_cursors_eq_executable d.target d.frame frameExec]
    exact List.get_mem d.frame.cursors (Fin.cast d.frame.length_eq.symm j)
  let graph := sourceCutArm i.moleculeGraph cur.occurrence.1.root
    (i.occurrenceCarrierNode single cur.occurrence) (i.occurrenceCarrierNode single d.target)
  have label : graph.label graph.root = cur.occurrence.1.node.toDeclarativeLabel :=
    (root_label _ _ _ _ (sourceCutAdmissible_of_executableChild i single _ _ child)).trans
      (i.occurrenceCarrierNode_label single cur.occurrence)
  change rootZ (ruleKeyWithObservations graph _ _ (retainedContextNodeObservation i.moleculeGraph graph
    (i.molecularFrameUnit d.target.1)) graph.root) = ((i.moleculeGraph.atomZ atom : ℤ) : WithBot ℤ)
  rw [rootZ_key]
  simp [retainedContextNodeObservation,retainedContextRuleValue,priorityValue,ruleValue,
    nodeAtomicNumber,label,OfficialCIPNode.toDeclarativeLabel,current]

/-- Pairwise distinct atomic numbers of the four physical neighbors suffice at every
original occurrence of the center, including inward ligands and ring duplicates. -/
theorem injective_of_distinct_neighbors (q : SourceQuery i m)
    (distinct : ∀ a b : i.Atom, i.moleculeGraph.Adj (frame q).1.val a →
      i.moleculeGraph.Adj (frame q).1.val b → i.moleculeGraph.atomZ a = i.moleculeGraph.atomZ b → a = b) :
    Function.Injective (structuralColumn single frame q) := by
  intro a b same
  have z := congrArg rootZ same
  rw [rootZ_at,rootZ_at] at z
  have eqz := WithBot.coe_injective z
  apply (frame q).2.ligandOf.injective
  apply i.detectedMultiCenterMolecule.ligandAtomAt_injective (frame q).1
  apply distinct
  · exact i.detectedMultiCenterMolecule.ligandAtomAt_adj ..
  · exact i.detectedMultiCenterMolecule.ligandAtomAt_adj ..
  · exact Int.ofNat.inj eqz


/-- For a canonical molecular frame, a collision in the pre-stereo column
can occur only at the exceptional atom when every other detected carbon or
tetrahedral center has distinct neighboring atomic numbers. -/
theorem only_exceptional_atom
    (agree : m.AuthoritativeStructureAgreement i.certified.input) (admit : m.StereochemicalAdmissible)
    (supported : ∀ b ∈ m.bonds, b.kind.IsLocalizedCovalent) (atom : Nat)
    (apart : ∀ c : i.detectedMultiCenterMolecule.Center, c.val.val ≠ atom → ∀ a b : i.Atom,
      i.moleculeGraph.Adj c.val a → i.moleculeGraph.Adj c.val b →
      i.moleculeGraph.atomZ a = i.moleculeGraph.atomZ b → a = b)
    (q : SourceQuery i m)
    (bad : ¬ Function.Injective (structuralColumn single
      (LocalizedChemicalRingRegeneratedLifetime.frames i m agree admit supported single) q)) :
    q.val.atom = atom := by
  let family := LocalizedChemicalRingRegeneratedLifetime.frames i m agree admit supported single
  have focus : q.val.atom = (family q).1.val.val :=
    (sourceQuery_data_exists i m agree admit supported single q).choose_spec.1
  by_contra different
  apply bad
  apply injective_of_distinct_neighbors
  exact apart (family q).1 (by simpa only [← focus] using different)

/-- Every unmarked descriptor, including refusal and mirror case, is
independent of older marks for this graph class. A single exceptional center
may enter promotion with any number of strict detected centers elsewhere. -/
theorem agree_of_one_repeated_element_center
    (agree : m.AuthoritativeStructureAgreement i.certified.input) (admit : m.StereochemicalAdmissible)
    (supported : ∀ b ∈ m.bonds, b.kind.IsLocalizedCovalent) (atom : Nat)
    (apart : ∀ c : i.detectedMultiCenterMolecule.Center, c.val.val ≠ atom → ∀ a b : i.Atom,
      i.moleculeGraph.Adj c.val a → i.moleculeGraph.Adj c.val b →
      i.moleculeGraph.atomZ a = i.moleculeGraph.atomZ b → a = b)
    (q : SourceQuery i m) (g : LocalizedGenericMarkedRecalculation.Geometry) :
    let family := LocalizedChemicalRingRegeneratedLifetime.frames i m agree admit supported single
    accumulated single family g [] q = replaced single family g [] q :=
  agree_of_one_collision_atom single _ admit atom
    (only_exceptional_atom single agree admit supported atom apart) q g

end
end TetraStereo.Engine.RingReferenceFirstSphere
assert_kernel_only TetraStereo.Engine.RingReferenceFirstSphere.injective_of_distinct_neighbors
assert_kernel_only TetraStereo.Engine.RingReferenceFirstSphere.only_exceptional_atom
assert_kernel_only TetraStereo.Engine.RingReferenceFirstSphere.agree_of_one_repeated_element_center
