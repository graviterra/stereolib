import TetraStereo.OneCenter.LocalizedChemicalRingOrientationInduction
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Which generated labels the symmetry hypothesis actually depends on

The immediate-frame step consults its inherited context only when the inherited reference atom lies
in the current frame (`rawStep_ctx_irrelevant`, `rawStep_ctx_adjacent`); otherwise it reads the
consensus of its own eligible references exactly as with no context. Hence the label symmetry
`Symmetric` of `LocalizedChemicalRingOrientationInduction` reduces (`symmetric_of_consensus_adjacent`)
to two families of facts about the actual recursion under `σ`:

* **consensus symmetry**: at every reached occurrence, the no-context descriptor at the `σ`-image
  equals the one at the occurrence;
* **adjacent symmetry**: at every reached occurrence whose frame contains the reference atom `m`,
  the single-reference descriptor for `σ m` at the `σ`-image equals the one for `m`.

`RecordedSymmetric` is label symmetry under the fixed reference `r` at EVERY depth and EVERY reached
occurrence; it is a stronger statement than the equality of one finite root state, and it is not
derived here from a root tie. Assuming it, `recorded_consensus` and `recorded_adjacent` supply the
consensus family at occurrences whose frame avoids `r` and the adjacent family for `m = r` only.
What `RecordedSymmetric` does not cover are the consensus readings at occurrences adjacent to `r`
and the single-reference readings for the inner references `m ≠ r` at occurrences adjacent to `m`.
The distant-reference step uses its inherited reading even outside the frame, so it has no such
reduction.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingOrientationContexts

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingRelabel LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingSenseTransport
open LocalizedChemicalRingCompletenessGeneralPhysical (structuralSymmetry_of_aut)
open LocalizedChemicalRingOrientationInduction
open LocalizedMarkedOperationEvaluator (Operations markedReading? underWith)
open LocalizedMarkedReachableConfigurations
open LocalizedMarkedReachedFrameNeighbors (reached_atom_valid)
open LocalizedMarkedCertifiedTerminalRefusal (raw_single)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedGenericMarkedRecalculation (Geometry frameAtoms? consensus appendFacts? mirror)

/-! ## The inherited context matters only inside the frame -/

section Step

variable (mol : RawMolecule) (ops : Operations)

theorem rawStep_ctx_irrelevant (geom : Geometry) (state : OccurrenceAuxState) (m : Nat)
    (node : RawMolecule.CanonicalBranchNode) (under : Nat → OccurrenceAuxState) (atoms : List Nat)
    (frame : frameAtoms? mol node = some atoms) (absent : m ∉ atoms) :
    LocalizedMarkedOperationEvaluator.rawStep? mol ops geom state (some m) node under =
      LocalizedMarkedOperationEvaluator.rawStep? mol ops geom state none node under := by
  unfold LocalizedMarkedOperationEvaluator.rawStep?
  rw [frame]
  cases ops.ordinary state node with
  | none => rfl
  | some result =>
      obtain ⟨sorted, adjacent⟩ := result
      simp only [Option.bind_eq_bind, Option.bind_some]
      split_ifs
      all_goals first
        | rfl
        | exact absurd (List.contains_iff_mem.mp ‹atoms.contains m = true›) absent

theorem rawStep_ctx_adjacent (geom : Geometry) (state : OccurrenceAuxState) (m : Nat)
    (node : RawMolecule.CanonicalBranchNode) (under : Nat → OccurrenceAuxState) (atoms : List Nat)
    (sorted : List Nat) (adjacent : List (Option Ordering))
    (frame : frameAtoms? mol node = some atoms)
    (ordered : ops.ordinary state node = some (sorted, adjacent)) (nodup : atoms.Nodup)
    (consistentOrder : LocalizedGenericMarkedRecalculation.consistent adjacent = true)
    (tied : LocalizedGenericMarkedRecalculation.strict adjacent = false) (present : m ∈ atoms) :
    LocalizedMarkedOperationEvaluator.rawStep? mol ops geom state (some m) node under =
      (appendFacts? state (under m)).bind fun temp => markedReading? mol ops geom temp node m := by
  simp [LocalizedMarkedOperationEvaluator.rawStep?, frame, ordered, nodup, consistentOrder, tied,
    present]

/-- The generated descriptor ignores an inherited reference outside the frame. -/
theorem descriptor_ctx_irrelevant (depth : Nat) (geom : Geometry) (m : Nat)
    (node : RawMolecule.CanonicalBranchNode) (atoms : List Nat)
    (frame : frameAtoms? mol node = some atoms) (absent : m ∉ atoms) :
    LocalizedMarkedOperationEvaluator.descriptor? mol ops depth geom [] (some m) node =
      LocalizedMarkedOperationEvaluator.descriptor? mol ops depth geom [] none node := by
  unfold LocalizedMarkedOperationEvaluator.descriptor? LocalizedMarkedOperationEvaluator.descriptorWith?
    LocalizedMarkedOperationEvaluator.rawWith?
  rw [rawStep_ctx_irrelevant mol ops geom [] m node _ atoms frame absent,
    rawStep_ctx_irrelevant mol ops (mirror geom) [] m node _ atoms frame absent]

theorem descriptor_none_of_no_frame (depth : Nat) (geom : Geometry) (ctx : Option Nat)
    (node : RawMolecule.CanonicalBranchNode) (frame : frameAtoms? mol node = none) :
    LocalizedMarkedOperationEvaluator.descriptor? mol ops depth geom [] ctx node = none := by
  rw [descriptor_eq_descriptorWith]
  exact descriptorWith_none_of_frame mol ops _ (rawStep_noFrame mol ops) depth geom [] ctx node frame

end Step

/-! ## Reduction of the symmetry hypothesis -/

section Reduction

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (e : input.detectedMultiCenterMolecule.Aut)
  (atomsPres : ∀ x, x < mol.atomCount →
    mol.atomAt? (relabelOf input (e : Equiv.Perm input.Atom) x) = mol.atomAt? x)

/-- No-context (consensus) label symmetry at every reached occurrence. -/
def ConsensusSymmetric (g : Geometry) : Prop :=
  ∀ depth node, Reached mol node →
    LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth g [] none
        (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node) =
      LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth g [] none node

/-- Single-reference label symmetry at every reached occurrence whose frame contains the
reference. -/
def AdjacentSymmetric (g : Geometry) : Prop :=
  ∀ depth node, Reached mol node → ∀ atoms, frameAtoms? mol node = some atoms → ∀ m ∈ atoms,
    LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth g []
        (some (relabelOf input (e : Equiv.Perm input.Atom) m))
        (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node) =
      LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth g []
        (some m) node

include agreement admissible supported single atomsPres in
/-- **Reduction.** Consensus symmetry and adjacent symmetry (for the geometry and its mirror)
give the full label symmetry used by the orientation induction. -/
theorem symmetric_of_consensus_adjacent
    (consensusSym : ∀ g, (g = inputGeometry input ∨ g = mirror (inputGeometry input)) →
      ConsensusSymmetric input mol e g)
    (adjacentSym : ∀ g, (g = inputGeometry input ∨ g = mirror (inputGeometry input)) →
      AdjacentSymmetric input mol e g) :
    Symmetric input mol e := by
  have wellFormed := admissible.1.1
  have unique := admissible.1.2
  have rawSingle := raw_single mol input agreement wellFormed unique supported single
  have sym := structuralSymmetry_of_aut input mol agreement admissible supported e atomsPres
  intro g hg depth ctx node reached
  have valid := reached_atom_valid mol wellFormed node reached
  cases ctx with
  | none => exact consensusSym g hg depth node reached
  | some m =>
      cases frame : frameAtoms? mol node with
      | none =>
          rw [descriptor_none_of_no_frame mol _ depth g _ node frame,
            descriptor_none_of_no_frame mol _ depth g _ _
              (frameAtoms_map_none sym wellFormed unique rawSingle node frame valid)]
      | some atoms =>
          by_cases present : m ∈ atoms
          · exact adjacentSym g hg depth node reached atoms frame m present
          · obtain ⟨atoms', frame', perm⟩ :=
              frameAtoms_map_some sym wellFormed unique rawSingle node atoms frame valid
            have absent' : relabelOf input (e : Equiv.Perm input.Atom) m ∉ atoms' := by
              intro member
              rw [perm.mem_iff, List.mem_map] at member
              obtain ⟨y, hy, eq⟩ := member
              exact present (sym.injective eq ▸ hy)
            rw [Option.map_some, descriptor_ctx_irrelevant mol _ depth g _ _ atoms' frame' absent',
              descriptor_ctx_irrelevant mol _ depth g m node atoms frame present]
            exact consensusSym g hg depth node reached

/-! ## What the root state records -/

variable (c : input.detectedMultiCenterMolecule.Center)
  (fixed : input.detectedMultiCenterMolecule.centerPerm e c = c)
  (k : Fin 4) (fixedRef : input.detectedMultiCenterMolecule.ligandPermAt e c k = k)

/-- Label symmetry of the recorded root-state context: the reference `r_k` fixed by `σ`. -/
def RecordedSymmetric (g : Geometry) : Prop :=
  ∀ depth node, Reached mol node →
    LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth g []
        (some (input.detectedMultiCenterMolecule.ligandAtomAt c k).val)
        (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node) =
      LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth g []
        (some (input.detectedMultiCenterMolecule.ligandAtomAt c k).val) node

include agreement admissible supported single atomsPres fixed fixedRef in
/-- Recorded symmetry supplies the consensus family at occurrences whose frame avoids the
recorded reference. -/
theorem recorded_consensus (g : Geometry) (recorded : RecordedSymmetric input mol e c k g)
    (depth : Nat) (node : RawMolecule.CanonicalBranchNode) (reached : Reached mol node)
    (atoms : List Nat) (frame : frameAtoms? mol node = some atoms)
    (absent : (input.detectedMultiCenterMolecule.ligandAtomAt c k).val ∉ atoms) :
    LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth g [] none
        (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node) =
      LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth g [] none
        node := by
  have wellFormed := admissible.1.1
  have unique := admissible.1.2
  have rawSingle := raw_single mol input agreement wellFormed unique supported single
  have sym := structuralSymmetry_of_aut input mol agreement admissible supported e atomsPres
  have valid := reached_atom_valid mol wellFormed node reached
  obtain ⟨atoms', frame', perm⟩ := frameAtoms_map_some sym wellFormed unique rawSingle node atoms
    frame valid
  have absent' : (input.detectedMultiCenterMolecule.ligandAtomAt c k).val ∉ atoms' := by
    intro member
    rw [perm.mem_iff, List.mem_map] at member
    obtain ⟨y, hy, eq⟩ := member
    have fixedAtom := LocalizedChemicalRingCompletenessOrbit.relabel_ligand_perm input e c fixed k
    rw [fixedRef] at fixedAtom
    rw [← fixedAtom] at eq
    exact absent (sym.injective eq ▸ hy)
  rw [← descriptor_ctx_irrelevant mol _ depth g _ _ atoms' frame' absent',
    ← descriptor_ctx_irrelevant mol _ depth g _ node atoms frame absent]
  exact recorded depth node reached

include fixed fixedRef in
/-- Recorded symmetry is the adjacent family for the recorded reference itself. -/
theorem recorded_adjacent (g : Geometry) (recorded : RecordedSymmetric input mol e c k g)
    (depth : Nat) (node : RawMolecule.CanonicalBranchNode) (reached : Reached mol node) :
    LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth g []
        (some (relabelOf input (e : Equiv.Perm input.Atom)
          (input.detectedMultiCenterMolecule.ligandAtomAt c k).val))
        (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node) =
      LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth g []
        (some (input.detectedMultiCenterMolecule.ligandAtomAt c k).val) node := by
  have fixedAtom := LocalizedChemicalRingCompletenessOrbit.relabel_ligand_perm input e c fixed k
  rw [fixedRef] at fixedAtom
  rw [fixedAtom]
  exact recorded depth node reached

end Reduction

end TetraStereo.OneCenter.LocalizedChemicalRingOrientationContexts

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationContexts.rawStep_ctx_irrelevant
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationContexts.rawStep_ctx_adjacent
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationContexts.descriptor_ctx_irrelevant
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationContexts.symmetric_of_consensus_adjacent
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationContexts.recorded_consensus
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationContexts.recorded_adjacent
