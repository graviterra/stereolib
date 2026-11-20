import TetraStereo.OneCenter.LocalizedChemicalRingOrientationResidue
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Orientation from the RECORDED labels plus two σ-independent evaluator properties

`LocalizedChemicalRingOrientationInduction` needs label symmetry in every context. Here the
inductive step is reorganised around the decoder: at an occurrence whose descriptor under some
context is a `some` label that is `σ`-symmetric, the sign is already `1`, so the descriptors under
ALL contexts agree with their pulled-back versions. The only occurrences that could break the
induction are those whose consulted label is refused. Two properties of the actual immediate-frame
evaluator on the molecule — independent of any automorphism — close exactly those cases:

* `NoTransientOnlyLabels g`: an occurrence whose no-context (consensus) descriptor is refused has
  no descriptor under any inherited reference either;
* `RefusalConsensus r g`: an occurrence whose descriptor under the recorded reference `r` is
  refused has a refused no-context descriptor (automatic where `r` is outside the frame or is an
  eligible reference; see `refusalConsensus_of_eligible`).

With these, `Recorded r g` — symmetry under the reference `r` fixed by `σ`, at every depth and
every reached occurrence — gives for the actual immediate-frame recursion:
`recorded_facts_pullback` (facts invariant under the pulled-back geometry),
`recorded_relativeSign_eq_one` (proper sense at every labelled framed descendant, any context), and
the root consequences `generated_perm_of_recorded`, `readingOf_relabel_of_recorded`,
`assignCenter_none_of_recorded_odd`.

These are sufficient conditions, not an extraction from one finite root state. `Recorded` and
the two evaluator properties remain hypotheses quantified over all depths and reached occurrences.
No domain-wide construction or reduction to a finite check is proved here. The unproved cases
also do not establish that a key tie cannot determine the required symmetry.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingOrientationRecorded

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingRelabel LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingSenseTransport
open LocalizedChemicalRingCompletenessStrict LocalizedChemicalRingCompletenessMarked
open LocalizedChemicalRingCompletenessMirror LocalizedChemicalRingCompletenessOrbit
open LocalizedChemicalRingCompletenessRefusal
open LocalizedChemicalRingCompletenessGeneralPhysical (actual_covariant structuralSymmetry_of_aut)
open LocalizedChemicalRingCompletenessPermutationTransport (descriptorWith_map)
open LocalizedChemicalRingOrientationReadback LocalizedChemicalRingOrientationInduction
open LocalizedChemicalRingOrientationContexts LocalizedChemicalRingOrientationResidue
open LocalizedMarkedOperationEvaluator (Operations underWith mem_tiedChildren_actual)
open LocalizedMarkedReachableConfigurations
open LocalizedMarkedReachedFrameNeighbors (reached_atom_valid)
open LocalizedMarkedCertifiedTerminalRefusal (raw_single raw_atom_bound)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedGenericMarkedRecalculation (Geometry frameAtoms? consensus mirror eligibleOf strict
  consistent flatMap_congr_mem structuralDepth)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

theorem flipDescriptorBy_one (x : Option LocalizedTetrahedralRSPseudoDescriptor) :
    flipDescriptorBy 1 x = x := by
  unfold flipDescriptorBy
  rw [if_pos rfl]

theorem flipDescriptorBy_none (s : ℝ) : flipDescriptorBy s none = none := by
  unfold flipDescriptorBy
  split_ifs <;> rfl

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (e : input.detectedMultiCenterMolecule.Aut)
  (atomsPres : ∀ x, x < mol.atomCount →
    mol.atomAt? (relabelOf input (e : Equiv.Perm input.Atom) x) = mol.atomAt? x)
  (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
    ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
  (r : Nat) (fixedR : relabelOf input (e : Equiv.Perm input.Atom) r = r)

/-- Symmetry of the labels generated under the recorded reference `r`. -/
def Recorded (g : Geometry) : Prop :=
  ∀ depth node, Reached mol node →
    LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth g [] (some r)
        (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node) =
      LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth g []
        (some r) node

/-- A refused no-context descriptor is refused under every inherited reference. -/
def NoTransientOnlyLabels (g : Geometry) : Prop :=
  ∀ depth node, Reached mol node → ∀ ctx,
    LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth g [] none
      node = none →
    LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth g [] ctx
      node = none

/-- A refused descriptor under the recorded reference has a refused no-context descriptor. -/
def RefusalConsensus (g : Geometry) : Prop :=
  ∀ depth node, Reached mol node →
    LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth g []
      (some r) node = none →
    LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth g [] none
      node = none

/-- `RefusalConsensus` is automatic at occurrences where `r` is outside the frame or eligible. -/
theorem refusalConsensus_of_eligible (g : Geometry) (depth : Nat)
    (node : RawMolecule.CanonicalBranchNode) (atoms sorted : List Nat)
    (adjacent : List (Option Ordering)) (frame : frameAtoms? mol node = some atoms)
    (ordered : (sparseOperations input mol).ordinary [] node = some (sorted, adjacent))
    (nodup : atoms.Nodup) (consistentOrder : consistent adjacent = true)
    (placement : r ∉ atoms ∨ (strict adjacent = false ∧ r ∈ eligibleOf atoms sorted adjacent))
    (refused : LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth g
      [] (some r) node = none) :
    LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth g [] none
      node = none := by
  rcases placement with absent | ⟨tied, eligible⟩
  · rw [← descriptor_ctx_irrelevant mol _ depth g r node atoms frame absent]
    exact refused
  · cases label : LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth
        g [] none node with
    | none => rfl
    | some x =>
        have present : r ∈ atoms := by
          unfold eligibleOf LocalizedGenericMarkedRecalculation.atomsAt at eligible
          obtain ⟨_, _, found⟩ := List.mem_filterMap.mp eligible
          exact List.mem_of_getElem? found
        rw [descriptor_ctx_eligible mol _ depth g r node atoms sorted adjacent frame ordered nodup
          consistentOrder tied present eligible x label] at refused
        cases refused

include agreement admissible supported single atomsPres fixedR in
/-- **Inductive step from recorded data.** -/
theorem descriptor_pullback_eq_of_recorded (g : Geometry)
    (flips : FlipsBy mol (relabelOf input (e : Equiv.Perm input.Atom))
      (nodeSign input mol agreement admissible supported cfg e) g)
    (depth : Nat) (ctx : Option Nat) (node : RawMolecule.CanonicalBranchNode)
    (reached : Reached mol node)
    (recordedAt : LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth
        g [] (some r) (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node) =
      LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth g []
        (some r) node)
    (noTransient : LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol)
        depth g [] none node = none →
      LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth g [] ctx
        node = none)
    (refusalCons : LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol)
        depth g [] (some r) node = none →
      LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth g [] none
        node = none)
    (below : ∀ child ∈ mol.canonicalChildren node, ∀ ctx',
      LocalizedMarkedOperationEvaluator.facts mol (sparseOperations input mol) depth
          (pullback (relabelOf input (e : Equiv.Perm input.Atom)) g) [] ctx' child =
        LocalizedMarkedOperationEvaluator.facts mol (sparseOperations input mol) depth g [] ctx' child)
    (belowMirror : ∀ child ∈ mol.canonicalChildren node, ∀ ctx',
      LocalizedMarkedOperationEvaluator.facts mol (sparseOperations input mol) depth
          (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (mirror g)) [] ctx' child =
        LocalizedMarkedOperationEvaluator.facts mol (sparseOperations input mol) depth (mirror g) []
          ctx' child) :
    LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth
        (pullback (relabelOf input (e : Equiv.Perm input.Atom)) g) [] ctx node =
      LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth g [] ctx
        node ∧
    ∀ x, LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth g []
      ctx node = some x → nodeSign input mol agreement admissible supported cfg e node = 1 := by
  have wellFormed := admissible.1.1
  have unique := admissible.1.2
  have rawSingle := raw_single mol input agreement wellFormed unique supported single
  have sym := structuralSymmetry_of_aut input mol agreement admissible supported e atomsPres
  have cov := actual_covariant input mol agreement admissible supported single e atomsPres
  have unit := nodeSign_unit input mol agreement admissible supported cfg e node
  cases frame : frameAtoms? mol node with
  | none =>
      refine ⟨?_, ?_⟩
      · rw [descriptor_none_of_no_frame mol _ depth _ ctx node frame,
          descriptor_none_of_no_frame mol _ depth g ctx node frame]
      · intro x label
        rw [descriptor_none_of_no_frame mol _ depth g ctx node frame] at label
        cases label
  | some atoms =>
      have flipped : ∀ ctx', LocalizedMarkedOperationEvaluator.descriptor? mol
          (sparseOperations input mol) depth (pullback (relabelOf input (e : Equiv.Perm input.Atom)) g)
          [] ctx' node =
          flipDescriptorBy (nodeSign input mol agreement admissible supported cfg e node)
            (LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth g []
              ctx' node) := by
        intro ctx'
        rw [descriptor_eq_descriptorWith, descriptor_eq_descriptorWith]
        refine descriptorWith_flip mol _ _ (rawStep_flip mol _) _ _ g depth node atoms frame
          (flips node reached atoms frame) [] ctx' ?_ ?_
        · intro mark
          unfold underWith
          rw [← facts_eq_factsWith]
          exact flatMap_congr_mem _ _ _ fun child member =>
            below child (mem_tiedChildren_actual mol _ [] node child member) (some mark)
        · intro mark
          rw [mirror_pullback]
          unfold underWith
          rw [← facts_eq_factsWith]
          exact flatMap_congr_mem _ _ _ fun child member =>
            belowMirror child (mem_tiedChildren_actual mol _ [] node child member) (some mark)
      have transported : LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol)
          depth g [] (some r) (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node) =
          LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth
            (pullback (relabelOf input (e : Equiv.Perm input.Atom)) g) [] (some r) node := by
        rw [descriptor_eq_descriptorWith, descriptor_eq_descriptorWith]
        have h := descriptorWith_map sym wellFormed unique rawSingle cov
          LocalizedMarkedOperationEvaluator.rawStep? (rawStep_map sym wellFormed unique rawSingle cov)
          depth g (some r) node reached
        rw [Option.map_some, fixedR] at h
        exact h
      have recordedEq : LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol)
          depth (pullback (relabelOf input (e : Equiv.Perm input.Atom)) g) [] (some r) node =
          LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth g []
            (some r) node := transported.symm.trans recordedAt
      -- the descriptor that decides the sign: the recorded one if `r` is in the frame, else the
      -- no-context one (both coincide with the recorded one outside the frame)
      have decide : ∀ (c₀ : Option Nat),
          LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth
            (pullback (relabelOf input (e : Equiv.Perm input.Atom)) g) [] c₀ node =
            LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth g []
              c₀ node →
          (LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth g []
            c₀ node = none →
            LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth g []
              ctx node = none) →
          LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth
            (pullback (relabelOf input (e : Equiv.Perm input.Atom)) g) [] ctx node =
            LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth g []
              ctx node ∧
          ∀ x, LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth g
            [] ctx node = some x →
            nodeSign input mol agreement admissible supported cfg e node = 1 := by
        intro c₀ invariant propagate
        cases decided : LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol)
            depth g [] c₀ node with
        | some y =>
            have h := flipped c₀
            rw [invariant, decided] at h
            have one := flipDescriptorBy_some_eq _ unit y h.symm
            refine ⟨?_, fun _ _ => one⟩
            rw [flipped ctx, one, flipDescriptorBy_one]
        | none =>
            have allNone := propagate decided
            refine ⟨?_, fun x hx => by rw [allNone] at hx; cases hx⟩
            rw [flipped ctx, allNone, flipDescriptorBy_none]
      by_cases present : r ∈ atoms
      · exact decide (some r) recordedEq (fun refused => noTransient (refusalCons refused))
      · have irr := descriptor_ctx_irrelevant mol (sparseOperations input mol) depth g r node atoms
          frame present
        have irr' := descriptor_ctx_irrelevant mol (sparseOperations input mol) depth
          (pullback (relabelOf input (e : Equiv.Perm input.Atom)) g) r node atoms frame present
        refine decide none ?_ noTransient
        rw [← irr', ← irr]
        exact recordedEq

include agreement admissible supported single calibrated atomsPres fixedR in
/-- **Facts are invariant under the pulled-back geometry from recorded symmetry and the two
evaluator properties**, for the input geometry and its mirror. -/
theorem recorded_facts_pullback
    (recorded : ∀ g, (g = inputGeometry input ∨ g = mirror (inputGeometry input)) →
      Recorded input mol e r g)
    (noTransient : ∀ g, (g = inputGeometry input ∨ g = mirror (inputGeometry input)) →
      NoTransientOnlyLabels input mol g)
    (refusalCons : ∀ g, (g = inputGeometry input ∨ g = mirror (inputGeometry input)) →
      RefusalConsensus input mol r g) :
    ∀ depth g, (g = inputGeometry input ∨ g = mirror (inputGeometry input)) →
      ∀ ctx node, Reached mol node →
        LocalizedMarkedOperationEvaluator.facts mol (sparseOperations input mol) depth
            (pullback (relabelOf input (e : Equiv.Perm input.Atom)) g) [] ctx node =
          LocalizedMarkedOperationEvaluator.facts mol (sparseOperations input mol) depth g [] ctx
            node := by
  have flips := flipsBy_input input mol agreement admissible supported single cfg e calibrated
  intro depth
  induction depth with
  | zero => intros; rfl
  | succ depth ih =>
      intro g hg ctx node reached
      have flipsG : FlipsBy mol (relabelOf input (e : Equiv.Perm input.Atom))
          (nodeSign input mol agreement admissible supported cfg e) g := by
        rcases hg with rfl | rfl
        · exact flips
        · exact flips.mirror
      have hgm : mirror g = inputGeometry input ∨ mirror g = mirror (inputGeometry input) := by
        rcases hg with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl (mirror_mirror _)
      have head := (descriptor_pullback_eq_of_recorded input mol agreement admissible supported single
        cfg e atomsPres r fixedR g flipsG depth ctx node reached
        (recorded g hg depth node reached) (noTransient g hg depth node reached ctx)
        (refusalCons g hg depth node reached)
        (fun child member ctx' => ih g hg ctx' child (reached_child mol node child reached member))
        (fun child member ctx' =>
          ih (mirror g) hgm ctx' child (reached_child mol node child reached member))).1
      rw [LocalizedMarkedOperationEvaluator.facts_succ, LocalizedMarkedOperationEvaluator.facts_succ,
        head]
      congr 1
      exact flatMap_congr_mem _ _ _ fun child member =>
        ih g hg ctx child (reached_child mol node child reached member)

include agreement admissible supported single calibrated atomsPres fixedR in
/-- **Proper sense at every labelled framed descendant, from recorded symmetry.** -/
theorem recorded_relativeSign_eq_one
    (recorded : ∀ g, (g = inputGeometry input ∨ g = mirror (inputGeometry input)) →
      Recorded input mol e r g)
    (noTransient : ∀ g, (g = inputGeometry input ∨ g = mirror (inputGeometry input)) →
      NoTransientOnlyLabels input mol g)
    (refusalCons : ∀ g, (g = inputGeometry input ∨ g = mirror (inputGeometry input)) →
      RefusalConsensus input mol r g)
    (depth : Nat) (ctx : Option Nat) (node : RawMolecule.CanonicalBranchNode)
    (reached : Reached mol node) (d : input.detectedMultiCenterMolecule.Center)
    (atomEq : node.atom = d.1.val) (atoms : List Nat) (frame : frameAtoms? mol node = some atoms)
    (x : LocalizedTetrahedralRSPseudoDescriptor)
    (label : LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth
      (inputGeometry input) [] ctx node = some x) :
    relativeSign input.detectedMultiCenterMolecule cfg e d = 1 := by
  rw [← nodeSign_eq input mol agreement admissible supported single cfg e d node atomEq reached
    atoms frame]
  exact (descriptor_pullback_eq_of_recorded input mol agreement admissible supported single cfg e
    atomsPres r fixedR (inputGeometry input)
    (flipsBy_input input mol agreement admissible supported single cfg e calibrated) depth ctx node
    reached (recorded _ (Or.inl rfl) depth node reached)
    (noTransient _ (Or.inl rfl) depth node reached ctx) (refusalCons _ (Or.inl rfl) depth node reached)
    (fun child member ctx' => recorded_facts_pullback input mol agreement admissible supported single
      cfg e atomsPres calibrated r fixedR recorded noTransient refusalCons depth _ (Or.inl rfl) ctx'
      child (reached_child mol node child reached member))
    (fun child member ctx' => recorded_facts_pullback input mol agreement admissible supported single
      cfg e atomsPres calibrated r fixedR recorded noTransient refusalCons depth _ (Or.inr rfl) ctx'
      child (reached_child mol node child reached member))).2 x label

/-! ## Root consequences -/

variable (c : input.detectedMultiCenterMolecule.Center)
  (fixed : input.detectedMultiCenterMolecule.centerPerm e c = c)

include agreement admissible supported single calibrated atomsPres fixedR fixed in
theorem generated_perm_of_recorded
    (recorded : ∀ g, (g = inputGeometry input ∨ g = mirror (inputGeometry input)) →
      Recorded input mol e r g)
    (noTransient : ∀ g, (g = inputGeometry input ∨ g = mirror (inputGeometry input)) →
      NoTransientOnlyLabels input mol g)
    (refusalCons : ∀ g, (g = inputGeometry input ∨ g = mirror (inputGeometry input)) →
      RefusalConsensus input mol r g) (m : Nat) :
    (generated input mol c (inputGeometry input) (relabelOf input (e : Equiv.Perm input.Atom) m)).Perm
      ((generated input mol c (inputGeometry input) m).map
        (mapFact (relabelOf input (e : Equiv.Perm input.Atom)))) := by
  have wellFormed := admissible.1.1
  have unique := admissible.1.2
  have rawSingle := raw_single mol input agreement wellFormed unique supported single
  have sym := structuralSymmetry_of_aut input mol agreement admissible supported e atomsPres
  have cov := actual_covariant input mol agreement admissible supported single e atomsPres
  have reached := reached_root mol c.1.val (raw_atom_bound mol input agreement c.1)
  have transport := underWith_map LocalizedMarkedOperationEvaluator.rawStep? sym wellFormed unique
    rawSingle cov (rawStep_map sym wellFormed unique rawSingle cov)
    (structuralDepth mol (canonicalCenterRoot c.1.val)) (inputGeometry input)
    (canonicalCenterRoot c.1.val) reached m
  rw [root_fixed input e c fixed, ← facts_eq_factsWith] at transport
  refine transport.trans (List.Perm.of_eq ?_)
  congr 1
  unfold generated underWith
  apply flatMap_congr_mem
  intro child member
  exact recorded_facts_pullback input mol agreement admissible supported single cfg e atomsPres
    calibrated r fixedR recorded noTransient refusalCons _ (inputGeometry input) (Or.inl rfl) (some m)
    child (reached_child mol _ child reached (mem_tiedChildren_actual mol _ [] _ child member))

include agreement admissible supported single calibrated atomsPres fixedR fixed in
theorem readingOf_relabel_of_recorded
    (recorded : ∀ g, (g = inputGeometry input ∨ g = mirror (inputGeometry input)) →
      Recorded input mol e r g)
    (noTransient : ∀ g, (g = inputGeometry input ∨ g = mirror (inputGeometry input)) →
      NoTransientOnlyLabels input mol g)
    (refusalCons : ∀ g, (g = inputGeometry input ∨ g = mirror (inputGeometry input)) →
      RefusalConsensus input mol r g)
    (data : RootData input mol c) (k : Fin 4) :
    readingOf input mol single c data (inputGeometry input)
        (generated input mol c (inputGeometry input))
        (input.detectedMultiCenterMolecule.ligandPermAt e c k) =
      if permHandedness (input.detectedMultiCenterMolecule.ligandPermAt e c) = 1 then
        readingOf input mol single c data (inputGeometry input)
          (generated input mol c (inputGeometry input)) k
      else (readingOf input mol single c data (inputGeometry input)
          (generated input mol c (inputGeometry input)) k).map RS.swap := by
  rw [readingOf_eq_evaluate, readingOf_eq_evaluate, ← relabel_ligand_perm input e c fixed,
    ← relativeSign_fixed input cfg e c fixed]
  exact evaluate_relabel_of_perm input mol agreement admissible supported single cfg e atomsPres c
    fixed calibrated data _ _ k
    (generated_perm_of_recorded input mol agreement admissible supported single cfg e atomsPres
      calibrated r fixedR c fixed recorded noTransient refusalCons _)

include agreement admissible supported single calibrated atomsPres fixedR fixed in
/-- **Refusal from recorded symmetry, the two evaluator properties and odd parity.** -/
theorem assignCenter_none_of_recorded_odd
    (recorded : ∀ g, (g = inputGeometry input ∨ g = mirror (inputGeometry input)) →
      Recorded input mol e r g)
    (noTransient : ∀ g, (g = inputGeometry input ∨ g = mirror (inputGeometry input)) →
      NoTransientOnlyLabels input mol g)
    (refusalCons : ∀ g, (g = inputGeometry input ∨ g = mirror (inputGeometry input)) →
      RefusalConsensus input mol r g)
    (odd : permHandedness (input.detectedMultiCenterMolecule.ligandPermAt e c) = -1) :
    LocalizedMarkedOperationEvaluator.assignCenter? mol (sparseOperations input mol)
      (inputGeometry input) c.1.val = none := by
  obtain ⟨data⟩ := rootData_exists input mol agreement admissible supported single c
  have notInj := not_injective_of_odd input mol agreement admissible supported single e atomsPres c
    fixed data odd
  rw [assignCenter_none_iff input mol single cfg c (calibrated c) data notInj]
  apply Or.inl
  apply consensus_none_of_swapped _ (tiedLigands_ne_nil input mol single c data notInj)
    (input.detectedMultiCenterMolecule.ligandPermAt e c)
  · exact perm_mem_tiedLigands input mol agreement admissible supported single e atomsPres c fixed data
  · intro k _
    rw [readingOf_relabel_of_recorded input mol agreement admissible supported single cfg e atomsPres
      calibrated r fixedR c fixed recorded noTransient refusalCons data k, if_neg (by rw [odd]; norm_num)]

end TetraStereo.OneCenter.LocalizedChemicalRingOrientationRecorded

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationRecorded.refusalConsensus_of_eligible
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationRecorded.descriptor_pullback_eq_of_recorded
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationRecorded.recorded_facts_pullback
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationRecorded.recorded_relativeSign_eq_one
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationRecorded.generated_perm_of_recorded
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationRecorded.readingOf_relabel_of_recorded
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationRecorded.assignCenter_none_of_recorded_odd
