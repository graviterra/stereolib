import TetraStereo.OneCenter.LocalizedChemicalRingCompletenessOrbit
import TetraStereo.OneCenter.LocalizedChemicalRingCompletenessPermutationTransport
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Decoding a generated stereo label into a physical frame sign

The central remaining obligation of ring completeness is to read the physical orientation of one
molecular automorphism `σ` off the ACTUALLY generated auxiliary labels. This module proves the
per-occurrence decoder.

* `flipBy s` complements a reading when the sign `s` is `-1`; `flipDescriptorBy s` does the same
  for a generated descriptor (uppercase and lowercase alike).
* `StepFlip`: a raw step whose geometry dependence is only through frame readbacks transports a
  uniform readback flip. Both actual steps satisfy it (`rawStep_flip`, `distantStep_flip`), with the
  consensus and inherited-reference policies commuting with the flip.
* `descriptorWith_flip`: when the facts of the tied children agree under two geometries, the
  generated descriptor under the first is the flipped descriptor under the second.
* `readback_pullback_frame`: at any reached occurrence of a calibrated centre `d`, every reading
  of a list drawn from the frame under the pulled-back geometry `pullback σ G` is the reading under
  `G` flipped by `relativeSign σ d`. The list is identified as a ligand enumeration
  (`exists_enumeration`); no rigidity or root position is assumed.
* `descriptorWith_pullback`, `relativeSign_eq_one_of_descriptor`,
  `relativeSign_eq_one_of_label_match`: the generated descriptor at an occurrence under the
  pulled-back geometry is the flipped descriptor under the original geometry; hence equal `some`
  labels at an occurrence and at its `σ`-image (through the accepted covariance) force
  `relativeSign σ d = 1`, provided the facts below agree under both geometries.

The last proviso is exactly the inductive hypothesis of the simultaneous recursion over the
generated forest; it is stated, not assumed away. The molecular automorphism `e` and the matched
labels are explicit premises; no proper-sign premise, sorting correctness or desired descriptor is
assumed.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingOrientationReadback

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingRelabel LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingSenseTransport
open LocalizedChemicalRingCompletenessStrict (list_four_eq swap_ne)
open LocalizedChemicalRingCompletenessMarked (enumeration swap_swap)
open LocalizedChemicalRingCompletenessGeneralPhysical (actual_covariant structuralSymmetry_of_aut)
open LocalizedChemicalRingCompletenessPermutationTransport (descriptorWith_map)
open LocalizedMarkedOperationEvaluator (Operations markedReading? underWith)
open LocalizedMarkedReachableConfigurations
open LocalizedMarkedReachedFrameNeighbors (frame_atoms_perm_neighbors)
open LocalizedMarkedCertifiedTerminalRefusal (raw_single)
open LocalizedMarkedCyclicDiscardedReference (rankedAtoms_subset)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedPhysicalMarkedDistantReference (chooseInherited chooseInherited_local
  chooseInherited_distant_success chooseInherited_distant_refusal)
open LocalizedGenericMarkedRecalculation (Geometry frameAtoms? readback? atomsAt? rankedAtoms?
  consensus appendFacts? mirror caseFromMirror? readback_mirror)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign relativeSign_eq_one_or_neg_one)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

/-! ## Flips -/

/-- Complement a reading when the sign is not `1`. -/
noncomputable def flipBy (s : ℝ) (x : Option RS) : Option RS :=
  if s = 1 then x else x.map RS.swap

theorem flipBy_none (s : ℝ) : flipBy s none = none := by
  unfold flipBy
  split_ifs <;> rfl

theorem flipBy_some (s : ℝ) (v : RS) :
    flipBy s (some v) = some (if s = 1 then v else v.swap) := by
  unfold flipBy
  split_ifs <;> rfl

theorem flipBy_map_swap (s : ℝ) (x : Option RS) :
    flipBy s (x.map RS.swap) = (flipBy s x).map RS.swap := by
  unfold flipBy
  split_ifs <;> rfl

theorem flipBy_bind {α : Type} (s : ℝ) (x : Option α) (f g : α → Option RS)
    (h : ∀ a, f a = flipBy s (g a)) : x.bind f = flipBy s (x.bind g) := by
  cases x with
  | none => rw [Option.bind_none, Option.bind_none, flipBy_none]
  | some a => rw [Option.bind_some, Option.bind_some]; exact h a

theorem flipBy_eq_id (s : ℝ) (h : s = 1) : flipBy s = id := by
  funext x
  unfold flipBy
  rw [if_pos h]
  rfl

theorem flipBy_eq_swap (s : ℝ) (h : ¬ s = 1) : flipBy s = Option.map RS.swap := by
  funext x
  unfold flipBy
  rw [if_neg h]

theorem consensus_map_swap (l : List (Option RS)) :
    consensus (l.map (Option.map RS.swap)) = (consensus l).map RS.swap := by
  cases h : consensus l with
  | none =>
      cases h' : consensus (l.map (Option.map RS.swap)) with
      | none => rfl
      | some w =>
          exfalso
          obtain ⟨ne, all⟩ := (consensus_eq_some_iff _ _).mp h'
          have back : consensus l = some w.swap := by
            rw [consensus_eq_some_iff]
            refine ⟨fun e => ne (by rw [e]; rfl), ?_⟩
            intro x hx
            have hx' := all (x.map RS.swap) (List.mem_map.mpr ⟨x, hx, rfl⟩)
            cases x with
            | none => simp at hx'
            | some v =>
                rw [Option.map_some, Option.some.injEq] at hx'
                rw [← hx', swap_swap]
          rw [h] at back
          cases back
  | some v =>
      obtain ⟨ne, all⟩ := (consensus_eq_some_iff _ _).mp h
      rw [Option.map_some, consensus_eq_some_iff]
      refine ⟨fun e => ne (List.map_eq_nil_iff.mp e), ?_⟩
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      rw [all y hy]
      rfl

theorem consensus_flipBy (s : ℝ) (l : List (Option RS)) :
    consensus (l.map (flipBy s)) = flipBy s (consensus l) := by
  by_cases h : s = 1
  · rw [flipBy_eq_id s h, List.map_id]
    rfl
  · rw [flipBy_eq_swap s h]
    exact consensus_map_swap l

/-- Complement of a lowercase descriptor. -/
def swapPseudo : PseudoRS → PseudoRS
  | .r => .s
  | .s => .r

/-- Complement of a generated descriptor, uppercase or lowercase. -/
def flipDescriptor : LocalizedTetrahedralRSPseudoDescriptor → LocalizedTetrahedralRSPseudoDescriptor
  | .chiral v => .chiral v.swap
  | .pseudoasymmetric p => .pseudoasymmetric (swapPseudo p)

noncomputable def flipDescriptorBy (s : ℝ) (x : Option LocalizedTetrahedralRSPseudoDescriptor) :
    Option LocalizedTetrahedralRSPseudoDescriptor :=
  if s = 1 then x else x.map flipDescriptor

theorem flipDescriptor_ne (x : LocalizedTetrahedralRSPseudoDescriptor) : flipDescriptor x ≠ x := by
  cases x with
  | chiral v => cases v <;> decide
  | pseudoasymmetric p => cases p <;> decide

theorem caseFromMirror_flipBy (s : ℝ) (a b : Option RS) :
    caseFromMirror? (flipBy s a) (flipBy s b) = flipDescriptorBy s (caseFromMirror? a b) := by
  unfold flipBy flipDescriptorBy
  split_ifs
  · rfl
  · cases a with
    | none => rfl
    | some x =>
        cases b with
        | none => rfl
        | some y => cases x <;> cases y <;> rfl

theorem flipDescriptorBy_some_eq (s : ℝ) (unit : s = 1 ∨ s = -1)
    (x : LocalizedTetrahedralRSPseudoDescriptor) (h : flipDescriptorBy s (some x) = some x) :
    s = 1 := by
  rcases unit with rfl | rfl
  · rfl
  · exfalso
    unfold flipDescriptorBy at h
    rw [if_neg (by norm_num), Option.map_some, Option.some.injEq] at h
    exact flipDescriptor_ne x h

/-! ## Steps transport a uniform readback flip -/

section Steps

variable (mol : RawMolecule) (ops : Operations)

/-- A step whose geometry dependence is through frame readbacks transports a uniform flip. -/
def StepFlip (step : Step) : Prop :=
  ∀ (s : ℝ) (first second : Geometry) (node : RawMolecule.CanonicalBranchNode) (atoms : List Nat),
    frameAtoms? mol node = some atoms →
    (∀ L : List Nat, (∀ x ∈ L, x ∈ atoms) → readback? first L = flipBy s (readback? second L)) →
    ∀ state ctx under,
      step mol ops first state ctx node under = flipBy s (step mol ops second state ctx node under)

theorem markedReading_flip (s : ℝ) (first second : Geometry)
    (node : RawMolecule.CanonicalBranchNode) (atoms : List Nat)
    (frame : frameAtoms? mol node = some atoms)
    (flip : ∀ L : List Nat, (∀ x ∈ L, x ∈ atoms) → readback? first L = flipBy s (readback? second L))
    (state : OccurrenceAuxState) (r : Nat) :
    markedReading? mol ops first state node r = flipBy s (markedReading? mol ops second state node r) := by
  unfold markedReading?
  rw [frame]
  simp only [Option.bind_eq_bind, Option.bind_some]
  cases ops.marked state node r with
  | none => simp only [Option.bind_none, flipBy_none]
  | some ranking =>
      simp only [Option.bind_some]
      cases h : rankedAtoms? atoms ranking with
      | none => simp only [Option.bind_none, flipBy_none]
      | some ranked =>
          simp only [Option.bind_some]
          exact flip ranked (rankedAtoms_subset atoms ranking ranked h)

theorem evaluate_flip (s : ℝ) (first second : Geometry)
    (node : RawMolecule.CanonicalBranchNode) (atoms : List Nat)
    (frame : frameAtoms? mol node = some atoms)
    (flip : ∀ L : List Nat, (∀ x ∈ L, x ∈ atoms) → readback? first L = flipBy s (readback? second L))
    (state : OccurrenceAuxState) (under : Nat → OccurrenceAuxState) (r : Nat) :
    ((appendFacts? state (under r)).bind fun temp => markedReading? mol ops first temp node r) =
      flipBy s ((appendFacts? state (under r)).bind fun temp =>
        markedReading? mol ops second temp node r) :=
  flipBy_bind s _ _ _ fun temp => markedReading_flip mol ops s first second node atoms frame flip temp r

theorem consensus_evaluate_flip (s : ℝ) (first second : Geometry)
    (node : RawMolecule.CanonicalBranchNode) (atoms : List Nat)
    (frame : frameAtoms? mol node = some atoms)
    (flip : ∀ L : List Nat, (∀ x ∈ L, x ∈ atoms) → readback? first L = flipBy s (readback? second L))
    (state : OccurrenceAuxState) (under : Nat → OccurrenceAuxState) (eligible : List Nat) :
    consensus (eligible.map fun r =>
        (appendFacts? state (under r)).bind fun temp => markedReading? mol ops first temp node r) =
      flipBy s (consensus (eligible.map fun r =>
        (appendFacts? state (under r)).bind fun temp => markedReading? mol ops second temp node r)) := by
  rw [← consensus_flipBy, List.map_map]
  congr 1
  apply List.map_congr_left
  intro r _
  simp only [Function.comp_apply]
  exact evaluate_flip mol ops s first second node atoms frame flip state under r

/-- The immediate-frame step transports a uniform readback flip. -/
theorem rawStep_flip : StepFlip mol ops LocalizedMarkedOperationEvaluator.rawStep? := by
  intro s first second node atoms frame flip state ctx under
  unfold LocalizedMarkedOperationEvaluator.rawStep?
  rw [frame]
  cases ops.ordinary state node with
  | none => simp only [Option.bind_eq_bind, Option.bind_some, Option.bind_none, flipBy_none]
  | some result =>
      obtain ⟨sorted, adjacent⟩ := result
      simp only [Option.bind_eq_bind, Option.bind_some]
      split_ifs
      · rw [flipBy_none]
      · cases h : atomsAt? atoms sorted with
        | none => simp only [Option.bind_none, flipBy_none]
        | some ranked =>
            simp only [Option.bind_some]
            exact flip ranked (atomsAt_subset atoms sorted ranked h)
      · cases ctx with
        | none =>
            exact consensus_evaluate_flip mol ops s first second node atoms frame flip state under _
        | some r =>
            dsimp only
            split_ifs
            · exact evaluate_flip mol ops s first second node atoms frame flip state under r
            · exact consensus_evaluate_flip mol ops s first second node atoms frame flip state under _

/-- The distant-reference step transports a uniform readback flip. -/
theorem distantStep_flip : StepFlip mol ops LocalizedPhysicalMarkedDistantReference.rawStep? := by
  intro s first second node atoms frame flip state ctx under
  have reading : ∀ r, LocalizedPhysicalMarkedDistantReference.inheritedRead? mol ops first state
      node under r = flipBy s (LocalizedPhysicalMarkedDistantReference.inheritedRead? mol ops second
        state node under r) := by
    intro r
    unfold LocalizedPhysicalMarkedDistantReference.inheritedRead?
    exact evaluate_flip mol ops s first second node atoms frame flip state under r
  unfold LocalizedPhysicalMarkedDistantReference.rawStep?
  rw [frame]
  cases ops.ordinary state node with
  | none => simp only [Option.bind_eq_bind, Option.bind_some, Option.bind_none, flipBy_none]
  | some result =>
      obtain ⟨sorted, adjacent⟩ := result
      simp only [Option.bind_eq_bind, Option.bind_some]
      split_ifs
      · rw [flipBy_none]
      · cases h : atomsAt? atoms sorted with
        | none => simp only [Option.bind_none, flipBy_none]
        | some ranked =>
            simp only [Option.bind_some]
            exact flip ranked (atomsAt_subset atoms sorted ranked h)
      · have fallback : consensus ((LocalizedGenericMarkedRecalculation.eligibleOf atoms sorted
            adjacent).map (LocalizedPhysicalMarkedDistantReference.inheritedRead? mol ops first state
              node under)) =
            flipBy s (consensus ((LocalizedGenericMarkedRecalculation.eligibleOf atoms sorted
              adjacent).map (LocalizedPhysicalMarkedDistantReference.inheritedRead? mol ops second
                state node under))) := by
          rw [← consensus_flipBy, List.map_map]
          congr 1
          apply List.map_congr_left
          intro r _
          exact reading r
        cases ctx with
        | none => exact fallback
        | some m =>
            by_cases present : m ∈ atoms
            · rw [chooseInherited_local _ _ _ _ present, chooseInherited_local _ _ _ _ present]
              exact reading m
            · cases read : LocalizedPhysicalMarkedDistantReference.inheritedRead? mol ops second
                  state node under m with
              | none =>
                  have read' := reading m
                  rw [read, flipBy_none] at read'
                  rw [chooseInherited_distant_refusal _ _ _ _ present read',
                    chooseInherited_distant_refusal _ _ _ _ present read]
                  exact fallback
              | some v =>
                  have read' := reading m
                  rw [read, flipBy_some] at read'
                  rw [chooseInherited_distant_success _ _ _ _ _ read',
                    chooseInherited_distant_success _ _ _ _ _ read, flipBy_some]

/-- **Generated descriptors transport a uniform readback flip** when the facts of the tied
children agree under the two geometries (and under their mirrors). -/
theorem descriptorWith_flip (step : Step) (stepFlip : StepFlip mol ops step) (s : ℝ)
    (first second : Geometry) (depth : Nat) (node : RawMolecule.CanonicalBranchNode)
    (atoms : List Nat) (frame : frameAtoms? mol node = some atoms)
    (flip : ∀ L : List Nat, (∀ x ∈ L, x ∈ atoms) → readback? first L = flipBy s (readback? second L))
    (state : OccurrenceAuxState) (ctx : Option Nat)
    (below : ∀ mark, underWith mol ops first state node (factsWith step mol ops depth) mark =
      underWith mol ops second state node (factsWith step mol ops depth) mark)
    (belowMirror : ∀ mark,
      underWith mol ops (mirror first) state node (factsWith step mol ops depth) mark =
        underWith mol ops (mirror second) state node (factsWith step mol ops depth) mark) :
    descriptorWith step mol ops depth first state ctx node =
      flipDescriptorBy s (descriptorWith step mol ops depth second state ctx node) := by
  have flipMirror : ∀ L : List Nat, (∀ x ∈ L, x ∈ atoms) →
      readback? (mirror first) L = flipBy s (readback? (mirror second) L) := by
    intro L sub
    rw [readback_mirror, readback_mirror, flip L sub, flipBy_map_swap]
  unfold descriptorWith
  rw [funext below, funext belowMirror, stepFlip s first second node atoms frame flip state ctx,
    stepFlip s (mirror first) (mirror second) node atoms frame flipMirror state ctx,
    caseFromMirror_flipBy]

end Steps

/-! ## Physical instance: the pulled-back geometry at a calibrated centre -/

section Physical

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (e : input.detectedMultiCenterMolecule.Aut)
  (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
    ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
  (d : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
  (atomEq : node.atom = d.1.val) (reached : Reached mol node) (atoms : List Nat)
  (frame : frameAtoms? mol node = some atoms)

include agreement admissible supported single atomEq reached frame in
/-- A duplicate-free four-list drawn from the frame of an occurrence of `d` is a ligand
enumeration of `d`. -/
theorem exists_enumeration (L : List Nat) (sub : ∀ x ∈ L, x ∈ atoms)
    (good : L.length = 4 ∧ L.Nodup) :
    ∃ π : Equiv.Perm (Fin 4), L = enumeration input d π := by
  have wellFormed := admissible.1.1
  have unique := admissible.1.2
  have rawSingle := raw_single mol input agreement wellFormed unique supported single
  have ligandMem : ∀ x ∈ L, ∃ i, (input.detectedMultiCenterMolecule.ligandAtomAt d i).val = x := by
    intro x hx
    have neighbor : x ∈ mol.canonicalIncidentNeighbors d.1.val := by
      rw [← atomEq]
      rcases frame_atoms_perm_neighbors mol wellFormed rawSingle node reached atoms frame with
        ⟨_, perm⟩ | ⟨three, _⟩
      · exact perm.mem_iff.mp (sub x hx)
      · exfalso
        have subset : baseFrame input d ⊆ mol.canonicalIncidentNeighbors d.1.val := by
          intro y hy
          apply (mem_neighbors_iff mol input agreement wellFormed unique supported d y).mpr
          simp only [baseFrame, Equiv.Perm.one_apply, List.mem_cons, List.mem_nil_iff, or_false]
            at hy
          rcases hy with rfl | rfl | rfl | rfl
          · exact ⟨0, rfl⟩
          · exact ⟨1, rfl⟩
          · exact ⟨2, rfl⟩
          · exact ⟨3, rfl⟩
        have le := ((baseFrame_nodup input d).subperm subset).length_le
        rw [baseFrame_length] at le
        rw [atomEq] at three
        omega
    exact (mem_neighbors_iff mol input agreement wellFormed unique supported d x).mp neighbor
  obtain ⟨l0, l1, l2, l3, hL⟩ : ∃ l0 l1 l2 l3, L = [l0, l1, l2, l3] :=
    ⟨_, _, _, _, list_four_eq L good.1⟩
  subst hL
  obtain ⟨i0, h0⟩ := ligandMem l0 (by simp)
  obtain ⟨i1, h1⟩ := ligandMem l1 (by simp)
  obtain ⟨i2, h2⟩ := ligandMem l2 (by simp)
  obtain ⟨i3, h3⟩ := ligandMem l3 (by simp)
  let f : Fin 4 → Fin 4 := fun p => if p = 0 then i0 else if p = 1 then i1 else if p = 2 then i2 else i3
  have val : ∀ p : Fin 4, (input.detectedMultiCenterMolecule.ligandAtomAt d (f p)).val =
      [l0, l1, l2, l3][p.val]'(by omega) := by
    intro p
    fin_cases p <;> simp [f, h0, h1, h2, h3]
  have inj : Function.Injective f := by
    intro p q hpq
    have eq : [l0, l1, l2, l3][p.val]'(by omega) = [l0, l1, l2, l3][q.val]'(by omega) := by
      rw [← val p, ← val q, hpq]
    exact Fin.ext (good.2.getElem_inj_iff.mp eq)
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp inj), ?_⟩
  unfold enumeration
  simp [f, Equiv.ofBijective_apply, h0, h1, h2, h3]

include agreement admissible supported single calibrated atomEq reached frame in
/-- **Readback under the pulled-back geometry is the readback flipped by the relative sign**,
for every list drawn from the frame of an occurrence of `d`. -/
theorem readback_pullback_frame (L : List Nat) (sub : ∀ x ∈ L, x ∈ atoms) :
    readback? (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (inputGeometry input)) L =
      flipBy (relativeSign input.detectedMultiCenterMolecule cfg e d)
        (readback? (inputGeometry input) L) := by
  rw [← readback_map]
  by_cases good : L.length = 4 ∧ L.Nodup
  · obtain ⟨π, rfl⟩ := exists_enumeration input mol agreement admissible supported single d node
      atomEq reached atoms frame L sub good
    have hr := readback_relabel input cfg e d (calibrated d) (calibrated _) π
    unfold flipBy
    by_cases h : relativeSign input.detectedMultiCenterMolecule cfg e d = 1
    · rw [if_pos h] at hr
      rw [if_pos h]
      exact hr
    · rw [if_neg h] at hr
      rw [if_neg h]
      exact hr
  · rw [readback_none_of_not_good _ _ (not_good_map _ L good), readback_none_of_not_good _ L good,
      flipBy_none]

include agreement admissible supported single calibrated atomEq reached frame in
/-- **The generated descriptor under the pulled-back geometry is the flipped descriptor**, for
either step, when the facts of the tied children agree under both geometry pairs. -/
theorem descriptorWith_pullback (ops : Operations) (step : Step) (stepFlip : StepFlip mol ops step)
    (depth : Nat) (state : OccurrenceAuxState) (ctx : Option Nat)
    (below : ∀ mark, underWith mol ops
        (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (inputGeometry input)) state node
        (factsWith step mol ops depth) mark =
      underWith mol ops (inputGeometry input) state node (factsWith step mol ops depth) mark)
    (belowMirror : ∀ mark, underWith mol ops
        (mirror (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (inputGeometry input)))
        state node (factsWith step mol ops depth) mark =
      underWith mol ops (mirror (inputGeometry input)) state node
        (factsWith step mol ops depth) mark) :
    descriptorWith step mol ops depth
        (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (inputGeometry input)) state ctx
        node =
      flipDescriptorBy (relativeSign input.detectedMultiCenterMolecule cfg e d)
        (descriptorWith step mol ops depth (inputGeometry input) state ctx node) :=
  descriptorWith_flip mol ops step stepFlip _ _ _ depth node atoms frame
    (fun L sub => readback_pullback_frame input mol agreement admissible supported single cfg e
      calibrated d node atomEq reached atoms frame L sub)
    state ctx below belowMirror

include agreement admissible supported single calibrated atomEq reached frame in
/-- **Decoder.** Equal `some` descriptors under the original and the pulled-back geometry force
the relative sign of the automorphism at the centre to be `1`. -/
theorem relativeSign_eq_one_of_descriptor (ops : Operations) (step : Step)
    (stepFlip : StepFlip mol ops step) (depth : Nat) (state : OccurrenceAuxState) (ctx : Option Nat)
    (below : ∀ mark, underWith mol ops
        (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (inputGeometry input)) state node
        (factsWith step mol ops depth) mark =
      underWith mol ops (inputGeometry input) state node (factsWith step mol ops depth) mark)
    (belowMirror : ∀ mark, underWith mol ops
        (mirror (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (inputGeometry input)))
        state node (factsWith step mol ops depth) mark =
      underWith mol ops (mirror (inputGeometry input)) state node
        (factsWith step mol ops depth) mark)
    (x : LocalizedTetrahedralRSPseudoDescriptor)
    (original : descriptorWith step mol ops depth (inputGeometry input) state ctx node = some x)
    (pulled : descriptorWith step mol ops depth
      (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (inputGeometry input)) state ctx
        node = some x) :
    relativeSign input.detectedMultiCenterMolecule cfg e d = 1 := by
  have h := descriptorWith_pullback input mol agreement admissible supported single cfg e calibrated
    d node atomEq reached atoms frame ops step stepFlip depth state ctx below belowMirror
  rw [pulled, original] at h
  exact flipDescriptorBy_some_eq _ (relativeSign_eq_one_or_neg_one _ _ _ _) x h.symm

variable (atomsPres : ∀ x, x < mol.atomCount →
  mol.atomAt? (relabelOf input (e : Equiv.Perm input.Atom) x) = mol.atomAt? x)

include agreement admissible supported single calibrated atomsPres atomEq reached frame in
/-- **Decoder on the actual recursion.** If the actual immediate-frame recursion generates the
same `some` label at an occurrence and at its image under the molecular automorphism (with the
image context), and the facts of the tied children agree under the original and pulled-back
geometries, then the automorphism has relative sign `1` at the occurrence's centre. -/
theorem relativeSign_eq_one_of_label_match (depth : Nat) (ctx : Option Nat)
    (below : ∀ mark, underWith mol (sparseOperations input mol)
        (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (inputGeometry input)) [] node
        (LocalizedMarkedOperationEvaluator.facts mol (sparseOperations input mol) depth) mark =
      underWith mol (sparseOperations input mol) (inputGeometry input) [] node
        (LocalizedMarkedOperationEvaluator.facts mol (sparseOperations input mol) depth) mark)
    (belowMirror : ∀ mark, underWith mol (sparseOperations input mol)
        (mirror (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (inputGeometry input)))
        [] node (LocalizedMarkedOperationEvaluator.facts mol (sparseOperations input mol) depth)
          mark =
      underWith mol (sparseOperations input mol) (mirror (inputGeometry input)) [] node
        (LocalizedMarkedOperationEvaluator.facts mol (sparseOperations input mol) depth) mark)
    (x : LocalizedTetrahedralRSPseudoDescriptor)
    (original : LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth
      (inputGeometry input) [] ctx node = some x)
    (image : LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth
      (inputGeometry input) [] (ctx.map (relabelOf input (e : Equiv.Perm input.Atom)))
      (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node) = some x) :
    relativeSign input.detectedMultiCenterMolecule cfg e d = 1 := by
  have wellFormed := admissible.1.1
  have unique := admissible.1.2
  have rawSingle := raw_single mol input agreement wellFormed unique supported single
  have sym := structuralSymmetry_of_aut input mol agreement admissible supported e atomsPres
  have cov := actual_covariant input mol agreement admissible supported single e atomsPres
  rw [descriptor_eq_descriptorWith] at original image
  rw [descriptorWith_map sym wellFormed unique rawSingle cov LocalizedMarkedOperationEvaluator.rawStep?
    (rawStep_map sym wellFormed unique rawSingle cov) depth (inputGeometry input) ctx node reached]
    at image
  rw [facts_eq_factsWith] at below belowMirror
  exact relativeSign_eq_one_of_descriptor input mol agreement admissible supported single cfg e
    calibrated d node atomEq reached atoms frame (sparseOperations input mol) _
    (rawStep_flip mol (sparseOperations input mol)) depth [] ctx below belowMirror x original image

end Physical

end TetraStereo.OneCenter.LocalizedChemicalRingOrientationReadback

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationReadback.consensus_flipBy
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationReadback.caseFromMirror_flipBy
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationReadback.flipDescriptorBy_some_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationReadback.rawStep_flip
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationReadback.distantStep_flip
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationReadback.descriptorWith_flip
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationReadback.exists_enumeration
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationReadback.readback_pullback_frame
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationReadback.descriptorWith_pullback
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationReadback.relativeSign_eq_one_of_descriptor
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationReadback.relativeSign_eq_one_of_label_match
