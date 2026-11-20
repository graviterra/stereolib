import TetraStereo.OneCenter.LocalizedChemicalRingOrientationReadback
import TetraStereo.OneCenter.LocalizedChemicalRingCompletenessRefusal
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Simultaneous induction: generated-label symmetry decodes to physical orientation

Let `σ` be a molecular automorphism (as a structural bijection of the raw molecule) and let the
actually generated labels be `σ`-symmetric at every occurrence, context and depth, for the input
geometry and its mirror (`symmetric`). Then, by a simultaneous induction over the finite generated
forest:

* `factsWith_pullback`: every generated fact list under the pulled-back geometry `pullback σ g`
  equals the one under `g` (for `g` the input geometry or its mirror);
* `sign_eq_one_of_label`: at every occurrence carrying a `some` label, the uniform readback sign of
  `σ` is `1`.

The physical instantiation (`nodeSign`, `flipsBy_input`) takes the sign at an occurrence of a
detected centre `d` to be `relativeSign σ d`, and `1` at degree-three occurrences, whose readbacks
are refused under either geometry. Consequences for the actual sparse recursion, both immediate
(`actual_facts_pullback`, `actual_relativeSign_eq_one`) and distant
(`distant_actual_facts_pullback`, `distant_actual_relativeSign_eq_one`): a `σ`-symmetric generated
state forces proper sense `relativeSign σ d = 1` at every labelled framed descendant.

Root consequences (`readingOf_relabel_of_symmetric`, `assignCenter_none_of_symmetric_odd`): the
reading relation along a centre-fixing automorphism and the odd refusal theorem hold with the
physical `proper` premise replaced by generated-label symmetry. Thus the stereochemical content the
evaluator needs from a reconstructed automorphism is exactly label symmetry of the actual
recursion. Label symmetry for the ROOT context alone (the facts recorded in the root state) is
weaker than this hypothesis; see the run status for the precise remaining obligation.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingOrientationInduction

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingRelabel LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingSenseTransport
open LocalizedChemicalRingCompletenessStrict LocalizedChemicalRingCompletenessMarked
open LocalizedChemicalRingCompletenessMirror LocalizedChemicalRingCompletenessOrbit
open LocalizedChemicalRingCompletenessRefusal
open LocalizedChemicalRingCompletenessGeneralPhysical (actual_covariant structuralSymmetry_of_aut)
open LocalizedChemicalRingCompletenessPermutationTransport (descriptorWith_map)
open LocalizedChemicalRingOrientationReadback
open LocalizedMarkedOperationEvaluator (Operations underWith mem_tiedChildren_actual)
open LocalizedMarkedReachableConfigurations
open LocalizedMarkedReachedFrameNeighbors (frame_atoms_perm_neighbors reached_atom_valid SingleBonded)
open LocalizedMarkedCertifiedTerminalRefusal (raw_single raw_atom_bound)
open LocalizedMarkedConfigurationTransport (readback_none_of_missing)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedGenericMarkedRecalculation (Geometry frameAtoms? readback? consensus mirror
  caseFromMirror? readback_mirror flatMap_congr_mem structuralDepth)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign relativeSign_eq_one_or_neg_one)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

theorem mirror_mirror (g : Geometry) : mirror (mirror g) = g := by
  funext a
  show ((g a).map CartesianPoint3.reflectX).map CartesianPoint3.reflectX = g a
  cases g a with
  | none => rfl
  | some p => simp [CartesianPoint3.reflectX_involutive]

/-! ## Generic induction -/

section Generic

variable (mol : RawMolecule) (ops : Operations) (step : Step)

/-- A step that refuses at an occurrence without a frame. -/
def StepNoFrame : Prop :=
  ∀ (geom : Geometry) state ctx (node : RawMolecule.CanonicalBranchNode) under,
    frameAtoms? mol node = none → step mol ops geom state ctx node under = none

theorem rawStep_noFrame : StepNoFrame mol ops LocalizedMarkedOperationEvaluator.rawStep? := by
  intro geom state ctx node under frame
  simp [LocalizedMarkedOperationEvaluator.rawStep?, frame]

theorem distantStep_noFrame : StepNoFrame mol ops LocalizedPhysicalMarkedDistantReference.rawStep? := by
  intro geom state ctx node under frame
  simp [LocalizedPhysicalMarkedDistantReference.rawStep?, frame]

theorem descriptorWith_none_of_frame (noFrame : StepNoFrame mol ops step) (depth : Nat)
    (geom : Geometry) (state : OccurrenceAuxState) (ctx : Option Nat)
    (node : RawMolecule.CanonicalBranchNode) (frame : frameAtoms? mol node = none) :
    descriptorWith step mol ops depth geom state ctx node = none := by
  unfold descriptorWith
  rw [noFrame _ _ _ _ _ frame, noFrame _ _ _ _ _ frame]
  rfl

theorem descriptorWith_mirror_none_iff (depth : Nat) (g : Geometry) (state : OccurrenceAuxState)
    (ctx : Option Nat) (node : RawMolecule.CanonicalBranchNode) :
    descriptorWith step mol ops depth (mirror g) state ctx node = none ↔
      descriptorWith step mol ops depth g state ctx node = none := by
  unfold descriptorWith
  rw [mirror_mirror, caseFromMirror?_eq_none_iff, caseFromMirror?_eq_none_iff]
  exact or_comm

/-- Readbacks under the pulled-back geometry flip uniformly at every reached frame, by a sign
that depends only on the occurrence. -/
def FlipsBy (σ : Nat → Nat) (sign : RawMolecule.CanonicalBranchNode → ℝ) (g : Geometry) : Prop :=
  ∀ node, Reached mol node → ∀ atoms, frameAtoms? mol node = some atoms →
    ∀ L : List Nat, (∀ x ∈ L, x ∈ atoms) →
      readback? (pullback σ g) L = flipBy (sign node) (readback? g L)

theorem FlipsBy.mirror {σ : Nat → Nat} {sign : RawMolecule.CanonicalBranchNode → ℝ} {g : Geometry}
    (h : FlipsBy mol σ sign g) : FlipsBy mol σ sign (mirror g) := by
  intro node reached atoms frame L sub
  rw [← mirror_pullback, readback_mirror, readback_mirror, h node reached atoms frame L sub,
    flipBy_map_swap]

variable {σ : Nat → Nat} (sym : StructuralSymmetry mol σ) (wellFormed : mol.WellFormed)
  (unique : mol.BondRecordsUnique) (single : SingleBonded mol) (cov : Covariant mol ops σ)
  (stepMap : StepMap step mol ops σ) (stepFlip : StepFlip mol ops step)
  (noFrame : StepNoFrame mol ops step)
  (sign : RawMolecule.CanonicalBranchNode → ℝ) (unit : ∀ node, sign node = 1 ∨ sign node = -1)

include sym wellFormed unique single cov stepMap stepFlip noFrame unit in
/-- One occurrence: with the children's facts agreeing under both geometry pairs, label symmetry
at the occurrence gives equal descriptors under the pulled-back geometry, and a `some` label
forces the occurrence sign to be `1`. -/
theorem descriptorWith_pullback_eq (g : Geometry) (flips : FlipsBy mol σ sign g) (depth : Nat)
    (ctx : Option Nat) (node : RawMolecule.CanonicalBranchNode) (reached : Reached mol node)
    (symmetricAt : descriptorWith step mol ops depth g [] (ctx.map σ) (mapNode σ node) =
      descriptorWith step mol ops depth g [] ctx node)
    (below : ∀ child ∈ mol.canonicalChildren node, ∀ ctx',
      factsWith step mol ops depth (pullback σ g) [] ctx' child =
        factsWith step mol ops depth g [] ctx' child)
    (belowMirror : ∀ child ∈ mol.canonicalChildren node, ∀ ctx',
      factsWith step mol ops depth (pullback σ (mirror g)) [] ctx' child =
        factsWith step mol ops depth (mirror g) [] ctx' child) :
    descriptorWith step mol ops depth (pullback σ g) [] ctx node =
        descriptorWith step mol ops depth g [] ctx node ∧
      ∀ x, descriptorWith step mol ops depth g [] ctx node = some x → sign node = 1 := by
  have transported := descriptorWith_map sym wellFormed unique single cov step stepMap depth g ctx
    node reached
  rw [symmetricAt] at transported
  refine ⟨transported.symm, ?_⟩
  intro x label
  cases frame : frameAtoms? mol node with
  | none =>
      rw [descriptorWith_none_of_frame mol ops step noFrame depth g [] ctx node frame] at label
      cases label
  | some atoms =>
      have underBelow : ∀ mark, underWith mol ops (pullback σ g) [] node (factsWith step mol ops depth)
          mark = underWith mol ops g [] node (factsWith step mol ops depth) mark := by
        intro mark
        unfold underWith
        exact flatMap_congr_mem _ _ _ fun child member =>
          below child (mem_tiedChildren_actual mol ops [] node child member) (some mark)
      have underBelowMirror : ∀ mark,
          underWith mol ops (mirror (pullback σ g)) [] node (factsWith step mol ops depth) mark =
            underWith mol ops (mirror g) [] node (factsWith step mol ops depth) mark := by
        intro mark
        rw [mirror_pullback]
        unfold underWith
        exact flatMap_congr_mem _ _ _ fun child member =>
          belowMirror child (mem_tiedChildren_actual mol ops [] node child member) (some mark)
      have flipped := descriptorWith_flip mol ops step stepFlip (sign node) (pullback σ g) g depth
        node atoms frame (flips node reached atoms frame) [] ctx underBelow underBelowMirror
      rw [transported.symm, label] at flipped
      exact flipDescriptorBy_some_eq _ (unit node) x flipped.symm

include sym wellFormed unique single cov stepMap stepFlip noFrame unit in
/-- **Simultaneous induction.** Under label symmetry for the geometry and its mirror, the
generated facts under the pulled-back geometry are the generated facts, at every depth, context
and reached occurrence. -/
theorem factsWith_pullback (G : Geometry) (flips : FlipsBy mol σ sign G)
    (symmetric : ∀ g, (g = G ∨ g = mirror G) → ∀ depth ctx node, Reached mol node →
      descriptorWith step mol ops depth g [] (ctx.map σ) (mapNode σ node) =
        descriptorWith step mol ops depth g [] ctx node) :
    ∀ depth g, (g = G ∨ g = mirror G) → ∀ ctx node, Reached mol node →
      factsWith step mol ops depth (pullback σ g) [] ctx node =
        factsWith step mol ops depth g [] ctx node := by
  intro depth
  induction depth with
  | zero => intros; rfl
  | succ depth ih =>
      intro g hg ctx node reached
      have flipsG : FlipsBy mol σ sign g := by
        rcases hg with rfl | rfl
        · exact flips
        · exact flips.mirror
      have hgm : mirror g = G ∨ mirror g = mirror G := by
        rcases hg with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl (mirror_mirror G)
      have head := (descriptorWith_pullback_eq mol ops step sym wellFormed unique single cov stepMap
        stepFlip noFrame sign unit g flipsG depth ctx node reached
        (symmetric g hg depth ctx node reached)
        (fun child member ctx' => ih g hg ctx' child (reached_child mol node child reached member))
        (fun child member ctx' =>
          ih (mirror g) hgm ctx' child (reached_child mol node child reached member))).1
      rw [factsWith_succ, factsWith_succ, head]
      congr 1
      exact flatMap_congr_mem _ _ _ fun child member =>
        ih g hg ctx child (reached_child mol node child reached member)

include sym wellFormed unique single cov stepMap stepFlip noFrame unit in
/-- **Decoded orientation.** Under label symmetry, every occurrence carrying a `some` label has
sign `1`. -/
theorem sign_eq_one_of_label (G : Geometry) (flips : FlipsBy mol σ sign G)
    (symmetric : ∀ g, (g = G ∨ g = mirror G) → ∀ depth ctx node, Reached mol node →
      descriptorWith step mol ops depth g [] (ctx.map σ) (mapNode σ node) =
        descriptorWith step mol ops depth g [] ctx node)
    (depth : Nat) (ctx : Option Nat) (node : RawMolecule.CanonicalBranchNode)
    (reached : Reached mol node) (x : LocalizedTetrahedralRSPseudoDescriptor)
    (label : descriptorWith step mol ops depth G [] ctx node = some x) : sign node = 1 :=
  (descriptorWith_pullback_eq mol ops step sym wellFormed unique single cov stepMap stepFlip noFrame
    sign unit G flips depth ctx node reached (symmetric G (Or.inl rfl) depth ctx node reached)
    (fun child member ctx' => factsWith_pullback mol ops step sym wellFormed unique single cov
      stepMap stepFlip noFrame sign unit G flips symmetric depth G (Or.inl rfl) ctx' child
      (reached_child mol node child reached member))
    (fun child member ctx' => factsWith_pullback mol ops step sym wellFormed unique single cov
      stepMap stepFlip noFrame sign unit G flips symmetric depth (mirror G) (Or.inr rfl) ctx' child
      (reached_child mol node child reached member))).2 x label

end Generic

/-! ## Physical instantiation -/

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

/-- The uniform readback sign of the automorphism at an occurrence: the relative sign at the
detected centre of a four-coordinate occurrence atom, `1` elsewhere. -/
noncomputable def nodeSign (node : RawMolecule.CanonicalBranchNode) : ℝ :=
  if h : node.atom < mol.atomCount ∧ (mol.canonicalIncidentNeighbors node.atom).length = 4 then
    relativeSign input.detectedMultiCenterMolecule cfg e
      ⟨atomOf mol input agreement node.atom h.1,
        center_of_degree mol input agreement admissible.1.1 admissible.1.2 supported node.atom h.1 h.2⟩
  else 1

theorem nodeSign_unit (node : RawMolecule.CanonicalBranchNode) :
    nodeSign input mol agreement admissible supported cfg e node = 1 ∨
      nodeSign input mol agreement admissible supported cfg e node = -1 := by
  unfold nodeSign
  split_ifs
  · exact relativeSign_eq_one_or_neg_one _ _ _ _
  · exact Or.inl rfl

include single in
/-- At an occurrence of a detected centre, the node sign is the relative sign at that centre. -/
theorem nodeSign_eq (d : input.detectedMultiCenterMolecule.Center)
    (node : RawMolecule.CanonicalBranchNode) (atomEq : node.atom = d.1.val)
    (reached : Reached mol node) (atoms : List Nat) (frame : frameAtoms? mol node = some atoms) :
    nodeSign input mol agreement admissible supported cfg e node =
      relativeSign input.detectedMultiCenterMolecule cfg e d := by
  have wellFormed := admissible.1.1
  have unique := admissible.1.2
  have rawSingle := raw_single mol input agreement wellFormed unique supported single
  have valid := reached_atom_valid mol wellFormed node reached
  have four : (mol.canonicalIncidentNeighbors node.atom).length = 4 := by
    rcases frame_atoms_perm_neighbors mol wellFormed rawSingle node reached atoms frame with
      ⟨four, _⟩ | ⟨three, _⟩
    · exact four
    · exfalso
      have subset : baseFrame input d ⊆ mol.canonicalIncidentNeighbors d.1.val := by
        intro y hy
        apply (mem_neighbors_iff mol input agreement wellFormed unique supported d y).mpr
        simp only [baseFrame, Equiv.Perm.one_apply, List.mem_cons, List.mem_nil_iff, or_false] at hy
        rcases hy with rfl | rfl | rfl | rfl
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
        · exact ⟨2, rfl⟩
        · exact ⟨3, rfl⟩
      have le := ((baseFrame_nodup input d).subperm subset).length_le
      rw [baseFrame_length] at le
      rw [atomEq] at three
      omega
  unfold nodeSign
  rw [dif_pos ⟨valid, four⟩]
  have centerEq : (⟨atomOf mol input agreement node.atom valid,
      center_of_degree mol input agreement wellFormed unique supported node.atom valid four⟩ :
        input.detectedMultiCenterMolecule.Center) = d := by
    apply Subtype.ext
    apply Fin.ext
    simp only [atomOf_val]
    exact atomEq
  rw [centerEq]

include agreement admissible supported single calibrated in
/-- The input geometry flips by the node sign under the pulled-back geometry at every reached
frame. Degree-three frames contain the phantom atom and refuse under both geometries. -/
theorem flipsBy_input :
    FlipsBy mol (relabelOf input (e : Equiv.Perm input.Atom))
      (nodeSign input mol agreement admissible supported cfg e) (inputGeometry input) := by
  intro node reached atoms frame L sub
  have wellFormed := admissible.1.1
  have unique := admissible.1.2
  have rawSingle := raw_single mol input agreement wellFormed unique supported single
  have valid := reached_atom_valid mol wellFormed node reached
  rcases frame_atoms_perm_neighbors mol wellFormed rawSingle node reached atoms frame with
    ⟨four, _⟩ | ⟨three, perm⟩
  · let d : input.detectedMultiCenterMolecule.Center :=
      ⟨atomOf mol input agreement node.atom valid,
        center_of_degree mol input agreement wellFormed unique supported node.atom valid four⟩
    have signEq : nodeSign input mol agreement admissible supported cfg e node =
        relativeSign input.detectedMultiCenterMolecule cfg e d := by
      unfold nodeSign
      rw [dif_pos ⟨valid, four⟩]
    rw [signEq]
    exact readback_pullback_frame input mol agreement admissible supported single cfg e calibrated d
      node rfl reached atoms frame L sub
  · have signOne : nodeSign input mol agreement admissible supported cfg e node = 1 := by
      unfold nodeSign
      rw [dif_neg]
      rintro ⟨_, four⟩
      rw [three] at four
      cases four
    rw [signOne, flipBy_eq_id _ rfl, id_eq, ← readback_map]
    have phantomNone : inputGeometry input mol.atomCount = none :=
      inputGeometry_outside input _ (by rw [count mol input agreement])
    by_cases phantom : mol.atomCount ∈ L
    · have left : readback? (inputGeometry input)
          (L.map (relabelOf input (e : Equiv.Perm input.Atom))) = none := by
        refine readback_none_of_missing _ _ (relabelOf input _ mol.atomCount)
          (List.mem_map_of_mem phantom) ?_
        rw [relabelOf_outside input _ _ (by rw [count mol input agreement])]
        exact phantomNone
      rw [left, readback_none_of_missing _ L _ phantom phantomNone]
    · have subNeighbors : ∀ y ∈ L, y ∈ mol.canonicalIncidentNeighbors node.atom := by
        intro y hy
        have member := perm.mem_iff.mp (sub y hy)
        rw [List.mem_append, List.mem_singleton] at member
        rcases member with inside | isPhantom
        · exact inside
        · exact absurd (isPhantom ▸ hy) phantom
      have bad : ¬ (L.length = 4 ∧ L.Nodup) := by
        rintro ⟨four, nodup⟩
        have := (nodup.subperm subNeighbors).length_le
        rw [four, three] at this
        omega
      rw [readback_none_of_not_good _ _ (not_good_map _ L bad), readback_none_of_not_good _ L bad]

variable (atomsPres : ∀ x, x < mol.atomCount →
  mol.atomAt? (relabelOf input (e : Equiv.Perm input.Atom) x) = mol.atomAt? x)

/-- Label symmetry of the actual immediate-frame recursion under `σ`, for the input geometry and
its mirror. -/
def Symmetric : Prop :=
  ∀ g, (g = inputGeometry input ∨ g = mirror (inputGeometry input)) →
    ∀ depth ctx node, Reached mol node →
      LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth g []
          (ctx.map (relabelOf input (e : Equiv.Perm input.Atom)))
          (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node) =
        LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth g [] ctx
          node

/-- Label symmetry of the actual distant-reference recursion. -/
def DistantSymmetric : Prop :=
  ∀ g, (g = inputGeometry input ∨ g = mirror (inputGeometry input)) →
    ∀ depth ctx node, Reached mol node →
      LocalizedPhysicalMarkedDistantEvaluator.descriptor? mol (sparseOperations input mol) depth g []
          (ctx.map (relabelOf input (e : Equiv.Perm input.Atom)))
          (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node) =
        LocalizedPhysicalMarkedDistantEvaluator.descriptor? mol (sparseOperations input mol) depth g
          [] ctx node

include agreement admissible supported single calibrated atomsPres in
/-- **Actual immediate-frame recursion: a symmetric generated state is invariant under the
pulled-back geometry.** -/
theorem actual_facts_pullback (symmetric : Symmetric input mol e) :
    ∀ depth g, (g = inputGeometry input ∨ g = mirror (inputGeometry input)) →
      ∀ ctx node, Reached mol node →
        LocalizedMarkedOperationEvaluator.facts mol (sparseOperations input mol) depth
            (pullback (relabelOf input (e : Equiv.Perm input.Atom)) g) [] ctx node =
          LocalizedMarkedOperationEvaluator.facts mol (sparseOperations input mol) depth g [] ctx
            node := by
  have wellFormed := admissible.1.1
  have unique := admissible.1.2
  have rawSingle := raw_single mol input agreement wellFormed unique supported single
  have sym := structuralSymmetry_of_aut input mol agreement admissible supported e atomsPres
  have cov := actual_covariant input mol agreement admissible supported single e atomsPres
  intro depth g hg ctx node reached
  rw [facts_eq_factsWith]
  exact factsWith_pullback mol (sparseOperations input mol) _ sym wellFormed unique rawSingle cov
    (rawStep_map sym wellFormed unique rawSingle cov) (rawStep_flip mol _) (rawStep_noFrame mol _)
    (nodeSign input mol agreement admissible supported cfg e)
    (nodeSign_unit input mol agreement admissible supported cfg e) (inputGeometry input)
    (flipsBy_input input mol agreement admissible supported single cfg e calibrated)
    (fun g hg depth ctx node reached => by
      rw [← descriptor_eq_descriptorWith, ← descriptor_eq_descriptorWith]
      exact symmetric g hg depth ctx node reached)
    depth g hg ctx node reached

include agreement admissible supported single calibrated atomsPres in
/-- **Actual immediate-frame recursion: a symmetric generated state has proper sense at every
labelled framed descendant.** -/
theorem actual_relativeSign_eq_one (symmetric : Symmetric input mol e) (depth : Nat)
    (ctx : Option Nat) (node : RawMolecule.CanonicalBranchNode) (reached : Reached mol node)
    (d : input.detectedMultiCenterMolecule.Center) (atomEq : node.atom = d.1.val) (atoms : List Nat)
    (frame : frameAtoms? mol node = some atoms) (x : LocalizedTetrahedralRSPseudoDescriptor)
    (label : LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth
      (inputGeometry input) [] ctx node = some x) :
    relativeSign input.detectedMultiCenterMolecule cfg e d = 1 := by
  have wellFormed := admissible.1.1
  have unique := admissible.1.2
  have rawSingle := raw_single mol input agreement wellFormed unique supported single
  have sym := structuralSymmetry_of_aut input mol agreement admissible supported e atomsPres
  have cov := actual_covariant input mol agreement admissible supported single e atomsPres
  rw [descriptor_eq_descriptorWith] at label
  rw [← nodeSign_eq input mol agreement admissible supported single cfg e d node atomEq reached
    atoms frame]
  exact sign_eq_one_of_label mol (sparseOperations input mol) _ sym wellFormed unique rawSingle cov
    (rawStep_map sym wellFormed unique rawSingle cov) (rawStep_flip mol _) (rawStep_noFrame mol _)
    (nodeSign input mol agreement admissible supported cfg e)
    (nodeSign_unit input mol agreement admissible supported cfg e) (inputGeometry input)
    (flipsBy_input input mol agreement admissible supported single cfg e calibrated)
    (fun g hg depth ctx node reached => by
      rw [← descriptor_eq_descriptorWith, ← descriptor_eq_descriptorWith]
      exact symmetric g hg depth ctx node reached)
    depth ctx node reached x label

include agreement admissible supported single calibrated atomsPres in
theorem distant_actual_facts_pullback (symmetric : DistantSymmetric input mol e) :
    ∀ depth g, (g = inputGeometry input ∨ g = mirror (inputGeometry input)) →
      ∀ ctx node, Reached mol node →
        LocalizedPhysicalMarkedDistantEvaluator.facts mol (sparseOperations input mol) depth
            (pullback (relabelOf input (e : Equiv.Perm input.Atom)) g) [] ctx node =
          LocalizedPhysicalMarkedDistantEvaluator.facts mol (sparseOperations input mol) depth g []
            ctx node := by
  have wellFormed := admissible.1.1
  have unique := admissible.1.2
  have rawSingle := raw_single mol input agreement wellFormed unique supported single
  have sym := structuralSymmetry_of_aut input mol agreement admissible supported e atomsPres
  have cov := actual_covariant input mol agreement admissible supported single e atomsPres
  intro depth g hg ctx node reached
  rw [distant_facts_eq_factsWith]
  exact factsWith_pullback mol (sparseOperations input mol) _ sym wellFormed unique rawSingle cov
    (distantStep_map sym wellFormed unique rawSingle cov) (distantStep_flip mol _)
    (distantStep_noFrame mol _)
    (nodeSign input mol agreement admissible supported cfg e)
    (nodeSign_unit input mol agreement admissible supported cfg e) (inputGeometry input)
    (flipsBy_input input mol agreement admissible supported single cfg e calibrated)
    (fun g hg depth ctx node reached => by
      rw [← distant_descriptor_eq_descriptorWith, ← distant_descriptor_eq_descriptorWith]
      exact symmetric g hg depth ctx node reached)
    depth g hg ctx node reached

include agreement admissible supported single calibrated atomsPres in
theorem distant_actual_relativeSign_eq_one (symmetric : DistantSymmetric input mol e) (depth : Nat)
    (ctx : Option Nat) (node : RawMolecule.CanonicalBranchNode) (reached : Reached mol node)
    (d : input.detectedMultiCenterMolecule.Center) (atomEq : node.atom = d.1.val) (atoms : List Nat)
    (frame : frameAtoms? mol node = some atoms) (x : LocalizedTetrahedralRSPseudoDescriptor)
    (label : LocalizedPhysicalMarkedDistantEvaluator.descriptor? mol (sparseOperations input mol)
      depth (inputGeometry input) [] ctx node = some x) :
    relativeSign input.detectedMultiCenterMolecule cfg e d = 1 := by
  have wellFormed := admissible.1.1
  have unique := admissible.1.2
  have rawSingle := raw_single mol input agreement wellFormed unique supported single
  have sym := structuralSymmetry_of_aut input mol agreement admissible supported e atomsPres
  have cov := actual_covariant input mol agreement admissible supported single e atomsPres
  rw [distant_descriptor_eq_descriptorWith] at label
  rw [← nodeSign_eq input mol agreement admissible supported single cfg e d node atomEq reached
    atoms frame]
  exact sign_eq_one_of_label mol (sparseOperations input mol) _ sym wellFormed unique rawSingle cov
    (distantStep_map sym wellFormed unique rawSingle cov) (distantStep_flip mol _)
    (distantStep_noFrame mol _)
    (nodeSign input mol agreement admissible supported cfg e)
    (nodeSign_unit input mol agreement admissible supported cfg e) (inputGeometry input)
    (flipsBy_input input mol agreement admissible supported single cfg e calibrated)
    (fun g hg depth ctx node reached => by
      rw [← distant_descriptor_eq_descriptorWith, ← distant_descriptor_eq_descriptorWith]
      exact symmetric g hg depth ctx node reached)
    depth ctx node reached x label

/-! ## Root consequences: label symmetry replaces the physical sense premise -/

variable (c : input.detectedMultiCenterMolecule.Center)
  (fixed : input.detectedMultiCenterMolecule.centerPerm e c = c)

include agreement admissible supported single calibrated atomsPres fixed in
/-- The root's generated facts for the relabelled reference are the relabelled generated facts,
from label symmetry alone. -/
theorem generated_perm_of_symmetric (symmetric : Symmetric input mol e) (r : Nat) :
    (generated input mol c (inputGeometry input) (relabelOf input (e : Equiv.Perm input.Atom) r)).Perm
      ((generated input mol c (inputGeometry input) r).map
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
    (canonicalCenterRoot c.1.val) reached r
  rw [root_fixed input e c fixed, ← facts_eq_factsWith] at transport
  refine transport.trans (List.Perm.of_eq ?_)
  congr 1
  unfold generated underWith
  apply flatMap_congr_mem
  intro child member
  exact actual_facts_pullback input mol agreement admissible supported single cfg e calibrated
    atomsPres symmetric _ (inputGeometry input) (Or.inl rfl) (some r) child
    (reached_child mol _ child reached (mem_tiedChildren_actual mol _ [] _ child member))

include agreement admissible supported single calibrated atomsPres fixed in
/-- **Reading relation from label symmetry**: the reading of the eligible reference `τ k` is
the reading of `k` or its complement according to the parity of `τ = ligandPermAt e c`. -/
theorem readingOf_relabel_of_symmetric (symmetric : Symmetric input mol e)
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
    (generated_perm_of_symmetric input mol agreement admissible supported single cfg e calibrated
      atomsPres c fixed symmetric _)

include agreement admissible supported single calibrated atomsPres fixed in
/-- **Refusal from label symmetry and odd parity**: no physical sense premise. -/
theorem assignCenter_none_of_symmetric_odd (symmetric : Symmetric input mol e)
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
    rw [readingOf_relabel_of_symmetric input mol agreement admissible supported single cfg e
      calibrated atomsPres c fixed symmetric data k, if_neg (by rw [odd]; norm_num)]

end Physical

end TetraStereo.OneCenter.LocalizedChemicalRingOrientationInduction

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationInduction.mirror_mirror
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationInduction.descriptorWith_pullback_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationInduction.factsWith_pullback
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationInduction.sign_eq_one_of_label
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationInduction.nodeSign_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationInduction.flipsBy_input
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationInduction.actual_facts_pullback
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationInduction.actual_relativeSign_eq_one
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationInduction.distant_actual_facts_pullback
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationInduction.distant_actual_relativeSign_eq_one
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationInduction.generated_perm_of_symmetric
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationInduction.readingOf_relabel_of_symmetric
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationInduction.assignCenter_none_of_symmetric_odd
