import TetraStereo.OneCenter.LocalizedCyclicWitnessedPhysicalTransport
import TetraStereo.OneCenter.LocalizedCyclicPhysicalTerminalTwinTransport
import TetraStereo.OneCenter.LocalizedCyclicGeneralRigidLabelCovariance
import TetraStereo.OneCenter.LocalizedCyclicRootBranchReaderClassification
import TetraStereo.OneCenter.LocalizedActualOrderedRootPhysicalDataCore
import TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0

/-! # Cyclic physical transport from witnessed current root observations

This module connects the residual component used by actual boundary reconstruction to the
physical rooted ligand branch.  It is the graph-theoretic bridge needed to consume one witnessed
path for each actual center when constructing a physical branch transport.

## The physical inverse at an actual root

The second half assembles the inverse direction for the current RuleMajorReference reader at a
real carrier occurrence with empty address (in particular the evaluator's own final root).

1. Two actual current `RuleMajorContextArm`s at frame slots `i ≠ j`, read with the target's
   actual context reader and tied constitutionally, give one molecular automorphism `π` fixing the
   root (`currentRootArm_witnessedAutomorphism`).  Every vertex of the source residual component,
   hence every center of the physical ligand branch (`ligandBranchReaches_implies_inComponent`),
   has one witnessed path whose two actual decorated nodes in those very arm trees sit at one
   ranked address.  The right node's occurrence is `transportOccurrence π` of the left one
   (`boundaryHistory_eq_transportOccurrence`).
2. A label correspondence on the same two trees (`UppercaseCorrespondence`, derived from actual
   matched descriptor tables in `LocalizedCyclicMatchedReadingDecode`) and the dependency reader's
   restriction law turn the two node labels into the actual generated states at the two
   occurrences.
3. At a reached center that is not a physical terminal twin, the domain gives calibration at the
   center and at its image.  The witness occurrence lies in the tied root arm, so its actual frame
   is constitutionally strict.  The two actual generated-label characterizations, the contextual
   priority covariance `τ' = slotPerm * τ` and the frame parity law `α' ∘ slotPerm = F ∘ α` feed
   the scalar decoder `matchedUppercaseLabels_decode_physicalSign`
   (`signLaw_of_matchedGeneratedLabels`).  No branch sign law is assumed.
4. Reached terminal-twin centers are repaired by actual twin swaps
   (`branchTransport_of_nonTwinSignLaw`); the root and the rigid-center signs are unchanged.

The endpoints read the label correspondence from actual compiled compound readings: matched
common-`R` readings (any own references) and a full compound tie give `ProperTransport`; matched
Rule-4b readings under opposite own references give `MirrorTransport`, and under one own
reference `ProperTransport`; an empty Rule-4b selection gives both.  Hence an actual prior tie
gives a mirror or a proper transport (`mirror_or_proper_of_priorTie`).  Under proper
distinguishability of the root ligand branches, distinct compiled compounds never tie through
Rule 5 and every actual prior tie is a physical enantiomorphic pair
(`finalRoot_physical_tie_classification`).  No acyclicity, reader law, sign law or desired
comparison is assumed; empty and multiple Rule-4b reference populations are covered because the
readings are arbitrary members of the actual reading lists.
-/

namespace TetraStereo.OneCenter
namespace LocalizedCyclicMatchedReadingPhysicalTransport

open CertifiedLocalizedCIPInput
open RetainedCoherentSymmetry
open RootedTetrahedralBranchSymmetry
open LocalizedCumulativeDecoratedTree
open LocalizedActualBoundaryPathRealization
open LocalizedCyclicGeneralRigidLabelCovariance

noncomputable section

/-- A vertex in the component left after deleting the root belongs to the actual physical ligand
branch whenever its component entry is that ligand's molecular neighbor. -/
theorem inComponent_implies_ligandBranchReaches
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) (c : m.Center) (i : Fin 4) (z : V)
    (h : InComponent m.mol [c.1] (m.ligandAtomAt c i) z) :
    LigandBranchReaches m c i z := by
  rcases h with ⟨_entryOutside, reachable⟩
  rcases reachable with ⟨w⟩
  let f : residualGraph m.mol [c.1] →g m.mol.underlyingSimpleGraph :=
    { toFun := id
      map_rel' := by
        intro x y edge
        exact (residual_adj_iff m.mol [c.1] x y).mp edge |>.2.2 }
  have supportAvoids : ∀ {x y} (path : (residualGraph m.mol [c.1]).Walk x y),
      x ∉ [c.1] → ∀ a, a ∈ path.support → a ∉ [c.1] := by
    intro x y path
    induction path with
    | nil =>
        intro hx a ha
        simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at ha
        subst a
        exact hx
    | @cons x y z edge rest ih =>
        intro hx a ha
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at ha
        rcases ha with rfl | ha
        · exact ((residual_adj_iff m.mol [c.1] a y).mp edge).1
        · exact ih ((residual_adj_iff m.mol [c.1] x y).mp edge).2.1 a ha
  have noRoot : c.1 ∉ w.support := by
    intro rootMem
    exact (supportAvoids w _entryOutside c.1 rootMem) (by simp)
  refine ⟨(w.map f).copy rfl rfl, ?_⟩
  intro rootMem
  have originalMem : c.1 ∈ w.support := by
    simpa [f, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map] using rootMem
  exact noRoot originalMem

/-- A matched observation at one shared ranked address is a matched value of the actual readers at
the two source cursors. The trees and traces are the current supplied `RuleMajorContextArm`s; this
does not compare independent reroots or impose a reader law. -/
theorem sameAddress_labelEq_implies_readEq
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {stageL stageR : LocalizedCumulativeRule45Stage}
    {readL readR : input.LocalizedRerootCursor fuel → Option LocalizedAuxiliaryLabel}
    {left right : input.LocalizedRerootCursor fuel}
    (armL : input.RuleMajorContextArm fuel stageL readL left)
    (armR : input.RuleMajorContextArm fuel stageR readR right)
    (address : List ℕ)
    (subtreeL subtreeR : LocalizedCumulativeDecoratedTree input fuel)
    (lookupL : armL.tree.decoratedSubtreeAt? address = some subtreeL)
    (lookupR : armR.tree.decoratedSubtreeAt? address = some subtreeR)
    (labels : subtreeL.label = subtreeR.label) :
    readL subtreeL.source = readR subtreeR.source := by
  have realizesL := LocalizedRuleMajorSortTrace.realizes_of_trace armL.trace
  have realizesR := LocalizedRuleMajorSortTrace.realizes_of_trace armR.trace
  have realizesSubL := realizes_of_decoratedSubtreeAt? armL.tree realizesL address subtreeL lookupL
  have realizesSubR := realizes_of_decoratedSubtreeAt? armR.tree realizesR address subtreeR lookupR
  have readL' : subtreeL.label = readL subtreeL.source := by
    rw [realizesSubL]
    rfl
  have readR' : subtreeR.label = readR subtreeR.source := by
    rw [realizesSubR]
    rfl
  calc
    readL subtreeL.source = subtreeL.label := readL'.symm
    _ = subtreeR.label := labels
    _ = readR subtreeR.source := readR'

/-- Actual occurrences with the full boundary histories of a witnessed path and its molecular
image are identified by their molecular occurrence units. This uses root plus full history; it
does not identify the numerical sibling addresses under the two independent atom-index orders. -/
theorem boundaryHistory_eq_transportOccurrence
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    {fuel : Nat} (e : input.moleculeGraph.Aut) (root : input.Atom)
    (fixesRoot : (e : Equiv.Perm input.Atom) root = root)
    {p : List input.Atom}
    (left right : input.LocalizedCIPOccurrence fuel)
    (leftRoot : left.1.root = root)
    (leftHistory : left.1.node = boundaryNode [root] p)
    (rightHistory : right.1.node = boundaryNode [root] (p.map e))
    (rightRoot : right.1.root = root) :
    right = input.transportOccurrence singleBonded e left := by
  apply input.molecularFrameUnit_injective_on_simpleBonded_carrier singleBonded
    right (input.transportOccurrence singleBonded e left)
  apply congrArg₂ TetraStereo.OneCenter.DeclarativeCIP.OccurrenceUnit.mk
  · simp [rightRoot, leftRoot, fixesRoot]
  · simp [transportOccurrence_node, leftHistory, rightHistory, mapOfficialNode, boundaryNode, fixesRoot,
      List.map_reverse]

/-- The two uppercase generated-label tests decode a matched/reflected R/S observation into the
physical sign relation once contextual priority and detected-ligand permutation parity have been
transported. `common` is the source detected-ligand parity times its contextual priority parity;
`framePerm` is the local physical atom-frame permutation induced by the molecular automorphism. -/
theorem matchedUppercaseLabels_decode_physicalSign
    (sourceConfig imageConfig framePerm common : ℝ) (mirror : Bool)
    (configSourceUnit : sourceConfig = 1 ∨ sourceConfig = -1)
    (configImageUnit : imageConfig = 1 ∨ imageConfig = -1)
    (framePermUnit : framePerm = 1 ∨ framePerm = -1)
    (commonUnit : common = 1 ∨ common = -1)
    (labels : (if imageConfig * framePerm * common = -1 then RS.R else RS.S) =
      (if mirror then RS.swap (if sourceConfig * common = -1 then RS.R else RS.S)
        else if sourceConfig * common = -1 then RS.R else RS.S)) :
    sourceConfig * framePerm = physicalMirrorFactor mirror * imageConfig := by
  have sourceProductUnit : sourceConfig * common = 1 ∨ sourceConfig * common = -1 := by
    rcases configSourceUnit with h | h <;> rcases commonUnit with k | k <;>
      simp [h, k]
  have imageProductUnit : imageConfig * framePerm * common = 1 ∨
      imageConfig * framePerm * common = -1 := by
    rcases configImageUnit with h | h <;> rcases framePermUnit with k | k <;>
      rcases commonUnit with l | l <;> simp [h, k, l]
  have products : imageConfig * framePerm * common =
      physicalMirrorFactor mirror * (sourceConfig * common) := by
    rcases sourceProductUnit with hs | hs
    all_goals
      rcases imageProductUnit with hi | hi
      all_goals
        cases mirror
        all_goals simp [hs, hi, RS.swap, physicalMirrorFactor] at labels ⊢
        all_goals norm_num [RS.swap] at labels
        all_goals norm_num
        all_goals exact (by decide : RS.S ≠ RS.R) labels
  have framePermSq : framePerm * framePerm = 1 := by
    rcases framePermUnit with h | h <;> simp [h]
  have commonSq : common * common = 1 := by
    rcases commonUnit with h | h <;> simp [h]
  have mirrorSq : physicalMirrorFactor mirror * physicalMirrorFactor mirror = 1 := by
    cases mirror <;> norm_num [physicalMirrorFactor]
  have canceled : imageConfig = physicalMirrorFactor mirror * sourceConfig * framePerm := by
    calc
      imageConfig = imageConfig * ((framePerm * framePerm) * (common * common)) := by
        rw [framePermSq, commonSq]
        ring
      _ = (imageConfig * framePerm * common) * (framePerm * common) := by ring
      _ = (physicalMirrorFactor mirror * (sourceConfig * common)) *
          (framePerm * common) := by rw [products]
      _ = physicalMirrorFactor mirror * sourceConfig * framePerm * (common * common) := by ring
      _ = physicalMirrorFactor mirror * sourceConfig * framePerm := by rw [commonSq]; ring
  calc
    sourceConfig * framePerm =
        (physicalMirrorFactor mirror * physicalMirrorFactor mirror) *
          (sourceConfig * framePerm) := by rw [mirrorSq]; ring
    _ = physicalMirrorFactor mirror *
        (physicalMirrorFactor mirror * sourceConfig * framePerm) := by ring
    _ = physicalMirrorFactor mirror * imageConfig := by rw [canceled]

/-! ## The physical ligand branch is the residual component -/

/-- Converse of `inComponent_implies_ligandBranchReaches`: every vertex of the physical ligand
branch lies in the residual component of the ligand after deleting the root. -/
theorem ligandBranchReaches_implies_inComponent
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) (c : m.Center) (i : Fin 4) (z : V)
    (h : LigandBranchReaches m c i z) :
    InComponent m.mol [c.1] (m.ligandAtomAt c i) z := by
  obtain ⟨walk, avoids⟩ := h
  have transfer : ∀ {x y : V} (path : m.mol.underlyingSimpleGraph.Walk x y),
      c.1 ∉ path.support → (residualGraph m.mol [c.1]).Reachable x y := by
    intro x y path
    induction path with
    | nil => intro _; exact SimpleGraph.Reachable.refl _
    | @cons x y w edge rest ih =>
        intro avoid
        rw [SimpleGraph.Walk.support_cons, List.mem_cons, not_or] at avoid
        have xOutside : x ∉ [c.1] := by
          rw [List.mem_singleton]
          exact fun same => avoid.1 same.symm
        have yOutside : y ∉ [c.1] := by
          rw [List.mem_singleton]
          intro same
          apply avoid.2
          rw [← same]
          exact rest.start_mem_support
        have adjacent : (residualGraph m.mol [c.1]).Adj x y :=
          (residual_adj_iff m.mol [c.1] x y).mpr ⟨xOutside, yOutside, edge⟩
        exact adjacent.reachable.trans (ih avoid.2)
  refine ⟨?_, transfer walk avoids⟩
  rw [List.mem_singleton]
  exact ligandAtomAt_ne_center m c i

/-! ## Terminal-twin gauge repair -/

/-- The distinguished centers carrying a physical terminal twin pair. -/
abbrev TwinCenter {input : CertifiedLocalizedCIPInput} (m : MultiCenterMolecule input.Atom) :=
  {d : m.Center // ActualPhysicalTerminalTwinCenter input m d}

/-- The first chosen leaf of a twin center. -/
noncomputable def twinLeftLeaf {input : CertifiedLocalizedCIPInput}
    {m : MultiCenterMolecule input.Atom} (d : TwinCenter m) : input.Atom :=
  Classical.choose d.2

/-- The second chosen leaf of a twin center. -/
noncomputable def twinRightLeaf {input : CertifiedLocalizedCIPInput}
    {m : MultiCenterMolecule input.Atom} (d : TwinCenter m) : input.Atom :=
  Classical.choose (Classical.choose_spec d.2)

/-- The chosen leaves form an actual terminal twin pair, at distinct centers for distinct
indices: an actual gauge family. -/
theorem twinCenterFamily {input : CertifiedLocalizedCIPInput}
    (m : MultiCenterMolecule input.Atom) :
    TerminalTwinConfigurationGauge.TerminalTwinFamily m (fun d : TwinCenter m => d.1)
      twinLeftLeaf twinRightLeaf :=
  ⟨fun d => Classical.choose_spec (Classical.choose_spec d.2), Subtype.val_injective⟩

/-- **Terminal-twin gauge repair of a branch transport.** Let a molecular automorphism `e` fix the
root and send ligand `i` to `j`, and satisfy the branch sign law at every reached center that is
not a physical terminal twin.  Composing `e` with the actual twin swaps at the reached twin centers
whose sign law fails gives a physical branch transport.  The root, its ligand permutation and the
signs at all other centers are unchanged by the repair. -/
theorem branchTransport_of_nonTwinSignLaw
    {input : CertifiedLocalizedCIPInput} {m : MultiCenterMolecule input.Atom}
    (cfg : m.Configuration) (c : m.Center) (i j : Fin 4) (mirror : Bool) (e : m.Aut)
    (rootFixed : m.centerPerm e c = c) (ligandSent : m.ligandPermAt e c i = j)
    (signLaw : ∀ d : m.Center, LigandBranchReaches m c i d.1 →
      ¬ ActualPhysicalTerminalTwinCenter input m d →
      m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) =
        (if mirror then -1 else 1) * m.configurationSign cfg (m.centerPerm e d)) :
    BranchTransport m cfg c i j mirror := by
  classical
  have family := twinCenterFamily m
  let Mismatch : TwinCenter m → Prop := fun d => LigandBranchReaches m c i d.1.1 ∧
    m.configurationSign cfg d.1 * permHandedness (m.ligandPermAt e d.1) ≠
      (if mirror then -1 else 1) * m.configurationSign cfg (m.centerPerm e d.1)
  let repaired : List (TwinCenter m) := (Finset.univ.filter Mismatch).toList
  have nodup : repaired.Nodup := Finset.nodup_toList _
  have mismatch_of_mem : ∀ x ∈ repaired, Mismatch x := fun x member =>
    (Finset.mem_filter.mp (Finset.mem_toList.mp member)).2
  have rootOutside : c ∉ repaired.map (fun x : TwinCenter m => x.1) := by
    intro member
    obtain ⟨x, xMem, xEq⟩ := List.mem_map.mp member
    obtain ⟨⟨walk, avoids⟩, -⟩ := mismatch_of_mem x xMem
    have atomEq : x.1.1 = c.1 := congrArg Subtype.val xEq
    exact avoids (atomEq ▸ walk.end_mem_support)
  have unitProduct : ∀ d : m.Center,
      m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) = 1 ∨
        m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) = -1 := by
    intro d
    have unit := permHandedness_eq_one_or_eq_neg_one (cfg d * m.ligandPermAt e d)
    rw [permHandedness_mul] at unit
    exact unit
  have unitSign : ∀ d : m.Center,
      m.configurationSign cfg d = 1 ∨ m.configurationSign cfg d = -1 :=
    fun d => permHandedness_eq_one_or_eq_neg_one (cfg d)
  have flipped : ∀ (P Q μ : ℝ), (P = 1 ∨ P = -1) → (Q = 1 ∨ Q = -1) →
      (μ = 1 ∨ μ = -1) → P ≠ μ * Q → -P = μ * Q := by
    intro P Q μ hP hQ hμ hne
    have squareP : P * P = 1 := by
      rcases hP with rfl | rfl <;> norm_num
    have squareQ : (μ * Q) * (μ * Q) = 1 := by
      rcases hQ with rfl | rfl <;> rcases hμ with rfl | rfl <;> norm_num
    have product : (P - μ * Q) * (P + μ * Q) = 0 := by
      have expand : (P - μ * Q) * (P + μ * Q) = P * P - (μ * Q) * (μ * Q) := by ring
      rw [expand, squareP, squareQ]
      ring
    rcases mul_eq_zero.mp product with same | opposite
    · exact absurd (sub_eq_zero.mp same) hne
    · linarith
  have mirrorUnit : ((if mirror then -1 else 1 : ℝ)) = 1 ∨ (if mirror then -1 else 1 : ℝ) = -1 := by
    cases mirror <;> simp
  refine ⟨e * family.familyAut repaired, ?_, ?_, ?_⟩
  · rw [centerPerm_mul_apply, family.centerPerm_familyAut_apply, rootFixed]
  · rw [m.ligandPermAt_mul, family.centerPerm_familyAut_apply,
      family.ligandPermAt_familyAut_of_not_mem repaired c rootOutside, mul_one]
    exact ligandSent
  · intro d reached
    rw [centerPerm_mul_apply, family.centerPerm_familyAut_apply, m.ligandPermAt_mul,
      family.centerPerm_familyAut_apply, permHandedness_mul]
    by_cases member : d ∈ repaired.map (fun x : TwinCenter m => x.1)
    · obtain ⟨x, xMem, rfl⟩ := List.mem_map.mp member
      rw [family.ligandPermAt_familyAut_at_index repaired nodup x xMem,
        TerminalTwinConfigurationGauge.TerminalTwinPair.permHandedness_swap_of_ne
          (family.twin x).twinSlotA_ne_twinSlotB]
      have rewritten : m.configurationSign cfg x.1 *
          (permHandedness (m.ligandPermAt e x.1) * -1) =
          -(m.configurationSign cfg x.1 * permHandedness (m.ligandPermAt e x.1)) := by ring
      rw [rewritten]
      exact flipped _ _ _ (unitProduct x.1) (unitSign _) mirrorUnit (mismatch_of_mem x xMem).2
    · rw [family.ligandPermAt_familyAut_of_not_mem repaired d member, permHandedness_one,
        mul_one]
      by_cases twin : ActualPhysicalTerminalTwinCenter input m d
      · by_contra failed
        exact member (List.mem_map.mpr ⟨⟨d, twin⟩, Finset.mem_toList.mpr
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, reached, failed⟩), rfl⟩)
      · exact signLaw d reached twin

/-! ## Carrier occurrence facts -/

/-- A real carrier occurrence at the empty address has the one-atom history of its current atom,
which is its stored root. -/
theorem rootOccurrence_history (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (real : occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (rootAddress : occurrence.1.address = [])
    {atom : input.Atom} (current : occurrence.1.node.current? = some atom) :
    occurrence.1.node.history = [atom] ∧ occurrence.1.root = atom := by
  obtain ⟨_nodup, headEq⟩ :=
    LocalizedActualBoundaryObservationReadback.occurrence_history_facts input occurrence real
  have lastEq := input.frameCarrierOccurrence_history_getLast_eq_root occurrence
  have derived := (input.mem_localizedOccurrences_iff fuel occurrence.1).mp occurrence.2
  have depthEq :=
    (OutwardRule1bObserverEquivalence.carrierOccurrence_ranked_depth input derived).2
  rw [rootAddress] at depthEq
  unfold OfficialCIPNode.depth at depthEq
  rw [current] at headEq
  cases hist : occurrence.1.node.history with
  | nil =>
      rw [hist] at headEq
      simp at headEq
  | cons first rest =>
      rw [hist] at headEq lastEq depthEq
      cases rest with
      | nil =>
          have firstEq : first = atom := by simpa using headEq.symm
          have rootEq : first = occurrence.1.root := by simpa using lastEq
          exact ⟨by rw [firstEq], rootEq.symm.trans firstEq⟩
      | cons second rest' => simp at depthEq

/-- A carrier occurrence whose node is the boundary node of a path below `[root]` has root
`root` and address length the path length. -/
theorem boundaryOccurrence_facts (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) {root : input.Atom}
    {path : List input.Atom}
    (node : occurrence.1.node = boundaryNode [root] path) :
    occurrence.1.root = root ∧ occurrence.1.address.length = path.length := by
  have lastEq := input.frameCarrierOccurrence_history_getLast_eq_root occurrence
  rw [node, boundaryNode_history, List.getLast?_reverse] at lastEq
  have rootEq : occurrence.1.root = root := by simpa using lastEq.symm
  have derived := (input.mem_localizedOccurrences_iff fuel occurrence.1).mp occurrence.2
  have depthEq :=
    (OutwardRule1bObserverEquivalence.carrierOccurrence_ranked_depth input derived).2
  rw [node] at depthEq
  unfold OfficialCIPNode.depth at depthEq
  rw [boundaryNode_history] at depthEq
  simp at depthEq
  exact ⟨rootEq, by omega⟩

/-- A boundary occurrence below `[root]` whose path starts at `a` lies in the root branch of the
root-arm occurrence of `a`.  Both carrier addresses are read from their canonical root-first
histories. -/
theorem rootBranchContains_of_boundary (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (arm occurrence : input.LocalizedCIPOccurrence fuel) {root a : input.Atom}
    {rest : List input.Atom}
    (armRoot : arm.1.root = root) (armHistory : arm.1.node.history = [a, root])
    (occurrenceRoot : occurrence.1.root = root)
    (occurrenceNode : occurrence.1.node = boundaryNode [root] (a :: rest)) :
    input.RootBranchContains arm occurrence := by
  have armAddress := (input.legitimateOccurrence_transport singleBonded 1
    (input.carrierOccurrence_legitimate singleBonded arm)).sourceAddress
  have occurrenceAddress := (input.legitimateOccurrence_transport singleBonded 1
    (input.carrierOccurrence_legitimate singleBonded occurrence)).sourceAddress
  refine ⟨armRoot.trans occurrenceRoot.symm, ?_⟩
  rw [armAddress, occurrenceAddress, armRoot, occurrenceRoot]
  unfold CertifiedLocalizedCIPInput.canonicalAddress
  rw [armHistory, occurrenceNode, boundaryNode_history]
  simp

/-- The label of an addressed node of an actual current arm is the arm reader's value at the
node's source cursor. -/
theorem arm_label_eq_read {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor fuel → Option LocalizedAuxiliaryLabel}
    {cursor : input.LocalizedRerootCursor fuel}
    (arm : input.RuleMajorContextArm fuel stage read cursor) (address : List ℕ)
    (node : LocalizedCumulativeDecoratedTree input fuel)
    (lookup : arm.tree.decoratedSubtreeAt? address = some node) :
    node.label = read node.source := by
  have realizes := LocalizedRuleMajorSortTrace.realizes_of_trace arm.trace
  have realized := realizes_of_decoratedSubtreeAt? arm.tree realizes address node lookup
  rw [realized]
  rfl

/-! ## The inverse sign law at one rigid center -/

section RigidCenter

open LocalizedRuleMajorReference DeclarativeCIP

/-- **Inverse sign law at one rigid center from matched actual generated labels.**  Let `t` be a
carrier occurrence with a constitutionally strict actual frame, calibrated general-rigid center
and calibrated image center under one molecular automorphism `e`.  If the actual generated
uppercase label at `transportOccurrence e t` is the label at `t`, reflected when `mirror` holds,
then `e` satisfies the physical branch sign law at the center.  The two labels are read from
`referenceState_eq_chiral_of_calibrated`, and the contextual priority and frame parity covariance
of the two actual frames enter the scalar decoder.  No sign law is assumed. -/
theorem signLaw_of_matchedGeneratedLabels
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (e : input.certified.moleculeGraph.Aut)
    {target : LocalizedRuleMajorReference.Occurrence input}
    {unit : DetectedOccurrence input.certified.moleculeGraph}
    {targetUnit : input.certified.molecularFrameUnit target.1 = unit.1}
    (frames : ContextFrameCompilation input target unit targetUnit)
    {imageUnit : DetectedOccurrence input.certified.moleculeGraph}
    {imageTargetUnit : input.certified.molecularFrameUnit
      (input.certified.transportOccurrence singleBonded e target).1 = imageUnit.1}
    (imageFrames : ContextFrameCompilation input
      (input.certified.transportOccurrence singleBonded e target) imageUnit imageTargetUnit)
    (strict : LocalizedCyclicGeneralRigidPriority.FrameConstitutionalStrict frames.frame)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration) (mirror : Bool)
    (sourceCalibrated : ActualPhysicalGeneralRigidCalibratedCenter input.certified
      input.certified.detectedMultiCenterMolecule cfg frames.center)
    (imageCalibrated : ActualPhysicalGeneralRigidCalibratedCenter input.certified
      input.certified.detectedMultiCenterMolecule cfg
        (input.certified.physicalImageCenter e frames.center))
    (labels : ∀ raw : RS, referenceState input target = some (.chiral raw) →
      referenceState input (input.certified.transportOccurrence singleBonded e target) =
        some (.chiral (if mirror then RS.swap raw else raw))) :
    input.certified.detectedMultiCenterMolecule.configurationSign cfg
        (input.certified.physicalSourceCenter frames.center) *
      permHandedness (input.certified.detectedMultiCenterMolecule.ligandPermAt
        (input.certified.physicalDetectedAut e)
        (input.certified.physicalSourceCenter frames.center)) =
    physicalMirrorFactor mirror *
      input.certified.detectedMultiCenterMolecule.configurationSign cfg
        (input.certified.detectedMultiCenterMolecule.centerPerm
          (input.certified.physicalDetectedAut e)
          (input.certified.physicalSourceCenter frames.center)) := by
  have imageCalibrated' : ActualPhysicalGeneralRigidCalibratedCenter input.certified
      input.certified.detectedMultiCenterMolecule cfg imageFrames.center := by
    rw [image_center singleBonded e frames imageFrames]
    exact imageCalibrated
  have source := LocalizedCyclicGeneralRigidGeneratedLabels.referenceState_eq_chiral_of_calibrated
    frames strict singleBonded cfg sourceCalibrated
  have image := LocalizedCyclicGeneralRigidGeneratedLabels.referenceState_eq_chiral_of_calibrated
    imageFrames (image_strict singleBonded e frames imageFrames strict) singleBonded cfg
    imageCalibrated'
  have matched := labels _ source
  rw [image] at matched
  have letters := Option.some.inj matched
  injection letters with letters
  rw [image_priorityOrder singleBonded e frames imageFrames strict, permHandedness_mul]
    at letters
  have imageProduct :
      input.certified.detectedMultiCenterMolecule.configurationSign cfg imageFrames.center *
          permHandedness imageFrames.detectedLigandPermutation *
          (permHandedness (slotTransport singleBonded e frames).slotPerm *
            permHandedness (LocalizedCyclicGeneralRigidGeneratedLabels.priorityOrder frames strict
              singleBonded)) =
        input.certified.detectedMultiCenterMolecule.configurationSign cfg imageFrames.center *
          permHandedness (input.certified.framePerm e frames.center.1
            (input.certified.sourceTetra frames.center)) *
          (permHandedness frames.detectedLigandPermutation *
            permHandedness (LocalizedCyclicGeneralRigidGeneratedLabels.priorityOrder frames strict
              singleBonded)) := by
    calc _ = input.certified.detectedMultiCenterMolecule.configurationSign cfg imageFrames.center *
            (permHandedness imageFrames.detectedLigandPermutation *
              permHandedness (slotTransport singleBonded e frames).slotPerm) *
            permHandedness (LocalizedCyclicGeneralRigidGeneratedLabels.priorityOrder frames strict
              singleBonded) := by ring
      _ = _ := by
          rw [image_detectedLigandPermutation_handedness singleBonded e frames imageFrames]
          ring
  have sourceProduct :
      input.certified.detectedMultiCenterMolecule.configurationSign cfg frames.center *
          permHandedness frames.detectedLigandPermutation *
          permHandedness (LocalizedCyclicGeneralRigidGeneratedLabels.priorityOrder frames strict
            singleBonded) =
        input.certified.detectedMultiCenterMolecule.configurationSign cfg frames.center *
          (permHandedness frames.detectedLigandPermutation *
            permHandedness (LocalizedCyclicGeneralRigidGeneratedLabels.priorityOrder frames strict
              singleBonded)) := by ring
  rw [imageProduct, sourceProduct] at letters
  have commonUnit : permHandedness frames.detectedLigandPermutation *
        permHandedness (LocalizedCyclicGeneralRigidGeneratedLabels.priorityOrder frames strict
          singleBonded) = 1 ∨
      permHandedness frames.detectedLigandPermutation *
        permHandedness (LocalizedCyclicGeneralRigidGeneratedLabels.priorityOrder frames strict
          singleBonded) = -1 := by
    rw [← permHandedness_mul]
    exact permHandedness_eq_one_or_eq_neg_one _
  have decoded := matchedUppercaseLabels_decode_physicalSign
    (input.certified.detectedMultiCenterMolecule.configurationSign cfg frames.center)
    (input.certified.detectedMultiCenterMolecule.configurationSign cfg imageFrames.center)
    (permHandedness (input.certified.framePerm e frames.center.1
      (input.certified.sourceTetra frames.center)))
    (permHandedness frames.detectedLigandPermutation *
      permHandedness (LocalizedCyclicGeneralRigidGeneratedLabels.priorityOrder frames strict
        singleBonded)) mirror
    (permHandedness_eq_one_or_eq_neg_one (cfg frames.center))
    (permHandedness_eq_one_or_eq_neg_one (cfg imageFrames.center))
    (permHandedness_eq_one_or_eq_neg_one _) commonUnit letters
  rw [input.certified.framePerm_eq_ligandPermAt e frames.center,
    image_center singleBonded e frames imageFrames] at decoded
  exact decoded

end RigidCenter

/-! ## The physical inverse at an actual root -/

section RootFacade

open LocalizedRuleMajorReference DeclarativeCIP
open LocalizedActualOutwardRule1bEquivalence
open LocalizedCyclicMatchedReadingDecode

variable {input : LocalizedRuleMajorReference.Input}
  {target : LocalizedRuleMajorReference.Occurrence input}
  {unit : DetectedOccurrence input.certified.moleculeGraph}
  {targetUnit : input.certified.molecularFrameUnit target.1 = unit.1}

/-- At the empty address the actual frame slots are outward siblings; the pair's cursors are
literally the frame cursors. -/
noncomputable def rootFramePair (frames : ContextFrameCompilation input target unit targetUnit)
    (rootAddress : target.1.address = []) (i j : Fin 4) :
    ActualOutwardSiblingPair input.certified (LocalizedUniversalReference.carrierFuel input) where
  target := { occurrence := target, previous? := none }
  left := frames.frame.cursorAt i
  right := frames.frame.cursorAt j
  leftPrevious :=
    input.certified.executableLocalizedRerootChildren_previous _ _ (frames.childAt i)
  rightPrevious :=
    input.certified.executableLocalizedRerootChildren_previous _ _ (frames.childAt j)
  leftRoot := input.certified.localizedRerootChildren_root_eq _ _ _
    (input.certified.executableLocalizedRerootChildren_declarative _) (frames.childAt i)
  rightRoot := input.certified.localizedRerootChildren_root_eq _ _ _
    (input.certified.executableLocalizedRerootChildren_declarative _) (frames.childAt j)
  leftSlot := Classical.choose
    (input.certified.localizedOccurrenceFourLigandFrame_root_all_outward target frames.frame
      (LocalizedCyclicGeneralRigidGeneratedLabels.frame_computed frames) rootAddress i).2
  rightSlot := Classical.choose
    (input.certified.localizedOccurrenceFourLigandFrame_root_all_outward target frames.frame
      (LocalizedCyclicGeneralRigidGeneratedLabels.frame_computed frames) rootAddress j).2
  leftAddress := Classical.choose_spec
    (input.certified.localizedOccurrenceFourLigandFrame_root_all_outward target frames.frame
      (LocalizedCyclicGeneralRigidGeneratedLabels.frame_computed frames) rootAddress i).2
  rightAddress := Classical.choose_spec
    (input.certified.localizedOccurrenceFourLigandFrame_root_all_outward target frames.frame
      (LocalizedCyclicGeneralRigidGeneratedLabels.frame_computed frames) rootAddress j).2

/-- The root target's current atom, history and stored root are the compiled center. -/
theorem rootFrame_target_facts (frames : ContextFrameCompilation input target unit targetUnit)
    (rootAddress : target.1.address = [])
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom) :
    target.1.node.current? = some frames.center.1 ∧
      target.1.node.history = [frames.center.1] ∧ target.1.root = frames.center.1 := by
  have current := ((input.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff target
    frames.center).mp frames.centerComputed).2
  obtain ⟨history, root⟩ := rootOccurrence_history input.certified target real rootAddress current
  exact ⟨current, history, root⟩

/-- Each root frame slot is a real occurrence of its detected ligand directly below the root. -/
theorem rootFrame_cursor_facts (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (frames : ContextFrameCompilation input target unit targetUnit)
    (rootAddress : target.1.address = [])
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom) (k : Fin 4) :
    (frames.frame.cursorAt k).occurrence.1.node.provenance =
        OfficialCIPNodeProvenance.realAtom ∧
      (frames.frame.cursorAt k).occurrence.1.root = frames.center.1 ∧
      (frames.frame.cursorAt k).occurrence.1.node.history =
        [input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
          (frames.detectedLigandPermutation k), frames.center.1] := by
  obtain ⟨current, history, root⟩ := rootFrame_target_facts frames rootAddress real
  have mem : (frames.frame.cursorAt k).occurrence.1.node ∈
      input.certified.executableOfficialCIPChildren target.1.node :=
    LocalizedActualBoundaryObservationReadback.outwardChild_node_mem input.certified
      (rootFramePair frames rootAddress k k).target (rootFramePair frames rootAddress k k).left
      (rootFramePair frames rootAddress k k).leftRoot
      (rootFramePair frames rootAddress k k).leftSlot
      (rootFramePair frames rootAddress k k).leftAddress
  obtain ⟨atom, nodeEq, adjacent, _⟩ := (mem_executableOfficialCIPChildren_iff input.certified
    singleBonded target.1.node current real _).mp mem
  have atomFresh : atom ∉ target.1.node.history := by
    rw [history, List.mem_singleton]
    exact (ne_of_adj _ adjacent).symm
  have atomEq : atom = input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
      (frames.detectedLigandPermutation k) := by
    have ligand := frames.ligandAt k
    rw [nodeEq, OfficialCIPNode.extend_current?] at ligand
    exact Option.some.inj ligand
  refine ⟨?_, ?_, ?_⟩
  · rw [nodeEq, OfficialCIPNode.extend_provenance,
      OfficialCIPNode.childProvenance_real _ _ atomFresh]
  · exact (rootFramePair frames rootAddress k k).leftRoot.trans root
  · rw [nodeEq, OfficialCIPNode.extend_history, history, atomEq]

/-- **Branch transport from a label correspondence on two tied current root arms.**  Let two
actual current arms at frame slots `i ≠ j` of a real root occurrence, read with the target's actual
context reader, tie constitutionally, and carry matched uppercase labels at every common address
(reflected when `mirror` holds).  In the general-rigid physical domain at the root, with constant
formal charge on a simple-bonded input, the molecular automorphism reconstructed from these very
arm trees, repaired at terminal twins, is a physical branch transport from `α i` to `α j`. -/
theorem branchTransport_of_rootArmCorrespondence
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph)
    (frames : ContextFrameCompilation input target unit targetUnit)
    (rootAddress : target.1.address = [])
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    {i j : Fin 4} (distinct : i ≠ j)
    {stageL stageR : LocalizedCumulativeRule45Stage}
    (armL : input.certified.RuleMajorContextArm (LocalizedUniversalReference.carrierFuel input)
      stageL (contextOccurrenceRead input target) (frames.frame.cursorAt i))
    (armR : input.certified.RuleMajorContextArm (LocalizedUniversalReference.carrierFuel input)
      stageR (contextOccurrenceRead input target) (frames.frame.cursorAt j))
    (tie : OfficialRuleMajorKey.compare armL.key.constitutional armR.key.constitutional =
      Ordering.eq)
    (mirror : Bool)
    (correspondence : UppercaseCorrespondence armL.tree armR.tree mirror)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg frames.center) :
    BranchTransport input.certified.detectedMultiCenterMolecule cfg frames.center
      (frames.detectedLigandPermutation i) (frames.detectedLigandPermutation j) mirror := by
  obtain ⟨rootCurrent, rootHistory, rootRoot⟩ := rootFrame_target_facts frames rootAddress real
  obtain ⟨realI, rootI, historyI⟩ :=
    rootFrame_cursor_facts singleBonded frames rootAddress real i
  obtain ⟨realJ, _rootJ, _historyJ⟩ :=
    rootFrame_cursor_facts singleBonded frames rootAddress real j
  have rootBoundary :
      (rootFramePair frames rootAddress i j).target.occurrence.1.node.history.reverse =
        [frames.center.1] := by
    show target.1.node.history.reverse = [frames.center.1]
    rw [rootHistory]
    rfl
  obtain ⟨π, hπ, πRoot, a, b, ha, hb, πab, witness⟩ :=
    LocalizedCyclicWitnessedPhysicalTransport.currentRootArm_witnessedAutomorphism
      input.certified singleBonded charge (rootFramePair frames rootAddress i j) frames.center.1
      rootBoundary rootCurrent real realI realJ armL armR tie
  let e : input.certified.moleculeGraph.Aut := ⟨π, hπ⟩
  let E := input.certified.physicalDetectedAut e
  have aEq : a = input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
      (frames.detectedLigandPermutation i) :=
    Option.some.inj (ha.symm.trans (frames.ligandAt i))
  have bEq : b = input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
      (frames.detectedLigandPermutation j) :=
    Option.some.inj (hb.symm.trans (frames.ligandAt j))
  have rootFixed : input.certified.detectedMultiCenterMolecule.centerPerm E frames.center =
      frames.center := Subtype.ext πRoot
  have ligandSent : input.certified.detectedMultiCenterMolecule.ligandPermAt E frames.center
      (frames.detectedLigandPermutation i) = frames.detectedLigandPermutation j := by
    apply input.certified.detectedMultiCenterMolecule.ligandAtomAt_injective frames.center
    have transported := input.certified.detectedMultiCenterMolecule.ligandAtomAt_ligandPermAt E
      frames.center (frames.detectedLigandPermutation i)
    rw [rootFixed] at transported
    rw [transported, ← aEq, ← bEq]
    exact πab
  -- The actual Rule-1a tie of the two root arms, in the older builder's form.
  have validI := input.certified.frameCursor_valid target frames.frame
    (LocalizedCyclicGeneralRigidGeneratedLabels.frame_computed frames) i
  have validJ := input.certified.frameCursor_valid target frames.frame
    (LocalizedCyclicGeneralRigidGeneratedLabels.frame_computed frames) j
  obtain ⟨key4aL, built4aL⟩ := input.certified.exists_buildRuleMajorCumulativeWithRead_at_twice
    .rule4a (contextOccurrenceRead input target) (frames.frame.cursorAt i) validI
  obtain ⟨key4aR, built4aR⟩ := input.certified.exists_buildRuleMajorCumulativeWithRead_at_twice
    .rule4a (contextOccurrenceRead input target) (frames.frame.cursorAt j) validJ
  have oldL := (input.certified.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized
    (contextOccurrenceRead input target) _ _).symm.trans built4aL
  have oldR := (input.certified.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized
    (contextOccurrenceRead input target) _ _).symm.trans built4aR
  have constitutionalTie :
      OfficialRuleMajorKey.compare key4aL.constitutional key4aR.constitutional =
        Ordering.eq := by
    rw [← RetainedConstitutionalReaderIndependence.ruleMajorBuild_constitutional_compare_congr
      stageL stageR .rule4a .rule4a (contextOccurrenceRead input target)
      (contextOccurrenceRead input target) (contextOccurrenceRead input target)
      (contextOccurrenceRead input target) (frames.frame.cursorAt i) (frames.frame.cursorAt j)
      armL.built armR.built built4aL built4aR]
    exact tie
  have rule1aTie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      key4aL.constitutional.rule1a key4aR.constitutional.rule1a = Ordering.eq :=
    (compareSparseLayers_compareNat_eq_iff _ _).mpr
      ((officialRuleMajorKey_compare_eq_iff _ _).mp constitutionalTie).1
  have armDistinct : (frames.frame.cursorAt i).occurrence ≠ (frames.frame.cursorAt j).occurrence := by
    intro same
    have currents := congrArg
      (fun occurrence : LocalizedRuleMajorReference.Occurrence input =>
        occurrence.1.node.current?) same
    simp only at currents
    rw [frames.ligandAt i, frames.ligandAt j] at currents
    exact distinct (frames.detectedLigandPermutation.injective
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt_injective frames.center
        (Option.some.inj currents)))
  -- The sign law at every reached center that is not a terminal twin.
  have signLaw : ∀ d : input.certified.detectedMultiCenterMolecule.Center,
      LigandBranchReaches input.certified.detectedMultiCenterMolecule frames.center
        (frames.detectedLigandPermutation i) d.1 →
      ¬ ActualPhysicalTerminalTwinCenter input.certified
        input.certified.detectedMultiCenterMolecule d →
      input.certified.detectedMultiCenterMolecule.configurationSign cfg d *
          permHandedness (input.certified.detectedMultiCenterMolecule.ligandPermAt E d) =
        (if mirror then -1 else 1) *
          input.certified.detectedMultiCenterMolecule.configurationSign cfg
            (input.certified.detectedMultiCenterMolecule.centerPerm E d) := by
    intro d reached notTwin
    have dNe : d ≠ frames.center := by
      intro same
      obtain ⟨walk, avoids⟩ := reached
      exact avoids ((congrArg Subtype.val same) ▸ walk.end_mem_support)
    have inComp := ligandBranchReaches_implies_inComponent
      input.certified.detectedMultiCenterMolecule frames.center
      (frames.detectedLigandPermutation i) d.1 reached
    rw [← aEq] at inComp
    have inComp' : InComponent input.certified.moleculeGraph
        (rootFramePair frames rootAddress i j).target.occurrence.1.node.history.reverse a d.1 := by
      rw [rootBoundary]
      exact inComp
    obtain ⟨path, address, leftNode, rightNode, terminal, leftAt, rightAt, leftWitness,
      rightWitness⟩ := witness d.1 inComp'
    have leftSource : leftNode.source.occurrence.1.node =
        boundaryNode [frames.center.1] path.1 :=
      leftWitness.trans (congrArg (fun boundary => boundaryNode boundary path.1) rootBoundary)
    have rightSource : rightNode.source.occurrence.1.node =
        boundaryNode [frames.center.1] (path.1.map π) :=
      rightWitness.trans
        (congrArg (fun boundary => boundaryNode boundary (path.1.map π)) rootBoundary)
    obtain ⟨leftRoot, leftLength⟩ :=
      boundaryOccurrence_facts input.certified leftNode.source.occurrence leftSource
    obtain ⟨rightRoot, rightLength⟩ :=
      boundaryOccurrence_facts input.certified rightNode.source.occurrence rightSource
    have pathHead := path.2.head
    obtain ⟨rest, pathCons⟩ : ∃ rest, path.1 = a :: rest := by
      cases hp : path.1 with
      | nil =>
          rw [hp] at pathHead
          simp at pathHead
      | cons first rest =>
          rw [hp] at pathHead
          simp only [List.head?_cons, Option.some.injEq] at pathHead
          exact ⟨rest, by rw [pathHead]⟩
    have leftReal : leftNode.source.occurrence.1.node.provenance =
        OfficialCIPNodeProvenance.realAtom := by
      rw [leftSource]
      rfl
    have leftCurrent : leftNode.source.occurrence.1.node.current? = some d.1 := by
      rw [leftSource, boundaryNode_current?, List.getLast?_eq_some_getLast path.2.nonempty]
      exact congrArg some terminal
    have transported : rightNode.source.occurrence =
        input.certified.transportOccurrence singleBonded e leftNode.source.occurrence :=
      boundaryHistory_eq_transportOccurrence input.certified singleBonded e frames.center.1 πRoot
        leftNode.source.occurrence rightNode.source.occurrence leftRoot leftSource rightSource
        rightRoot
    -- The two node labels are the actual generated states at the two occurrences.
    have dependencyL : input.certified.LocalizedDepthDependency leftNode.source.occurrence
        target := by
      refine ⟨leftRoot.trans rootRoot.symm, ?_⟩
      rw [rootAddress, leftLength, pathCons]
      simp
    have dependencyR : input.certified.LocalizedDepthDependency rightNode.source.occurrence
        target := by
      refine ⟨rightRoot.trans rootRoot.symm, ?_⟩
      rw [rootAddress, rightLength, List.length_map, pathCons]
      simp
    have labelL : leftNode.label = referenceState input leftNode.source.occurrence := by
      rw [arm_label_eq_read armL address leftNode leftAt]
      exact input.certified.localizedDependencyLabel_eq_state_of_dependency target
        (referenceState input) leftNode.source dependencyL
    have labelR : rightNode.label = referenceState input rightNode.source.occurrence := by
      rw [arm_label_eq_read armR address rightNode rightAt]
      exact input.certified.localizedDependencyLabel_eq_state_of_dependency target
        (referenceState input) rightNode.source dependencyR
    -- The actual frame at the witness occurrence.
    have headL : leftNode.source.occurrence.1.node.history.head? = some d.1 := by
      have facts := LocalizedActualBoundaryObservationReadback.occurrence_history_facts
        input.certified leftNode.source.occurrence leftReal
      rw [← facts.2]
      exact leftCurrent
    have unitAtomL := input.certified.molecularFrameUnit_atom_eq_current
      leftNode.source.occurrence.1 headL
      (input.certified.frameCarrierOccurrence_history_getLast_eq_root leftNode.source.occurrence)
    have detectedL : IsDetectedCenter input.certified.moleculeGraph
        (input.certified.molecularFrameUnit leftNode.source.occurrence.1).atom := by
      rw [unitAtomL]
      exact tetrahedralCenter_isDetected input.certified ⟨d.1, d.2⟩
    let unitL : DetectedOccurrence input.certified.moleculeGraph :=
      ⟨input.certified.molecularFrameUnit leftNode.source.occurrence.1, detectedL⟩
    let framesL := cyclicContextFrameCompilation input singleBonded leftNode.source.occurrence
      leftReal unitL rfl
    have centerMeaningL := (input.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff
      leftNode.source.occurrence framesL.center).mp framesL.centerComputed
    have centerEqL : input.certified.physicalSourceCenter framesL.center = d :=
      Subtype.ext (Option.some.inj (centerMeaningL.2.symm.trans leftCurrent))
    have calibratedL : ActualPhysicalGeneralRigidCalibratedCenter input.certified
        input.certified.detectedMultiCenterMolecule cfg framesL.center := by
      have rigid := (LocalizedCyclicGeneralRigidPriority.physicalGeneralRigid_of_domain
        input.certified cfg frames.center domain d dNe notTwin).1
      rw [← centerEqL] at rigid
      exact rigid
    have inside : input.certified.RootBranchContains (frames.frame.cursorAt i).occurrence
        leftNode.source.occurrence := by
      apply rootBranchContains_of_boundary input.certified singleBonded _ _ rootI
        (by rw [historyI, ← aEq]) leftRoot
      rw [leftSource, pathCons]
    have nonrootL : leftNode.source.occurrence.1.address ≠ [] := by
      intro empty
      have lengthZero := congrArg List.length empty
      rw [leftLength, pathCons] at lengthZero
      simp at lengthZero
    have strictL := LocalizedCyclicGeneralRigidPriority.frameConstitutionalStrict_of_rootArmRule1aTie_of_physicalRigid
      input.certified singleBonded charge { occurrence := target, previous? := none } rootAddress
      (frames.frame.cursorAt i) (frames.frame.cursorAt j) (frames.childAt i) (frames.childAt j)
      armDistinct realI realJ (contextOccurrenceRead input target)
      (contextOccurrenceRead input target) key4aL key4aR oldL oldR rule1aTie
      leftNode.source.occurrence leftReal inside framesL.frame
      (LocalizedCyclicGeneralRigidGeneratedLabels.frame_computed framesL) nonrootL cfg
      framesL.center centerMeaningL.2 calibratedL
    -- The actual frame at the transported occurrence, and its calibration.
    let imageFramesL := cyclicContextFrameCompilation input singleBonded
      (input.certified.transportOccurrence singleBonded e leftNode.source.occurrence)
      (transportOccurrence_real input singleBonded e leftNode.source.occurrence leftReal)
      (input.certified.transportDetectedOccurrence e unitL)
      (transportOccurrence_unit input singleBonded e leftNode.source.occurrence unitL rfl)
    have imageNe : input.certified.detectedMultiCenterMolecule.centerPerm E d ≠ frames.center := by
      intro same
      apply dNe
      apply (input.certified.detectedMultiCenterMolecule.centerPerm E).injective
      rw [same, rootFixed]
    have imageNotTwin : ¬ ActualPhysicalTerminalTwinCenter input.certified
        input.certified.detectedMultiCenterMolecule
        (input.certified.detectedMultiCenterMolecule.centerPerm E d) := fun twin =>
      notTwin ((LocalizedCyclicPhysicalTerminalTwinTransport.actualPhysicalTerminalTwinCenter_transport_iff
        E d).mp twin)
    have imageCalibratedL : ActualPhysicalGeneralRigidCalibratedCenter input.certified
        input.certified.detectedMultiCenterMolecule cfg
          (input.certified.physicalImageCenter e framesL.center) := by
      have rigid := (LocalizedCyclicGeneralRigidPriority.physicalGeneralRigid_of_domain
        input.certified cfg frames.center domain _ imageNe imageNotTwin).1
      unfold CertifiedLocalizedCIPInput.physicalImageCenter
      rw [centerEqL]
      exact rigid
    have labelsL : ∀ raw : RS, referenceState input leftNode.source.occurrence =
          some (.chiral raw) →
        referenceState input
            (input.certified.transportOccurrence singleBonded e leftNode.source.occurrence) =
          some (.chiral (if mirror then RS.swap raw else raw)) := by
      intro raw sourceLabel
      rw [← transported, ← labelR]
      exact correspondence address leftNode rightNode leftAt rightAt raw
        (labelL.trans sourceLabel)
    have law := signLaw_of_matchedGeneratedLabels input singleBonded e framesL imageFramesL
      strictL cfg mirror calibratedL imageCalibratedL labelsL
    rw [centerEqL] at law
    exact law
  exact branchTransport_of_nonTwinSignLaw cfg frames.center
    (frames.detectedLigandPermutation i) (frames.detectedLigandPermutation j) mirror E rootFixed
    ligandSent signLaw

/-- The constitutional tie of two actual current arms at two root slots, at any stages, is the
Rule-4a tie of the two compiled compounds. -/
theorem armTie_of_rule4aTie (frames : ContextFrameCompilation input target unit targetUnit)
    {i j : Fin 4} {stageL stageR : LocalizedCumulativeRule45Stage}
    (armL : input.certified.RuleMajorContextArm (LocalizedUniversalReference.carrierFuel input)
      stageL (contextOccurrenceRead input target) (frames.frame.cursorAt i))
    (armR : input.certified.RuleMajorContextArm (LocalizedUniversalReference.carrierFuel input)
      stageR (contextOccurrenceRead input target) (frames.frame.cursorAt j))
    (rule4aTie : input.certified.compareLocalizedRerootCumulativeRule45Keys
      (frames.compounds i).prior.rule4aKey (frames.compounds j).prior.rule4aKey =
        Ordering.eq) :
    OfficialRuleMajorKey.compare armL.key.constitutional armR.key.constitutional =
      Ordering.eq := by
  rw [RetainedConstitutionalReaderIndependence.ruleMajorBuild_constitutional_compare_congr
    stageL stageR .rule4a .rule4a (contextOccurrenceRead input target)
    (contextOccurrenceRead input target) (contextOccurrenceRead input target)
    (contextOccurrenceRead input target) (frames.frame.cursorAt i) (frames.frame.cursorAt j)
    armL.built armR.built (compound_rule4a_built frames i) (compound_rule4a_built frames j)]
  exact (officialRuleMajorKey_compare_eq_iff _ _).mpr
    (cumulativeRule45Tie_constitutional_columns input.certified _ _ rule4aTie)

/-- An actual current arm at a root slot exists at every stage. -/
theorem nonempty_rootArm (frames : ContextFrameCompilation input target unit targetUnit)
    (stage : LocalizedCumulativeRule45Stage) (k : Fin 4) :
    Nonempty (input.certified.RuleMajorContextArm (LocalizedUniversalReference.carrierFuel input)
      stage (contextOccurrenceRead input target) (frames.frame.cursorAt k)) :=
  input.certified.exists_ruleMajorContextArm (LocalizedUniversalReference.carrierFuel input) stage
    (contextOccurrenceRead input target) (frames.frame.cursorAt k)
    (input.certified.frameCursor_valid target frames.frame
      (LocalizedCyclicGeneralRigidGeneratedLabels.frame_computed frames) k)

/-- **Actual matched common-`R` readings imply a proper physical transport.**  Let the compiled
compounds at two distinct root slots tie at Rule 4a, and let one Rule-5 reading of each, with
arbitrary own references, have equal actual common-`R` descriptor columns.  In the general-rigid
physical domain at the root, the two root branches are related by a proper transport. -/
theorem properTransport_of_matchedCommonR
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph)
    (frames : ContextFrameCompilation input target unit targetUnit)
    (rootAddress : target.1.address = [])
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    {i j : Fin 4} (distinct : i ≠ j)
    (rule4aTie : input.certified.compareLocalizedRerootCumulativeRule45Keys
      (frames.compounds i).prior.rule4aKey (frames.compounds j).prior.rule4aKey =
        Ordering.eq)
    {left right : input.certified.LocalizedRerootRule5Reading}
    (leftMember : left ∈ (frames.compounds i).rule5Readings)
    (rightMember : right ∈ (frames.compounds j).rule5Readings)
    (commonR : left.commonR.descriptor = right.commonR.descriptor)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg frames.center) :
    ProperTransport input.certified.detectedMultiCenterMolecule cfg frames.center
      (frames.detectedLigandPermutation i) (frames.detectedLigandPermutation j) := by
  obtain ⟨armL⟩ := nonempty_rootArm frames (localizedRule5StageFor left.prior.reference? .R) i
  obtain ⟨armR⟩ := nonempty_rootArm frames (localizedRule5StageFor right.prior.reference? .R) j
  have keyL := arm_key_eq_of_built armL (compound_commonR_built frames i leftMember)
  have keyR := arm_key_eq_of_built armR (compound_commonR_built frames j rightMember)
  have descriptors : armL.key.descriptor = armR.key.descriptor := by
    rw [keyL, keyR]
    exact commonR
  exact branchTransport_of_rootArmCorrespondence singleBonded charge frames rootAddress real
    distinct armL armR (armTie_of_rule4aTie frames armL armR rule4aTie) false
    (uppercaseCorrespondence_of_commonReading armL armR descriptors) cfg domain

/-- **Matched relative readings under opposite own references imply a mirror transport.**  Let
the compiled compounds at two distinct root slots tie at Rule 4a, and let one prior reading of
each, with opposite uppercase own references, have equal actual Rule-4b descriptor columns.  In
the general-rigid physical domain at the root, the two root branches are related by a mirror
transport. -/
theorem mirrorTransport_of_oppositeRule4b
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph)
    (frames : ContextFrameCompilation input target unit targetUnit)
    (rootAddress : target.1.address = [])
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    {i j : Fin 4} (distinct : i ≠ j)
    (rule4aTie : input.certified.compareLocalizedRerootCumulativeRule45Keys
      (frames.compounds i).prior.rule4aKey (frames.compounds j).prior.rule4aKey =
        Ordering.eq)
    {left right : input.certified.LocalizedRerootRule4bcReading}
    (leftMember : left ∈ (frames.compounds i).prior.readings)
    (rightMember : right ∈ (frames.compounds j).prior.readings)
    {reference : RS} (leftReference : left.reference? = some reference)
    (rightReference : right.reference? = some (RS.swap reference))
    (rule4b : left.rule4bKey.descriptor = right.rule4bKey.descriptor)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg frames.center) :
    MirrorTransport input.certified.detectedMultiCenterMolecule cfg frames.center
      (frames.detectedLigandPermutation i) (frames.detectedLigandPermutation j) := by
  obtain ⟨armL⟩ := nonempty_rootArm frames (.rule4b reference) i
  obtain ⟨armR⟩ := nonempty_rootArm frames (.rule4b (RS.swap reference)) j
  have keyL := arm_key_eq_of_built armL (compound_rule4b_built frames i leftMember leftReference)
  have keyR := arm_key_eq_of_built armR
    (compound_rule4b_built frames j rightMember rightReference)
  have descriptors : armL.key.descriptor = armR.key.descriptor := by
    rw [keyL, keyR]
    exact rule4b
  exact branchTransport_of_rootArmCorrespondence singleBonded charge frames rootAddress real
    distinct armL armR (armTie_of_rule4aTie frames armL armR rule4aTie) true
    (uppercaseCorrespondence_of_oppositeRule4b armL armR descriptors) cfg domain

/-- **Matched relative readings under one own reference imply a proper transport.** -/
theorem properTransport_of_sameRule4b
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph)
    (frames : ContextFrameCompilation input target unit targetUnit)
    (rootAddress : target.1.address = [])
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    {i j : Fin 4} (distinct : i ≠ j)
    (rule4aTie : input.certified.compareLocalizedRerootCumulativeRule45Keys
      (frames.compounds i).prior.rule4aKey (frames.compounds j).prior.rule4aKey =
        Ordering.eq)
    {left right : input.certified.LocalizedRerootRule4bcReading}
    (leftMember : left ∈ (frames.compounds i).prior.readings)
    (rightMember : right ∈ (frames.compounds j).prior.readings)
    {reference : RS} (leftReference : left.reference? = some reference)
    (rightReference : right.reference? = some reference)
    (rule4b : left.rule4bKey.descriptor = right.rule4bKey.descriptor)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg frames.center) :
    ProperTransport input.certified.detectedMultiCenterMolecule cfg frames.center
      (frames.detectedLigandPermutation i) (frames.detectedLigandPermutation j) := by
  obtain ⟨armL⟩ := nonempty_rootArm frames (.rule4b reference) i
  obtain ⟨armR⟩ := nonempty_rootArm frames (.rule4b reference) j
  have keyL := arm_key_eq_of_built armL (compound_rule4b_built frames i leftMember leftReference)
  have keyR := arm_key_eq_of_built armR
    (compound_rule4b_built frames j rightMember rightReference)
  have descriptors : armL.key.descriptor = armR.key.descriptor := by
    rw [keyL, keyR]
    exact rule4b
  exact branchTransport_of_rootArmCorrespondence singleBonded charge frames rootAddress real
    distinct armL armR (armTie_of_rule4aTie frames armL armR rule4aTie) false
    (uppercaseCorrespondence_of_sameRule4b armL armR descriptors) cfg domain

/-- **A full actual compound tie implies a proper physical transport.**  A tie of the actual
through-Rule-5 compound comparator between two distinct root slots contains the Rule-4a tie and a
matched head common-`R` reading. -/
theorem properTransport_of_fullTie
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph)
    (frames : ContextFrameCompilation input target unit targetUnit)
    (rootAddress : target.1.address = [])
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    {i j : Fin 4} (distinct : i ≠ j)
    (fullTie : input.certified.compareLocalizedRerootCompoundRule45Keys
      (frames.compounds i) (frames.compounds j) = Ordering.eq)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg frames.center) :
    ProperTransport input.certified.detectedMultiCenterMolecule cfg frames.center
      (frames.detectedLigandPermutation i) (frames.detectedLigandPermutation j) := by
  obtain ⟨priorTie, readingsTie⟩ :=
    fullTie_rule45Tie_prior_and_readings input.certified _ _ fullTie
  have rule4aTie :=
    ((input.certified.compareLocalizedRerootCompoundRule4bcKeys_eq_eq_iff _ _).mp priorTie).1
  obtain ⟨headL, tailL, eqL⟩ :=
    fullTie_list_exists_cons_of_ne_nil (compound_rule5Readings_ne_nil' frames i)
  obtain ⟨headR, tailR, eqR⟩ :=
    fullTie_list_exists_cons_of_ne_nil (compound_rule5Readings_ne_nil' frames j)
  have consTie : input.certified.compareLocalizedRerootCompoundRule5Readings .R
      (headL :: tailL) (headR :: tailR) = Ordering.eq := by
    rw [← eqL, ← eqR]
    exact readingsTie
  have heads := fullTie_compareRule5Readings_cons_cons_eq input.certified .R headL headR tailL
    tailR consTie
  have commonR : headL.commonR.descriptor = headR.commonR.descriptor := by
    simpa only [localizedRerootRule5Descriptor] using heads
  exact properTransport_of_matchedCommonR singleBonded charge frames rootAddress real distinct
    rule4aTie (by rw [eqL]; exact List.mem_cons_self) (by rw [eqR]; exact List.mem_cons_self)
    commonR cfg domain

/-- **Empty Rule-4b selection: both transports.**  If the compiled compound at slot `i` selects no
Rule-4b reference, its actual Rule-4a arm tree carries no uppercase label.  The label
correspondence is then empty, every rigid reached center would contradict it, and the
reconstructed automorphism repaired at the reached terminal twins is both a proper and a mirror
transport. -/
theorem transports_of_emptyReferences
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph)
    (frames : ContextFrameCompilation input target unit targetUnit)
    (rootAddress : target.1.address = [])
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    {i j : Fin 4} (distinct : i ≠ j)
    (rule4aTie : input.certified.compareLocalizedRerootCumulativeRule45Keys
      (frames.compounds i).prior.rule4aKey (frames.compounds j).prior.rule4aKey =
        Ordering.eq)
    (empty : localizedRule4bReferencesFromRankedLabels
      (frames.compounds i).prior.rule4aKey.rankedLabels = [])
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg frames.center) :
    ProperTransport input.certified.detectedMultiCenterMolecule cfg frames.center
        (frames.detectedLigandPermutation i) (frames.detectedLigandPermutation j) ∧
      MirrorTransport input.certified.detectedMultiCenterMolecule cfg frames.center
        (frames.detectedLigandPermutation i) (frames.detectedLigandPermutation j) := by
  obtain ⟨armL⟩ := nonempty_rootArm frames .rule4a i
  obtain ⟨armR⟩ := nonempty_rootArm frames .rule4a j
  have free := rule4aArm_uppercaseFree_of_references_nil frames i armL empty
  have tie := armTie_of_rule4aTie frames armL armR rule4aTie
  exact ⟨branchTransport_of_rootArmCorrespondence singleBonded charge frames rootAddress real
      distinct armL armR tie false (uppercaseCorrespondence_of_uppercaseFree free _ false) cfg
      domain,
    branchTransport_of_rootArmCorrespondence singleBonded charge frames rootAddress real
      distinct armL armR tie true (uppercaseCorrespondence_of_uppercaseFree free _ true) cfg
      domain⟩

/-- **An actual prior compound tie gives a physical transport.**  A tie of the actual compound
Rules-4b/4c comparator between two distinct root slots exposes the Rule-4a tie and a tied pair of
head relative readings.  Opposite own references give a mirror transport, one common own
reference gives a proper transport, and an empty selection gives both; a mixed pair cannot tie. -/
theorem mirror_or_proper_of_priorTie
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph)
    (frames : ContextFrameCompilation input target unit targetUnit)
    (rootAddress : target.1.address = [])
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    {i j : Fin 4} (distinct : i ≠ j)
    (priorTie : input.certified.compareLocalizedRerootCompoundRule4bcKeys
      (frames.compounds i).prior (frames.compounds j).prior = Ordering.eq)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg frames.center) :
    MirrorTransport input.certified.detectedMultiCenterMolecule cfg frames.center
        (frames.detectedLigandPermutation i) (frames.detectedLigandPermutation j) ∨
      ProperTransport input.certified.detectedMultiCenterMolecule cfg frames.center
        (frames.detectedLigandPermutation i) (frames.detectedLigandPermutation j) := by
  obtain ⟨rule4aTie, -, readingsTie, -⟩ :=
    (input.certified.compareLocalizedRerootCompoundRule4bcKeys_eq_eq_iff _ _).mp priorTie
  obtain ⟨left, tailL, eqL⟩ :=
    fullTie_list_exists_cons_of_ne_nil (compound_priorReadings_ne_nil' frames i)
  obtain ⟨right, tailR, eqR⟩ :=
    fullTie_list_exists_cons_of_ne_nil (compound_priorReadings_ne_nil' frames j)
  have leftMember : left ∈ (frames.compounds i).prior.readings := by
    rw [eqL]
    exact List.mem_cons_self
  have rightMember : right ∈ (frames.compounds j).prior.readings := by
    rw [eqR]
    exact List.mem_cons_self
  have headTie : left.rule4bKey.descriptor = right.rule4bKey.descriptor := by
    rw [eqL, eqR] at readingsTie
    simp only [compareLocalizedRerootCompoundRule4bReadings, List.compareLex_cons_cons,
      compareLocalizedRerootRule4bcReadingsByRule4b, Ordering.byKey,
      Ordering.then_eq_eq] at readingsTie
    exact (compareSparseLayers_compareLocalizedCumulativeRule45Priority_eq_iff _ _).mp
      readingsTie.1
  cases leftReference : left.reference? with
  | none =>
      exact Or.inl (transports_of_emptyReferences singleBonded charge frames rootAddress real
        distinct rule4aTie (compound_references_nil_of_reading frames i leftMember leftReference)
        cfg domain).2
  | some reference =>
      cases rightReference : right.reference? with
      | none =>
          exfalso
          obtain ⟨armL⟩ := nonempty_rootArm frames (.rule4b reference) i
          obtain ⟨armR⟩ := nonempty_rootArm frames .rule4a j
          have keyL := arm_key_eq_of_built armL
            (compound_rule4b_built frames i leftMember leftReference)
          have keyR := arm_key_eq_of_built armR
            (compound_rule4bNone_built frames j rightMember rightReference)
          exact rule4b_descriptor_ne_rule4a armL armR (by rw [keyL, keyR]; exact headTie)
      | some other =>
          by_cases same : other = reference
          · subst same
            exact Or.inr (properTransport_of_sameRule4b singleBonded charge frames rootAddress
              real distinct rule4aTie leftMember rightMember leftReference rightReference headTie
              cfg domain)
          · have opposite : other = RS.swap reference := by
              cases reference <;> cases other <;> first | exact absurd rfl same | rfl
            exact Or.inl (mirrorTransport_of_oppositeRule4b singleBonded charge frames rootAddress
              real distinct rule4aTie leftMember rightMember leftReference
              (rightReference.trans (congrArg some opposite)) headTie cfg domain)

/-- **Prior tie and proper distinguishability give a mirror transport.** -/
theorem mirrorTransport_of_priorTie_of_notProper
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph)
    (frames : ContextFrameCompilation input target unit targetUnit)
    (rootAddress : target.1.address = [])
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    {i j : Fin 4} (distinct : i ≠ j)
    (priorTie : input.certified.compareLocalizedRerootCompoundRule4bcKeys
      (frames.compounds i).prior (frames.compounds j).prior = Ordering.eq)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg frames.center)
    (notProper : ¬ ProperTransport input.certified.detectedMultiCenterMolecule cfg frames.center
      (frames.detectedLigandPermutation i) (frames.detectedLigandPermutation j)) :
    MirrorTransport input.certified.detectedMultiCenterMolecule cfg frames.center
      (frames.detectedLigandPermutation i) (frames.detectedLigandPermutation j) :=
  (mirror_or_proper_of_priorTie singleBonded charge frames rootAddress real distinct priorTie cfg
    domain).resolve_right notProper

/-- **Physical distinguishability separates the actual compiled compounds.**  If no two distinct
root ligand branches are related by a proper transport, then no two distinct compiled compounds
tie through Rule 5. -/
theorem compounds_fullComparison_ne_eq_of_properDistinct
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph)
    (frames : ContextFrameCompilation input target unit targetUnit)
    (rootAddress : target.1.address = [])
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg frames.center)
    (properDistinct : ∀ i j : Fin 4, i ≠ j →
      ¬ ProperTransport input.certified.detectedMultiCenterMolecule cfg frames.center
        (frames.detectedLigandPermutation i) (frames.detectedLigandPermutation j)) :
    ∀ i j : Fin 4, i ≠ j →
      input.certified.compareLocalizedRerootCompoundRule45Keys
        (frames.compounds i) (frames.compounds j) ≠ Ordering.eq := fun i j distinct fullTie =>
  properDistinct i j distinct (properTransport_of_fullTie singleBonded charge frames rootAddress
    real distinct fullTie cfg domain)

/-- **Prior compound ties are physically enantiomorphic.**  Under proper distinguishability, an
actual prior tie of two distinct compiled compounds is a physical enantiomorphic pair of the
corresponding detected ligand branches. -/
theorem enantiomorphic_of_priorTie
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph)
    (frames : ContextFrameCompilation input target unit targetUnit)
    (rootAddress : target.1.address = [])
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg frames.center)
    (properDistinct : ∀ i j : Fin 4, i ≠ j →
      ¬ ProperTransport input.certified.detectedMultiCenterMolecule cfg frames.center
        (frames.detectedLigandPermutation i) (frames.detectedLigandPermutation j))
    {i j : Fin 4} (distinct : i ≠ j)
    (priorTie : input.certified.compareLocalizedRerootCompoundRule4bcKeys
      (frames.compounds i).prior (frames.compounds j).prior = Ordering.eq) :
    Enantiomorphic input.certified.detectedMultiCenterMolecule cfg frames.center
      (frames.detectedLigandPermutation i) (frames.detectedLigandPermutation j) :=
  ⟨fun same => distinct (frames.detectedLigandPermutation.injective same),
    mirrorTransport_of_priorTie_of_notProper singleBonded charge frames rootAddress real distinct
      priorTie cfg domain (properDistinct i j distinct),
    properDistinct i j distinct⟩

end RootFacade

/-! ## The evaluator's own final root -/

section FinalRoot

open LocalizedRuleMajorReference DeclarativeCIP

/-- The actual compiled frame of the evaluator's own final root occurrence of a detected center. -/
noncomputable abbrev finalRootFrames (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (center : input.certified.TetrahedralCenter) :
    ContextFrameCompilation input
      (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center)
      (finalCenterUnit input center) (finalOccurrence_molecularFrameUnit input center) :=
  cyclicContextFrameCompilation input singleBonded
    (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center)
    (finalOccurrence_provenance_real input center) (finalCenterUnit input center)
    (finalOccurrence_molecularFrameUnit input center)

/-- The final root frame's compiled center is the reported center. -/
theorem finalRootFrames_center (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (center : input.certified.TetrahedralCenter) :
    (finalRootFrames input singleBonded center).center = center := by
  have computed := ((input.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff _
    (finalRootFrames input singleBonded center).center).mp
    (finalRootFrames input singleBonded center).centerComputed).2
  apply Subtype.ext
  have finalCurrent :
      (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center).1.node.current? =
        some center.1 := by
    simp [localizedFinalOccurrenceExecutable, localizedFinalRootFrame, OfficialCIPNode.root]
  exact Option.some.inj (computed.symm.trans finalCurrent)

/-- **Final-root proper transport from a full actual compound tie.**  At the evaluator's own final
root of a detected center, a full tie of the actual compiled compounds at two distinct slots gives
a proper physical transport between the corresponding detected ligand branches, in the
general-rigid physical domain at that center. -/
theorem finalRoot_properTransport_of_fullTie (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph)
    (center : input.certified.TetrahedralCenter) {i j : Fin 4} (distinct : i ≠ j)
    (fullTie : input.certified.compareLocalizedRerootCompoundRule45Keys
      ((finalRootFrames input singleBonded center).compounds i)
      ((finalRootFrames input singleBonded center).compounds j) = Ordering.eq)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg center) :
    ProperTransport input.certified.detectedMultiCenterMolecule cfg center
      ((finalRootFrames input singleBonded center).detectedLigandPermutation i)
      ((finalRootFrames input singleBonded center).detectedLigandPermutation j) := by
  have centerEq := finalRootFrames_center input singleBonded center
  have domain' : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg
      (finalRootFrames input singleBonded center).center := by
    rw [centerEq]
    exact domain
  have transport := properTransport_of_fullTie singleBonded charge
    (finalRootFrames input singleBonded center)
    (input.certified.localizedFinalOccurrenceExecutable_address (carrierFuel input) center)
    (finalOccurrence_provenance_real input center) distinct fullTie cfg domain'
  rw [centerEq] at transport
  exact transport

/-- **Final-root mirror transport from matched relative readings under opposite references.** -/
theorem finalRoot_mirrorTransport_of_oppositeRule4b (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph)
    (center : input.certified.TetrahedralCenter) {i j : Fin 4} (distinct : i ≠ j)
    (rule4aTie : input.certified.compareLocalizedRerootCumulativeRule45Keys
      ((finalRootFrames input singleBonded center).compounds i).prior.rule4aKey
      ((finalRootFrames input singleBonded center).compounds j).prior.rule4aKey = Ordering.eq)
    {left right : input.certified.LocalizedRerootRule4bcReading}
    (leftMember : left ∈ ((finalRootFrames input singleBonded center).compounds i).prior.readings)
    (rightMember : right ∈ ((finalRootFrames input singleBonded center).compounds j).prior.readings)
    {reference : RS} (leftReference : left.reference? = some reference)
    (rightReference : right.reference? = some (RS.swap reference))
    (rule4b : left.rule4bKey.descriptor = right.rule4bKey.descriptor)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg center) :
    MirrorTransport input.certified.detectedMultiCenterMolecule cfg center
      ((finalRootFrames input singleBonded center).detectedLigandPermutation i)
      ((finalRootFrames input singleBonded center).detectedLigandPermutation j) := by
  have centerEq := finalRootFrames_center input singleBonded center
  have domain' : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg
      (finalRootFrames input singleBonded center).center := by
    rw [centerEq]
    exact domain
  have transport := mirrorTransport_of_oppositeRule4b singleBonded charge
    (finalRootFrames input singleBonded center)
    (input.certified.localizedFinalOccurrenceExecutable_address (carrierFuel input) center)
    (finalOccurrence_provenance_real input center) distinct rule4aTie leftMember rightMember
    leftReference rightReference rule4b cfg domain'
  rw [centerEq] at transport
  exact transport

/-- **Final-root prior ties give a physical transport.** -/
theorem finalRoot_mirror_or_proper_of_priorTie (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph)
    (center : input.certified.TetrahedralCenter) {i j : Fin 4} (distinct : i ≠ j)
    (priorTie : input.certified.compareLocalizedRerootCompoundRule4bcKeys
      ((finalRootFrames input singleBonded center).compounds i).prior
      ((finalRootFrames input singleBonded center).compounds j).prior = Ordering.eq)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg center) :
    MirrorTransport input.certified.detectedMultiCenterMolecule cfg center
        ((finalRootFrames input singleBonded center).detectedLigandPermutation i)
        ((finalRootFrames input singleBonded center).detectedLigandPermutation j) ∨
      ProperTransport input.certified.detectedMultiCenterMolecule cfg center
        ((finalRootFrames input singleBonded center).detectedLigandPermutation i)
        ((finalRootFrames input singleBonded center).detectedLigandPermutation j) := by
  have centerEq := finalRootFrames_center input singleBonded center
  have domain' : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg
      (finalRootFrames input singleBonded center).center := by
    rw [centerEq]
    exact domain
  have transport := mirror_or_proper_of_priorTie singleBonded charge
    (finalRootFrames input singleBonded center)
    (input.certified.localizedFinalOccurrenceExecutable_address (carrierFuel input) center)
    (finalOccurrence_provenance_real input center) distinct priorTie cfg domain'
  rw [centerEq] at transport
  exact transport

/-- **Final-root enantiomorphism of prior ties and separation of full ties.**  At the evaluator's
own final root, under proper distinguishability of the detected ligand branches, distinct compiled
compounds never tie through Rule 5, and every prior tie is a physical enantiomorphic pair. -/
theorem finalRoot_physical_tie_classification (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph)
    (center : input.certified.TetrahedralCenter)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg center)
    (properDistinct : ∀ i j : Fin 4, i ≠ j →
      ¬ ProperTransport input.certified.detectedMultiCenterMolecule cfg center
        ((finalRootFrames input singleBonded center).detectedLigandPermutation i)
        ((finalRootFrames input singleBonded center).detectedLigandPermutation j)) :
    (∀ i j : Fin 4, i ≠ j →
      input.certified.compareLocalizedRerootCompoundRule45Keys
        ((finalRootFrames input singleBonded center).compounds i)
        ((finalRootFrames input singleBonded center).compounds j) ≠ Ordering.eq) ∧
    (∀ i j : Fin 4, i ≠ j →
      input.certified.compareLocalizedRerootCompoundRule4bcKeys
        ((finalRootFrames input singleBonded center).compounds i).prior
        ((finalRootFrames input singleBonded center).compounds j).prior = Ordering.eq →
      Enantiomorphic input.certified.detectedMultiCenterMolecule cfg center
        ((finalRootFrames input singleBonded center).detectedLigandPermutation i)
        ((finalRootFrames input singleBonded center).detectedLigandPermutation j)) := by
  have centerEq := finalRootFrames_center input singleBonded center
  have domain' : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg
      (finalRootFrames input singleBonded center).center := by
    rw [centerEq]
    exact domain
  have properDistinct' : ∀ i j : Fin 4, i ≠ j →
      ¬ ProperTransport input.certified.detectedMultiCenterMolecule cfg
        (finalRootFrames input singleBonded center).center
        ((finalRootFrames input singleBonded center).detectedLigandPermutation i)
        ((finalRootFrames input singleBonded center).detectedLigandPermutation j) := by
    rw [centerEq]
    exact properDistinct
  have rootAddress :=
    input.certified.localizedFinalOccurrenceExecutable_address (carrierFuel input) center
  refine ⟨compounds_fullComparison_ne_eq_of_properDistinct singleBonded charge
    (finalRootFrames input singleBonded center) rootAddress
    (finalOccurrence_provenance_real input center) cfg domain' properDistinct', ?_⟩
  intro i j distinct priorTie
  have pair := enantiomorphic_of_priorTie singleBonded charge
    (finalRootFrames input singleBonded center) rootAddress
    (finalOccurrence_provenance_real input center) cfg domain' properDistinct' distinct priorTie
  rw [centerEq] at pair
  exact pair

end FinalRoot

end
end LocalizedCyclicMatchedReadingPhysicalTransport
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport.inComponent_implies_ligandBranchReaches
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport.sameAddress_labelEq_implies_readEq
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport.boundaryHistory_eq_transportOccurrence
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport.matchedUppercaseLabels_decode_physicalSign
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport.ligandBranchReaches_implies_inComponent
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport.TwinCenter
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport.twinLeftLeaf
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport.twinRightLeaf
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport.twinCenterFamily
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport.branchTransport_of_nonTwinSignLaw
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport.rootOccurrence_history
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport.boundaryOccurrence_facts
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport.rootBranchContains_of_boundary
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport.arm_label_eq_read
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport.signLaw_of_matchedGeneratedLabels
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport.rootFramePair
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport.rootFrame_target_facts
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport.rootFrame_cursor_facts
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport.branchTransport_of_rootArmCorrespondence
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport.armTie_of_rule4aTie
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport.nonempty_rootArm
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport.properTransport_of_matchedCommonR
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport.mirrorTransport_of_oppositeRule4b
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport.properTransport_of_sameRule4b
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport.properTransport_of_fullTie
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport.finalRootFrames
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport.finalRootFrames_center
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport.finalRoot_properTransport_of_fullTie
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport.finalRoot_mirrorTransport_of_oppositeRule4b
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport.transports_of_emptyReferences
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport.mirror_or_proper_of_priorTie
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport.mirrorTransport_of_priorTie_of_notProper
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport.compounds_fullComparison_ne_eq_of_properDistinct
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport.enantiomorphic_of_priorTie
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport.finalRoot_mirror_or_proper_of_priorTie
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport.finalRoot_physical_tie_classification
