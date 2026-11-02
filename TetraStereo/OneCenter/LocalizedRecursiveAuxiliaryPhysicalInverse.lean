import TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0

/-!
# The inverse direction at a cyclic root: label-blind arms and hidden parity

The accepted classification decodes an actual prior tie of two root arms into a physical branch
transport by reading local signs off matched uppercase labels. Without auxiliary rigidity a
reached center may be refused (`none`) and still carry physical configuration information. This
module isolates that phenomenon in reader-free form.

* `reach_transport`: a root-fixing automorphism carrying root slot `i` to slot `j` carries every
  cursor reached from `i` to one reached from `j`.
* `referenceState_none_of_historyWitness`: at a real reached occurrence, an automorphism fixing
  its retained history pointwise, exchanging two fresh neighbours of the current atom and obeying
  the proper sign law on the residual component, forces the actual state `none`. This is a
  statement about the graph and the configuration only.
* `retainedKeys_eq_of_blindArms`, `referenceState_none_of_blindArms`: if every occurrence reached
  from two root slots exchanged by a root-fixing automorphism is refused, the two complete root
  keys are equal and the root refuses. **No sign law of the automorphism is used.**
* `not_branchTransport_of_parityCoupling`: if every root-fixing exchange of the two ligands acts
  with equal handedness at two reached centers, the product of their configuration signs is a
  physical invariant of branch transport, proper or mirror.

Together: refused auxiliary centers whose refusal witnesses act evenly can hide a parity that the
physical branch relation sees and the actual keys do not. The concrete counterexample is in
`LocalizedRecursiveAuxiliaryPhysicalCompletion`.
-/

namespace TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalInverse

open CertifiedLocalizedCIPInput LocalizedRuleMajorReference DeclarativeCIP
open DeclarativeCIP.RetainedOccurrenceCarrier DeclarativeCIP.RetainedCutArm
open DeclarativeCIP.RetainedCutAutomorphism
open LocalizedRecursiveAuxiliaryPhysicalDomain LocalizedRecursiveAuxiliaryPhysicalTransport
open LocalizedRecursiveAuxiliaryPhysicalCorrectness
open LocalizedCyclicMatchedReadingPhysicalTransport LocalizedCyclicRootArmReachability
open LocalizedCyclicPhysicalStageTransport LocalizedCyclicPhysicalMirrorPriorTie
open RootedTetrahedralBranchSymmetry
open scoped Classical

noncomputable section

section Root

variable {input : Input} {rootTarget : Occurrence input}
  {rootUnit : DetectedOccurrence input.certified.moleculeGraph}
  {rootTargetUnit : input.certified.molecularFrameUnit rootTarget.1 = rootUnit.1}

/-- The retained history of the root occurrence is fixed by an automorphism fixing the root. -/
theorem rootHistory_fixed
    (rootFrames : ContextFrameCompilation input rootTarget rootUnit rootTargetUnit)
    (rootAddress : rootTarget.1.address = [])
    (rootReal : rootTarget.1.node.provenance = .realAtom)
    (e : input.certified.moleculeGraph.Aut)
    (rootFixed : (e : Equiv.Perm input.certified.Atom) rootFrames.center.1 = rootFrames.center.1) :
    ∀ x ∈ rootTarget.1.node.history, (e : Equiv.Perm input.certified.Atom) x = x := by
  have history := (rootFrame_target_facts rootFrames rootAddress rootReal).2.1
  intro x member
  rw [history, List.mem_singleton] at member
  rw [member]
  exact rootFixed

/-- The root slot cursors are carried to each other. -/
theorem rootSlot_sent
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (rootFrames : ContextFrameCompilation input rootTarget rootUnit rootTargetUnit)
    (rootAddress : rootTarget.1.address = [])
    (rootReal : rootTarget.1.node.provenance = .realAtom)
    (e : input.certified.moleculeGraph.Aut) {i j : Fin 4}
    (rootFixed : (e : Equiv.Perm input.certified.Atom) rootFrames.center.1 = rootFrames.center.1)
    (ligandSent : (e : Equiv.Perm input.certified.Atom)
        (input.certified.detectedMultiCenterMolecule.ligandAtomAt rootFrames.center
          (rootFrames.detectedLigandPermutation i)) =
      input.certified.detectedMultiCenterMolecule.ligandAtomAt rootFrames.center
        (rootFrames.detectedLigandPermutation j)) :
    input.certified.transportCursor singleBonded e (rootFrames.frame.cursorAt i) =
      rootFrames.frame.cursorAt j := by
  have outwardI : IsLocalizedActualFrameOutwardCursor input.certified rootTarget
      (rootFrames.frame.cursorAt i) :=
    ⟨_, (rootFramePair rootFrames rootAddress i i).leftAddress⟩
  have outwardJ : IsLocalizedActualFrameOutwardCursor input.certified rootTarget
      (rootFrames.frame.cursorAt j) :=
    ⟨_, (rootFramePair rootFrames rootAddress j j).leftAddress⟩
  exact transportCursor_slot_of_history singleBonded rootFrames rootReal e outwardI outwardJ
    (rootHistory_fixed rootFrames rootAddress rootReal e rootFixed) ligandSent

/-- **Transport of reached cursors.** -/
theorem reach_transport
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (rootFrames : ContextFrameCompilation input rootTarget rootUnit rootTargetUnit)
    (e : input.certified.moleculeGraph.Aut) {i j : Fin 4}
    (sent : input.certified.transportCursor singleBonded e (rootFrames.frame.cursorAt i) =
      rootFrames.frame.cursorAt j)
    {z : Occurrence input} (reach : Reach rootFrames i z) :
    Reach rootFrames j (input.certified.transportOccurrence singleBonded e z) := by
  obtain ⟨cursor, cursorEq, reachable⟩ := reach
  have main : ∀ c, Relation.ReflTransGen (CertifiedLocalizedCIPInput.E input.certified)
      (rootFrames.frame.cursorAt i) c →
      (∃ parent, c ∈ input.certified.executableLocalizedRerootChildren parent) ∧
      Relation.ReflTransGen (CertifiedLocalizedCIPInput.E input.certified)
        (rootFrames.frame.cursorAt j) (input.certified.transportCursor singleBonded e c) := by
    intro c path
    induction path with
    | refl =>
        exact ⟨⟨{ occurrence := rootTarget, previous? := none }, rootFrames.childAt i⟩,
          sent ▸ Relation.ReflTransGen.refl⟩
    | @tail b c' _ edge ih =>
        obtain ⟨⟨parent, present⟩, reached⟩ := ih
        exact ⟨⟨b, edge⟩, reached.tail
          ((input.certified.executableLocalizedRerootChildren_transport_mem_iff_of_child
            singleBonded e parent b c' present).mp edge)⟩
  refine ⟨input.certified.transportCursor singleBonded e cursor, ?_, (main cursor reachable).2⟩
  rw [input.certified.transportCursor_occurrence, cursorEq]

/-- **Label-blind arms tie completely.** Let a root-fixing automorphism carry root ligand `α i`
to `α j`, and let every occurrence reached from either slot be refused. Then every read of the
arm of `i` is covariant without any sign law, and the two complete retained keys are equal. -/
theorem retainedKeys_eq_of_blindArms
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (rootFrames : ContextFrameCompilation input rootTarget rootUnit rootTargetUnit)
    (rootAddress : rootTarget.1.address = [])
    (rootReal : rootTarget.1.node.provenance = .realAtom)
    (e : input.certified.moleculeGraph.Aut) {i j : Fin 4}
    (rootFixed : (e : Equiv.Perm input.certified.Atom) rootFrames.center.1 = rootFrames.center.1)
    (ligandSent : (e : Equiv.Perm input.certified.Atom)
        (input.certified.detectedMultiCenterMolecule.ligandAtomAt rootFrames.center
          (rootFrames.detectedLigandPermutation i)) =
      input.certified.detectedMultiCenterMolecule.ligandAtomAt rootFrames.center
        (rootFrames.detectedLigandPermutation j))
    (blind : ∀ z, Reach rootFrames i z ∨ Reach rootFrames j z → referenceState input z = none) :
    rootFrames.retainedKeys i = rootFrames.retainedKeys j := by
  have sent := rootSlot_sent singleBonded rootFrames rootAddress rootReal e rootFixed ligandSent
  have fixed := transportOccurrence_fixed_of_history singleBonded e rootTarget
    (rootHistory_fixed rootFrames rootAddress rootReal e rootFixed)
  have armReads : ReadsAgree input.certified.moleculeGraph e (descriptorMap input)
      (mirroredMap input.certified.moleculeGraph false (descriptorMap input)) rootUnit
      (rootFrames.actualArmGraphs i) := by
    intro node steps occ _real ancestors context
    obtain ⟨source, sourceReach, sourceUnit⟩ :=
      actualArm_read_source singleBonded rootFrames i node steps occ ancestors context
    have reachI : Reach rootFrames i source.occurrence := ⟨source, rfl, sourceReach⟩
    have reachJ := reach_transport singleBonded rootFrames e sent reachI
    have law : Law singleBonded e false source.occurrence := by
      unfold Law
      rw [blind _ (Or.inl reachI), blind _ (Or.inr reachJ)]
      rfl
    exact covariant_of_law singleBonded e false source.occurrence occ sourceUnit law
  let iso : RootedDigraph.Iso (rootFrames.canonicalCutGraphs singleBonded i)
      (rootFrames.actualArmGraphs i) :=
    Classical.choice (rootFrames.canonicalLigandCut singleBonded i).faithful
  exact retainedKeys_eq_of_readsAgree singleBonded rootFrames e fixed sent
    (readsAgree_of_iso e (descriptorMap input)
      (mirroredMap input.certified.moleculeGraph false (descriptorMap input)) rootUnit iso.symm
      armReads)

/-- **Label-blind arms make the root refuse**, whatever the configuration. -/
theorem referenceState_none_of_blindArms
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (rootFrames : ContextFrameCompilation input rootTarget rootUnit rootTargetUnit)
    (rootAddress : rootTarget.1.address = [])
    (rootReal : rootTarget.1.node.provenance = .realAtom)
    (e : input.certified.moleculeGraph.Aut) {i j : Fin 4} (distinct : i ≠ j)
    (rootFixed : (e : Equiv.Perm input.certified.Atom) rootFrames.center.1 = rootFrames.center.1)
    (ligandSent : (e : Equiv.Perm input.certified.Atom)
        (input.certified.detectedMultiCenterMolecule.ligandAtomAt rootFrames.center
          (rootFrames.detectedLigandPermutation i)) =
      input.certified.detectedMultiCenterMolecule.ligandAtomAt rootFrames.center
        (rootFrames.detectedLigandPermutation j))
    (blind : ∀ z, Reach rootFrames i z ∨ Reach rootFrames j z → referenceState input z = none) :
    referenceState input rootTarget = none := by
  have equal := retainedKeys_eq_of_blindArms singleBonded rootFrames rootAddress rootReal e
    rootFixed ligandSent blind
  rw [rootFrames.referenceState_none_iff_no_retainedJudgment singleBonded]
  rintro ⟨descriptor, points, _available, judgment⟩
  exact distinct (completeRootDescriptorJudgment_injective judgment equal)

/-- **A reader-free refusal witness at a retained history.** An automorphism fixing every atom
of the history, exchanging two distinct fresh neighbours `s, t` of the current atom, and obeying
the proper sign law at every center of the residual component of `s`. -/
def HistoryRefusalWitness (input : Input)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (history : List input.certified.Atom) (current : input.certified.Atom) : Prop :=
  ∃ σ : input.certified.moleculeGraph.Aut, ∃ s t : input.certified.Atom,
    s ≠ t ∧ input.certified.moleculeGraph.Adj current s ∧
    input.certified.moleculeGraph.Adj current t ∧ s ∉ history ∧ t ∉ history ∧
    (∀ x ∈ history, (σ : Equiv.Perm input.certified.Atom) x = x) ∧
    (σ : Equiv.Perm input.certified.Atom) s = t ∧
    ∀ d : input.certified.detectedMultiCenterMolecule.Center,
      RetainedCoherentSymmetry.InComponent input.certified.moleculeGraph history s d.1 →
      input.certified.detectedMultiCenterMolecule.configurationSign cfg d *
          permHandedness (input.certified.detectedMultiCenterMolecule.ligandPermAt
            (input.certified.physicalDetectedAut σ) d) =
        input.certified.detectedMultiCenterMolecule.configurationSign cfg
          (input.certified.detectedMultiCenterMolecule.centerPerm
            (input.certified.physicalDetectedAut σ) d)

/-- A fresh neighbour of the current atom is the ligand of an outward slot of the actual frame. -/
theorem outwardSlot_of_fresh
    {target : Occurrence input} {unit : DetectedOccurrence input.certified.moleculeGraph}
    {targetUnit : input.certified.molecularFrameUnit target.1 = unit.1}
    (frames : ContextFrameCompilation input target unit targetUnit)
    (nonroot : target.1.address ≠ [])
    (s : input.certified.Atom) (adjacent : input.certified.moleculeGraph.Adj frames.center.1 s)
    (fresh : s ∉ target.1.node.history) :
    ∃ a : Fin 4, input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
        (frames.detectedLigandPermutation a) = s ∧
      IsLocalizedActualFrameOutwardCursor input.certified target (frames.frame.cursorAt a) := by
  obtain ⟨k, hk⟩ := input.certified.detectedMultiCenterMolecule.ligandAtomAt_surjective
    frames.center s adjacent
  refine ⟨frames.detectedLigandPermutation.symm k, by rw [Equiv.apply_symm_apply]; exact hk, ?_⟩
  obtain ⟨parentIndex, certificate, cursorEq, _parentClass, others⟩ :=
    input.certified.actualFrame_parentIndex target frames.frame
      (LocalizedCyclicGeneralRigidGeneratedLabels.frame_computed frames) nonroot
  apply (others _ _).1
  intro same
  apply fresh
  have ligand : certificate.parent.1.node.current? =
      some (input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
        (frames.detectedLigandPermutation parentIndex)) := by
    have atParent := frames.ligandAt parentIndex
    rw [cursorEq] at atParent
    exact atParent
  rw [← same, Equiv.apply_symm_apply, hk] at ligand
  have facts := LocalizedActualBoundaryObservationReadback.occurrence_history_facts
    input.certified certificate.parent certificate.parent_active.1
  rw [facts.2] at ligand
  rw [certificate.history_eq]
  exact List.mem_cons_of_mem _ (List.mem_of_mem_head? ligand)

/-- **Reader-free refusal.** At a real occurrence reached inside a root arm constitutionally
equivalent to another, a history refusal witness forces the actual state `none`. -/
theorem referenceState_none_of_historyWitness
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (rootFrames : ContextFrameCompilation input rootTarget rootUnit rootTargetUnit)
    (rootAddress : rootTarget.1.address = [])
    (rootReal : rootTarget.1.node.provenance = .realAtom)
    {i j : Fin 4} (distinct : i ≠ j) (e : input.certified.moleculeGraph.Aut)
    (rootArmFixed : (e : Equiv.Perm input.certified.Atom) rootFrames.center.1 = rootFrames.center.1)
    (rootArmSent : (e : Equiv.Perm input.certified.Atom)
        (input.certified.detectedMultiCenterMolecule.ligandAtomAt rootFrames.center
          (rootFrames.detectedLigandPermutation i)) =
      input.certified.detectedMultiCenterMolecule.ligandAtomAt rootFrames.center
        (rootFrames.detectedLigandPermutation j))
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : RecursiveAuxiliaryPhysicalDomain input.certified cfg rootFrames.center)
    (z : Occurrence input) (reach : Reach rootFrames i z)
    (real : z.1.node.provenance = .realAtom)
    (detected : IsDetectedCenter input.certified.moleculeGraph
      (input.certified.molecularFrameUnit z.1).atom)
    (witness : ∀ d : input.certified.Atom, z.1.node.current? = some d →
      HistoryRefusalWitness input cfg z.1.node.history d) :
    referenceState input z = none := by
  obtain ⟨cursor, cursorEq, reachable⟩ := reach
  obtain ⟨_previousData, _inside, nonroot, _rooted⟩ :=
    cursor_facts rootFrames rootAddress rootReal i cursor reachable
  rw [cursorEq] at nonroot
  let unit : DetectedOccurrence input.certified.moleculeGraph :=
    ⟨input.certified.molecularFrameUnit z.1, detected⟩
  let frames := cyclicContextFrameCompilation input singleBonded z real unit rfl
  have centerMeaning := (input.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff z
    frames.center).mp frames.centerComputed
  obtain ⟨σ, s, t, distinctST, adjS, adjT, freshS, freshT, historyFixed, sentST, law⟩ :=
    witness frames.center.1 centerMeaning.2
  obtain ⟨a, ligandA, outwardA⟩ := outwardSlot_of_fresh frames nonroot s adjS freshS
  obtain ⟨b, ligandB, outwardB⟩ := outwardSlot_of_fresh frames nonroot t adjT freshT
  have slotsDistinct : a ≠ b := by
    intro same
    apply distinctST
    rw [← ligandA, ← ligandB, same]
  have transport : AuxiliaryBranchTransport frames σ cfg a b false :=
    { historyFixed := historyFixed
      ligandSent := by rw [ligandA, ligandB]; exact sentST
      componentLaw := by
        intro d component
        rw [ligandA] at component
        rw [law d component]
        simp [physicalMirrorFactor] }
  exact auxiliary_referenceState_none_of_physicalProper singleBonded rootFrames rootAddress
    rootReal distinct e rootArmFixed rootArmSent cfg domain frames real cursor cursorEq reachable
    slotsDistinct outwardA outwardB σ transport

end Root

/-! ## The physical side: a parity invariant of branch transport -/

section Parity

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem permHandedness_mul_self (σ : Equiv.Perm (Fin 4)) :
    permHandedness σ * permHandedness σ = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hsign | hsign <;>
    simp [permHandedness, hsign]

theorem physicalMirrorFactor_mul_self (mirror : Bool) :
    physicalMirrorFactor mirror * physicalMirrorFactor mirror = 1 := by
  cases mirror <;> simp [physicalMirrorFactor]

/-- **Hidden parity obstruction.** Let every automorphism fixing the root `c` and carrying ligand
`i` to `j` act with equal handedness at two centers `d₁, d₃` reached from `i`, carrying them to
`d₁', d₃'`. Then a proper or mirror branch transport forces
`s(d₁)·s(d₃) = s(d₁')·s(d₃')`. -/
theorem not_branchTransport_of_parityCoupling (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (c : m.Center) (i j : Fin 4) (d₁ d₃ d₁' d₃' : m.Center)
    (reach₁ : LigandBranchReaches m c i d₁.1) (reach₃ : LigandBranchReaches m c i d₃.1)
    (coupled : ∀ e : m.Aut, m.centerPerm e c = c → m.ligandPermAt e c i = j →
      m.centerPerm e d₁ = d₁' ∧ m.centerPerm e d₃ = d₃' ∧
        permHandedness (m.ligandPermAt e d₁) = permHandedness (m.ligandPermAt e d₃))
    (mismatch : m.configurationSign cfg d₁ * m.configurationSign cfg d₃ ≠
      m.configurationSign cfg d₁' * m.configurationSign cfg d₃')
    (mirror : Bool) : ¬ BranchTransport m cfg c i j mirror := by
  rintro ⟨e, fixed, sent, signs⟩
  obtain ⟨image₁, image₃, sameHand⟩ := coupled e fixed sent
  have law₁ := signs d₁ reach₁
  have law₃ := signs d₃ reach₃
  rw [image₁] at law₁
  rw [image₃, ← sameHand] at law₃
  apply mismatch
  have hand := permHandedness_mul_self (m.ligandPermAt e d₁)
  have factor : ((if mirror then -1 else 1 : ℝ)) * (if mirror then -1 else 1) = 1 := by
    cases mirror <;> norm_num
  calc m.configurationSign cfg d₁ * m.configurationSign cfg d₃
      = (m.configurationSign cfg d₁ * permHandedness (m.ligandPermAt e d₁)) *
          (m.configurationSign cfg d₃ * permHandedness (m.ligandPermAt e d₁)) := by
        rw [show (m.configurationSign cfg d₁ * permHandedness (m.ligandPermAt e d₁)) *
            (m.configurationSign cfg d₃ * permHandedness (m.ligandPermAt e d₁)) =
            m.configurationSign cfg d₁ * m.configurationSign cfg d₃ *
              (permHandedness (m.ligandPermAt e d₁) * permHandedness (m.ligandPermAt e d₁)) by
            ring, hand, mul_one]
    _ = ((if mirror then -1 else 1) * m.configurationSign cfg d₁') *
          ((if mirror then -1 else 1) * m.configurationSign cfg d₃') := by rw [law₁, law₃]
    _ = m.configurationSign cfg d₁' * m.configurationSign cfg d₃' := by
        rw [show ((if mirror then -1 else 1) * m.configurationSign cfg d₁') *
            ((if mirror then -1 else 1) * m.configurationSign cfg d₃') =
            ((if mirror then -1 else 1 : ℝ) * (if mirror then -1 else 1)) *
              (m.configurationSign cfg d₁' * m.configurationSign cfg d₃') by ring, factor, one_mul]

end Parity

end

end TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalInverse

assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalInverse.rootHistory_fixed
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalInverse.rootSlot_sent
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalInverse.reach_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalInverse.retainedKeys_eq_of_blindArms
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalInverse.referenceState_none_of_blindArms
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalInverse.outwardSlot_of_fresh
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalInverse.referenceState_none_of_historyWitness
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalInverse.permHandedness_mul_self
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalInverse.not_branchTransport_of_parityCoupling
