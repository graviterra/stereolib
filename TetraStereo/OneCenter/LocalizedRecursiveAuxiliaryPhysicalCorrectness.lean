import TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalTransport
import TetraStereo.OneCenter.LocalizedCyclicPhysicalMirrorPriorTie
import TetraStereo.OneCenter.LocalizedCyclicRootIndependentJudgment
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0

/-!
# Physical consequences at a cyclic root without auxiliary rigidity

On a finite simple-bonded input with rings, at the evaluator's own final root of a detected
center, with the recursive physical domain (every other detected center a terminal twin or
calibrated; constitutional symmetry allowed):

* `rootArm_readsAgree`, `canonicalCut_readsAgree`: every real read of a transported root arm is
  covariant: the generated descriptor map at the image unit is the source value, reflected for a
  mirror (uppercase swapped, lowercase fixed).
* `priorTie_of_mirrorTransport`: a physical mirror transport of two root branches gives an actual
  prior (Rules 1–4) tie of the compiled compounds.
* `retainedKeys_eq_of_properTransport` and `referenceState_none_of_properTransport`: a physical
  proper transport of two distinct root branches gives equal complete retained keys, hence the
  actual state refuses.
* `finalRoot_*`: the same statements at `localizedFinalOccurrenceExecutable`, the occurrence the
  whole-molecule report reads.

These are the converse physical direction of the accepted root classification, now without the
non-root rigidity premise. The general inverse direction (an actual prior tie gives a physical
transport) is not claimed. Under the physical root hypothesis `ConstitutionalPairsEnantiomorphic`
(root-fixing exchanges of root ligands are enantiomorphic pairs; rigid roots satisfy it), the
inverse follows from the witnessed automorphism of a constitutional arm tie, giving the exact
prior-tie classification, the physical pair count and the physical letter of any returned root
descriptor (`finalRoot_physical_letter_of_pairs`).
-/

namespace TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness

open CertifiedLocalizedCIPInput LocalizedRuleMajorReference DeclarativeCIP
open DeclarativeCIP.RetainedOccurrenceCarrier DeclarativeCIP.RetainedCutArm
open DeclarativeCIP.RetainedCutAutomorphism
open LocalizedRecursiveAuxiliaryPhysicalDomain LocalizedRecursiveAuxiliaryPhysicalTransport
open LocalizedCyclicMatchedReadingPhysicalTransport LocalizedCyclicRootArmReachability
open LocalizedCyclicPhysicalStageTransport LocalizedCyclicPhysicalMirrorPriorTie
open RootedTetrahedralBranchSymmetry
open scoped Classical

noncomputable section

section Root

variable {input : Input} {target : Occurrence input}
  {unit : DetectedOccurrence input.certified.moleculeGraph}
  {targetUnit : input.certified.molecularFrameUnit target.1 = unit.1}

/-- **Covariant reads of a transported root arm.** Every real read of the actual stage graph of
the transported root slot reads covariant generated values. -/
theorem rootArm_readsAgree
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (frames : ContextFrameCompilation input target unit targetUnit)
    (rootAddress : target.1.address = [])
    (real : target.1.node.provenance = .realAtom)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : RecursiveAuxiliaryPhysicalDomain input.certified cfg frames.center)
    (e : input.certified.moleculeGraph.Aut) {i j : Fin 4} (distinct : i ≠ j) (mirror : Bool)
    (transport : input.certified.DetectedBranchTransport e cfg frames.center
      (frames.detectedLigandPermutation i) (frames.detectedLigandPermutation j) mirror) :
    ReadsAgree input.certified.moleculeGraph e (descriptorMap input)
      (mirroredMap input.certified.moleculeGraph mirror (descriptorMap input)) unit
      (frames.actualArmGraphs i) := by
  intro node steps occ _real ancestors context
  obtain ⟨source, sourceReach, sourceUnit⟩ :=
    actualArm_read_source singleBonded frames i node steps occ ancestors context
  exact covariant_of_law singleBonded e mirror source.occurrence occ sourceUnit
    (law_of_reach singleBonded frames rootAddress real cfg domain e distinct mirror transport
      source.occurrence ⟨source, rfl, sourceReach⟩)

/-- The same covariance on the faithful canonical predecessor cut. -/
theorem canonicalCut_readsAgree
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (frames : ContextFrameCompilation input target unit targetUnit)
    (rootAddress : target.1.address = [])
    (real : target.1.node.provenance = .realAtom)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : RecursiveAuxiliaryPhysicalDomain input.certified cfg frames.center)
    (e : input.certified.moleculeGraph.Aut) {i j : Fin 4} (distinct : i ≠ j) (mirror : Bool)
    (transport : input.certified.DetectedBranchTransport e cfg frames.center
      (frames.detectedLigandPermutation i) (frames.detectedLigandPermutation j) mirror) :
    ReadsAgree input.certified.moleculeGraph e (descriptorMap input)
      (mirroredMap input.certified.moleculeGraph mirror (descriptorMap input)) unit
      (frames.canonicalCutGraphs singleBonded i) := by
  let iso : RootedDigraph.Iso (frames.canonicalCutGraphs singleBonded i) (frames.actualArmGraphs i) :=
    Classical.choice (frames.canonicalLigandCut singleBonded i).faithful
  exact readsAgree_of_iso e (descriptorMap input)
    (mirroredMap input.certified.moleculeGraph mirror (descriptorMap input)) unit iso.symm
    (rootArm_readsAgree singleBonded frames rootAddress real cfg domain e distinct mirror transport)

/-- **Mirror transport gives an actual prior tie**, with constitutionally symmetric, Rule-4/5
decided and lowercase auxiliary centers allowed. -/
theorem priorTie_of_mirrorTransport
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (frames : ContextFrameCompilation input target unit targetUnit)
    (rootAddress : target.1.address = [])
    (real : target.1.node.provenance = .realAtom)
    {i j : Fin 4} (distinct : i ≠ j)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : RecursiveAuxiliaryPhysicalDomain input.certified cfg frames.center)
    (mirror : MirrorTransport input.certified.detectedMultiCenterMolecule cfg frames.center
      (frames.detectedLigandPermutation i) (frames.detectedLigandPermutation j)) :
    input.certified.compareLocalizedRerootCompoundRule4bcKeys
      (frames.compounds i).prior (frames.compounds j).prior = .eq := by
  obtain ⟨e, transport⟩ := exists_detectedBranchTransport_of_branchTransport input.certified
    cfg frames.center (frames.detectedLigandPermutation i) (frames.detectedLigandPermutation j)
    true mirror
  exact priorTie_of_readsAgree_and_cursor_transport singleBonded frames e
    (rootOccurrence_fixed singleBonded frames rootAddress real e transport)
    (rootSlot_transport singleBonded frames rootAddress real e transport)
    (canonicalCut_readsAgree singleBonded frames rootAddress real cfg domain e distinct true
      transport)

/-- An automorphism fixing an occurrence and carrying one frame slot to another, with
unreflected covariant reads on the first slot's canonical cut, gives equal complete retained keys
at the two slots. -/
theorem retainedKeys_eq_of_readsAgree
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (frames : ContextFrameCompilation input target unit targetUnit)
    (e : input.certified.moleculeGraph.Aut) {i j : Fin 4}
    (fixed : input.certified.transportOccurrence singleBonded e target = target)
    (sent : input.certified.transportCursor singleBonded e (frames.frame.cursorAt i) =
      frames.frame.cursorAt j)
    (reads : ReadsAgree input.certified.moleculeGraph e (descriptorMap input)
      (descriptorMap input) unit (frames.canonicalCutGraphs singleBonded i)) :
    frames.retainedKeys i = frames.retainedKeys j := by
  have keyEq := cut_rule5Key input.certified.moleculeGraph e
    (frames.canonicalLigandCut singleBonded i).focus
    (some (frames.canonicalLigandCut singleBonded i).incoming)
    (frames.canonicalLigandCut singleBonded i).anchor (descriptorMap input) (descriptorMap input)
    unit reads frames.W frames.D
  rw [mapDetected_eq_of_target_fixed (targetUnit := targetUnit) singleBonded e fixed,
    LocalizedCyclicPhysicalMirrorPriorTie.image_canonicalCut_eq singleBonded frames e fixed sent]
    at keyEq
  let isoI : RootedDigraph.Iso (frames.canonicalCutGraphs singleBonded i) (frames.actualArmGraphs i) :=
    Classical.choice (frames.canonicalLigandCut singleBonded i).faithful
  let isoJ : RootedDigraph.Iso (frames.canonicalCutGraphs singleBonded j) (frames.actualArmGraphs j) :=
    Classical.choice (frames.canonicalLigandCut singleBonded j).faithful
  have armI := retainedCompleteLigandRule5KeyAt_iso input.certified.moleculeGraph
    (descriptorMap input) unit isoI frames.W frames.D
  have armJ := retainedCompleteLigandRule5KeyAt_iso input.certified.moleculeGraph
    (descriptorMap input) unit isoJ frames.W frames.D
  change retainedCompleteLigandRule5KeyAt input.certified.moleculeGraph (descriptorMap input) unit
      (frames.actualArmGraphs i) frames.W frames.D =
    retainedCompleteLigandRule5KeyAt input.certified.moleculeGraph (descriptorMap input) unit
      (frames.actualArmGraphs j) frames.W frames.D
  rw [armI, armJ]
  exact keyEq.symm

/-- **Proper transport gives equal complete retained keys** at the two root slots. -/
theorem retainedKeys_eq_of_properTransport
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (frames : ContextFrameCompilation input target unit targetUnit)
    (rootAddress : target.1.address = [])
    (real : target.1.node.provenance = .realAtom)
    {i j : Fin 4} (distinct : i ≠ j)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : RecursiveAuxiliaryPhysicalDomain input.certified cfg frames.center)
    (proper : ProperTransport input.certified.detectedMultiCenterMolecule cfg frames.center
      (frames.detectedLigandPermutation i) (frames.detectedLigandPermutation j)) :
    frames.retainedKeys i = frames.retainedKeys j := by
  obtain ⟨e, transport⟩ := exists_detectedBranchTransport_of_branchTransport input.certified
    cfg frames.center (frames.detectedLigandPermutation i) (frames.detectedLigandPermutation j)
    false proper
  exact retainedKeys_eq_of_readsAgree singleBonded frames e
    (rootOccurrence_fixed singleBonded frames rootAddress real e transport)
    (rootSlot_transport singleBonded frames rootAddress real e transport)
    (canonicalCut_readsAgree singleBonded frames rootAddress real cfg domain e distinct false
      transport)

/-- **Physically identical root branches refuse.** -/
theorem referenceState_none_of_properTransport
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (frames : ContextFrameCompilation input target unit targetUnit)
    (rootAddress : target.1.address = [])
    (real : target.1.node.provenance = .realAtom)
    {i j : Fin 4} (distinct : i ≠ j)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : RecursiveAuxiliaryPhysicalDomain input.certified cfg frames.center)
    (proper : ProperTransport input.certified.detectedMultiCenterMolecule cfg frames.center
      (frames.detectedLigandPermutation i) (frames.detectedLigandPermutation j)) :
    referenceState input target = none := by
  have equal := retainedKeys_eq_of_properTransport singleBonded frames rootAddress real distinct
    cfg domain proper
  rw [frames.referenceState_none_iff_no_retainedJudgment singleBonded]
  rintro ⟨descriptor, points, _available, judgment⟩
  exact distinct (completeRootDescriptorJudgment_injective judgment equal)

end Root

/-! ## Auxiliary occurrences in retained context -/

section Auxiliary

variable {input : Input} {rootTarget : Occurrence input}
  {rootUnit : DetectedOccurrence input.certified.moleculeGraph}
  {rootTargetUnit : input.certified.molecularFrameUnit rootTarget.1 = rootUnit.1}
  {target : Occurrence input} {unit : DetectedOccurrence input.certified.moleculeGraph}
  {targetUnit : input.certified.molecularFrameUnit target.1 = unit.1}

/-- **Covariant reads of an outward auxiliary arm.** Let `target` be an occurrence reached from
root slot `i` of a Rule-1a tied root arm, `a` an outward slot of its actual frame, and `σ` an
automorphism fixing the root whose physical sign law holds on everything reached from slot `a`.
Every real read of the actual stage graph of slot `a` is covariant under `σ`. -/
theorem auxiliaryArm_readsAgree
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (rootFrames : ContextFrameCompilation input rootTarget rootUnit rootTargetUnit)
    (rootAddress : rootTarget.1.address = [])
    (rootReal : rootTarget.1.node.provenance = .realAtom)
    {i j : Fin 4} (distinct : i ≠ j)
    (tie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (rootFrames.stages i).a.key.constitutional.rule1a
      (rootFrames.stages j).a.key.constitutional.rule1a = .eq)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : RecursiveAuxiliaryPhysicalDomain input.certified cfg rootFrames.center)
    (frames : ContextFrameCompilation input target unit targetUnit)
    (cursor : input.certified.LocalizedRerootCursor (carrierFuel input))
    (cursorEq : cursor.occurrence = target)
    (reachable : Relation.ReflTransGen (CertifiedLocalizedCIPInput.E input.certified)
      (rootFrames.frame.cursorAt i) cursor)
    {a : Fin 4}
    (outward : IsLocalizedActualFrameOutwardCursor input.certified target (frames.frame.cursorAt a))
    (σ : input.certified.moleculeGraph.Aut) (mirror : Bool)
    (rootFixed : input.certified.detectedMultiCenterMolecule.centerPerm
      (input.certified.physicalDetectedAut σ) rootFrames.center = rootFrames.center)
    (signLaw : SignLawFrom σ cfg mirror (frames.frame.cursorAt a)) :
    ReadsAgree input.certified.moleculeGraph σ (descriptorMap input)
      (mirroredMap input.certified.moleculeGraph mirror (descriptorMap input)) unit
      (frames.actualArmGraphs a) := by
  obtain ⟨⟨previous, previousEq, shorter⟩, _inside, _nonroot, _rooted⟩ :=
    cursor_facts rootFrames rootAddress rootReal i cursor reachable
  rw [cursorEq] at shorter
  have step := frame_outward_mem_children singleBonded frames cursor cursorEq previous previousEq
    shorter outward
  have startReach := reachable.tail step
  intro node steps occ _real ancestors context
  obtain ⟨source, sourceReach, sourceUnit⟩ :=
    actualArm_read_source singleBonded frames a node steps occ ancestors context
  exact covariant_of_law singleBonded σ mirror source.occurrence occ sourceUnit
    (law_of_reachFrom singleBonded rootFrames rootAddress rootReal distinct tie cfg domain σ mirror
      rootFixed (frames.frame.cursorAt a) startReach signLaw source.occurrence
      ⟨source, rfl, sourceReach⟩)

/-- The same covariance on the canonical predecessor cut of the auxiliary slot. -/
theorem auxiliaryCut_readsAgree
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (rootFrames : ContextFrameCompilation input rootTarget rootUnit rootTargetUnit)
    (rootAddress : rootTarget.1.address = [])
    (rootReal : rootTarget.1.node.provenance = .realAtom)
    {i j : Fin 4} (distinct : i ≠ j)
    (tie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (rootFrames.stages i).a.key.constitutional.rule1a
      (rootFrames.stages j).a.key.constitutional.rule1a = .eq)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : RecursiveAuxiliaryPhysicalDomain input.certified cfg rootFrames.center)
    (frames : ContextFrameCompilation input target unit targetUnit)
    (cursor : input.certified.LocalizedRerootCursor (carrierFuel input))
    (cursorEq : cursor.occurrence = target)
    (reachable : Relation.ReflTransGen (CertifiedLocalizedCIPInput.E input.certified)
      (rootFrames.frame.cursorAt i) cursor)
    {a : Fin 4}
    (outward : IsLocalizedActualFrameOutwardCursor input.certified target (frames.frame.cursorAt a))
    (σ : input.certified.moleculeGraph.Aut) (mirror : Bool)
    (rootFixed : input.certified.detectedMultiCenterMolecule.centerPerm
      (input.certified.physicalDetectedAut σ) rootFrames.center = rootFrames.center)
    (signLaw : SignLawFrom σ cfg mirror (frames.frame.cursorAt a)) :
    ReadsAgree input.certified.moleculeGraph σ (descriptorMap input)
      (mirroredMap input.certified.moleculeGraph mirror (descriptorMap input)) unit
      (frames.canonicalCutGraphs singleBonded a) := by
  let iso : RootedDigraph.Iso (frames.canonicalCutGraphs singleBonded a) (frames.actualArmGraphs a) :=
    Classical.choice (frames.canonicalLigandCut singleBonded a).faithful
  exact readsAgree_of_iso σ (descriptorMap input)
    (mirroredMap input.certified.moleculeGraph mirror (descriptorMap input)) unit iso.symm
    (auxiliaryArm_readsAgree singleBonded rootFrames rootAddress rootReal distinct tie cfg domain
      frames cursor cursorEq reachable outward σ mirror rootFixed signLaw)

/-- **Enantiomorphic auxiliary branches tie through Rule 4.** At a reached auxiliary occurrence,
an automorphism fixing the occurrence (with its full retained history) and carrying outward slot
`a` to slot `b`, whose mirror sign law holds on the branch of `a`, gives an actual prior tie of the
compiled compounds at `a` and `b`. -/
theorem auxiliary_priorTie_of_mirror
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (rootFrames : ContextFrameCompilation input rootTarget rootUnit rootTargetUnit)
    (rootAddress : rootTarget.1.address = [])
    (rootReal : rootTarget.1.node.provenance = .realAtom)
    {i j : Fin 4} (distinct : i ≠ j)
    (tie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (rootFrames.stages i).a.key.constitutional.rule1a
      (rootFrames.stages j).a.key.constitutional.rule1a = .eq)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : RecursiveAuxiliaryPhysicalDomain input.certified cfg rootFrames.center)
    (frames : ContextFrameCompilation input target unit targetUnit)
    (cursor : input.certified.LocalizedRerootCursor (carrierFuel input))
    (cursorEq : cursor.occurrence = target)
    (reachable : Relation.ReflTransGen (CertifiedLocalizedCIPInput.E input.certified)
      (rootFrames.frame.cursorAt i) cursor)
    {a b : Fin 4}
    (outward : IsLocalizedActualFrameOutwardCursor input.certified target (frames.frame.cursorAt a))
    (σ : input.certified.moleculeGraph.Aut)
    (rootFixed : input.certified.detectedMultiCenterMolecule.centerPerm
      (input.certified.physicalDetectedAut σ) rootFrames.center = rootFrames.center)
    (fixed : input.certified.transportOccurrence singleBonded σ target = target)
    (sent : input.certified.transportCursor singleBonded σ (frames.frame.cursorAt a) =
      frames.frame.cursorAt b)
    (signLaw : SignLawFrom σ cfg true (frames.frame.cursorAt a)) :
    input.certified.compareLocalizedRerootCompoundRule4bcKeys
      (frames.compounds a).prior (frames.compounds b).prior = .eq :=
  priorTie_of_readsAgree_and_cursor_transport singleBonded frames σ fixed sent
    (auxiliaryCut_readsAgree singleBonded rootFrames rootAddress rootReal distinct tie cfg domain
      frames cursor cursorEq reachable outward σ true rootFixed signLaw)

/-- **Physically identical auxiliary branches have equal complete keys.** -/
theorem auxiliary_retainedKeys_eq_of_proper
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (rootFrames : ContextFrameCompilation input rootTarget rootUnit rootTargetUnit)
    (rootAddress : rootTarget.1.address = [])
    (rootReal : rootTarget.1.node.provenance = .realAtom)
    {i j : Fin 4} (distinct : i ≠ j)
    (tie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (rootFrames.stages i).a.key.constitutional.rule1a
      (rootFrames.stages j).a.key.constitutional.rule1a = .eq)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : RecursiveAuxiliaryPhysicalDomain input.certified cfg rootFrames.center)
    (frames : ContextFrameCompilation input target unit targetUnit)
    (cursor : input.certified.LocalizedRerootCursor (carrierFuel input))
    (cursorEq : cursor.occurrence = target)
    (reachable : Relation.ReflTransGen (CertifiedLocalizedCIPInput.E input.certified)
      (rootFrames.frame.cursorAt i) cursor)
    {a b : Fin 4}
    (outward : IsLocalizedActualFrameOutwardCursor input.certified target (frames.frame.cursorAt a))
    (σ : input.certified.moleculeGraph.Aut)
    (rootFixed : input.certified.detectedMultiCenterMolecule.centerPerm
      (input.certified.physicalDetectedAut σ) rootFrames.center = rootFrames.center)
    (fixed : input.certified.transportOccurrence singleBonded σ target = target)
    (sent : input.certified.transportCursor singleBonded σ (frames.frame.cursorAt a) =
      frames.frame.cursorAt b)
    (signLaw : SignLawFrom σ cfg false (frames.frame.cursorAt a)) :
    frames.retainedKeys a = frames.retainedKeys b :=
  retainedKeys_eq_of_readsAgree singleBonded frames σ fixed sent
    (auxiliaryCut_readsAgree singleBonded rootFrames rootAddress rootReal distinct tie cfg domain
      frames cursor cursorEq reachable outward σ false rootFixed signLaw)

/-- **Physically identical auxiliary branches refuse.** -/
theorem auxiliary_referenceState_none_of_proper
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (rootFrames : ContextFrameCompilation input rootTarget rootUnit rootTargetUnit)
    (rootAddress : rootTarget.1.address = [])
    (rootReal : rootTarget.1.node.provenance = .realAtom)
    {i j : Fin 4} (distinct : i ≠ j)
    (tie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (rootFrames.stages i).a.key.constitutional.rule1a
      (rootFrames.stages j).a.key.constitutional.rule1a = .eq)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : RecursiveAuxiliaryPhysicalDomain input.certified cfg rootFrames.center)
    (frames : ContextFrameCompilation input target unit targetUnit)
    (cursor : input.certified.LocalizedRerootCursor (carrierFuel input))
    (cursorEq : cursor.occurrence = target)
    (reachable : Relation.ReflTransGen (CertifiedLocalizedCIPInput.E input.certified)
      (rootFrames.frame.cursorAt i) cursor)
    {a b : Fin 4} (slotsDistinct : a ≠ b)
    (outward : IsLocalizedActualFrameOutwardCursor input.certified target (frames.frame.cursorAt a))
    (σ : input.certified.moleculeGraph.Aut)
    (rootFixed : input.certified.detectedMultiCenterMolecule.centerPerm
      (input.certified.physicalDetectedAut σ) rootFrames.center = rootFrames.center)
    (fixed : input.certified.transportOccurrence singleBonded σ target = target)
    (sent : input.certified.transportCursor singleBonded σ (frames.frame.cursorAt a) =
      frames.frame.cursorAt b)
    (signLaw : SignLawFrom σ cfg false (frames.frame.cursorAt a)) :
    referenceState input target = none := by
  have equal := auxiliary_retainedKeys_eq_of_proper singleBonded rootFrames rootAddress rootReal
    distinct tie cfg domain frames cursor cursorEq reachable outward σ rootFixed fixed sent signLaw
  rw [frames.referenceState_none_iff_no_retainedJudgment singleBonded]
  rintro ⟨descriptor, points, _available, judgment⟩
  exact slotsDistinct (completeRootDescriptorJudgment_injective judgment equal)

/-! ### From atom-level symmetry data to the cursor-level transport facts -/

private theorem occurrenceUnit_ext' {Atom : Type*} {a b : OccurrenceUnit Atom}
    (rootEq : a.root = b.root) (pathEq : a.path = b.path) : a = b := by
  cases a
  cases b
  simp_all

private theorem mem_of_getLast?_eq' {α : Type*} : ∀ {l : List α} {a : α},
    l.getLast? = some a → a ∈ l
  | [], _, h => by simp at h
  | [_], a, h => by
      simp at h
      simp [h]
  | _ :: y :: rest, _, h => by
      rw [List.getLast?_cons_cons] at h
      exact List.mem_cons_of_mem _ (mem_of_getLast?_eq' (l := y :: rest) h)

/-- The outer root is an atom of every carrier history. -/
theorem root_mem_history (occurrence : Occurrence input) :
    occurrence.1.root ∈ occurrence.1.node.history :=
  mem_of_getLast?_eq' (input.certified.frameCarrierOccurrence_history_getLast_eq_root occurrence)

/-- An outward frame slot of a real occurrence extends its history by the slot's detected
ligand. -/
theorem outwardSlot_history
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (frames : ContextFrameCompilation input target unit targetUnit)
    (real : target.1.node.provenance = .realAtom) {a : Fin 4}
    (outward : IsLocalizedActualFrameOutwardCursor input.certified target (frames.frame.cursorAt a)) :
    (frames.frame.cursorAt a).occurrence.1.node.history =
      input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
          (frames.detectedLigandPermutation a) :: target.1.node.history := by
  have centerMeaning := (input.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff target
    frames.center).mp frames.centerComputed
  obtain ⟨slot, addressEq⟩ := outward
  have mem : (frames.frame.cursorAt a).occurrence.1.node ∈
      input.certified.executableOfficialCIPChildren target.1.node :=
    LocalizedActualBoundaryObservationReadback.outwardChild_node_mem input.certified
      { occurrence := target, previous? := none } (frames.frame.cursorAt a)
      (frames.ligandCursor_outerRoot a) slot addressEq
  obtain ⟨atom, nodeEq, _adjacent, _⟩ :=
    (LocalizedActualBoundaryPathRealization.mem_executableOfficialCIPChildren_iff input.certified
      singleBonded target.1.node centerMeaning.2 real _).mp mem
  have atomEq : atom = input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
      (frames.detectedLigandPermutation a) := by
    have ligand := frames.ligandAt a
    rw [nodeEq, OfficialCIPNode.extend_current?] at ligand
    exact Option.some.inj ligand
  rw [nodeEq, OfficialCIPNode.extend_history, atomEq]

/-- An automorphism fixing every atom of a retained history fixes the occurrence. -/
theorem transportOccurrence_fixed_of_history
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (σ : input.certified.moleculeGraph.Aut) (occurrence : Occurrence input)
    (historyFixed : ∀ x ∈ occurrence.1.node.history,
      (σ : Equiv.Perm input.certified.Atom) x = x) :
    input.certified.transportOccurrence singleBonded σ occurrence = occurrence := by
  apply input.certified.molecularFrameUnit_injective_on_simpleBonded_carrier singleBonded
  rw [input.certified.molecularFrameUnit_transport singleBonded σ occurrence]
  apply occurrenceUnit_ext'
  · exact historyFixed _ (root_mem_history occurrence)
  · show (occurrence.1.node.history.reverse.tail).map (σ : Equiv.Perm input.certified.Atom) =
      occurrence.1.node.history.reverse.tail
    refine (List.map_congr_left fun x member => ?_).trans (List.map_id _)
    exact historyFixed x (List.mem_reverse.1 (List.mem_of_mem_tail member))

/-- An automorphism fixing every atom of the retained history of a real occurrence and carrying
one outward ligand atom to another carries the actual slot cursor to the actual slot cursor. -/
theorem transportCursor_slot_of_history
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (frames : ContextFrameCompilation input target unit targetUnit)
    (real : target.1.node.provenance = .realAtom)
    (σ : input.certified.moleculeGraph.Aut) {a b : Fin 4}
    (outwardA : IsLocalizedActualFrameOutwardCursor input.certified target
      (frames.frame.cursorAt a))
    (outwardB : IsLocalizedActualFrameOutwardCursor input.certified target
      (frames.frame.cursorAt b))
    (historyFixed : ∀ x ∈ target.1.node.history, (σ : Equiv.Perm input.certified.Atom) x = x)
    (ligandSent : (σ : Equiv.Perm input.certified.Atom)
        (input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
          (frames.detectedLigandPermutation a)) =
      input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
        (frames.detectedLigandPermutation b)) :
    input.certified.transportCursor singleBonded σ (frames.frame.cursorAt a) =
      frames.frame.cursorAt b := by
  have historyA := outwardSlot_history singleBonded frames real outwardA
  have historyB := outwardSlot_history singleBonded frames real outwardB
  have rootA := frames.ligandCursor_outerRoot a
  have rootB := frames.ligandCursor_outerRoot b
  have nonempty : target.1.node.history.reverse ≠ [] := by
    intro empty
    have member := List.mem_reverse.2 (root_mem_history target)
    rw [empty] at member
    simp at member
  apply LocalizedRerootCursor.ext
  · apply input.certified.molecularFrameUnit_injective_on_simpleBonded_carrier singleBonded
    rw [input.certified.transportCursor_occurrence, input.certified.molecularFrameUnit_transport]
    apply occurrenceUnit_ext'
    · show (σ : Equiv.Perm input.certified.Atom) (frames.frame.cursorAt a).occurrence.1.root =
        (frames.frame.cursorAt b).occurrence.1.root
      rw [rootA, rootB]
      exact historyFixed _ (root_mem_history target)
    · show ((frames.frame.cursorAt a).occurrence.1.node.history.reverse.tail).map
          (σ : Equiv.Perm input.certified.Atom) =
        (frames.frame.cursorAt b).occurrence.1.node.history.reverse.tail
      rw [historyA, historyB, List.reverse_cons, List.reverse_cons,
        List.tail_append_of_ne_nil nonempty, List.tail_append_of_ne_nil nonempty, List.map_append,
        List.map_singleton, ligandSent]
      congr 1
      refine (List.map_congr_left fun x member => ?_).trans (List.map_id _)
      exact historyFixed x (List.mem_reverse.1 (List.mem_of_mem_tail member))
  · rw [input.certified.transportCursor_previous?, frames.ligandCursor_previous singleBonded,
      frames.ligandCursor_previous singleBonded, Option.map_some]
    exact congrArg some
      (transportOccurrence_fixed_of_history singleBonded σ target historyFixed)

/-- **The explored outward branch is the residual component.** Every cursor reached from an
outward slot of a real occurrence extends the occurrence's retained history, and a real one sits
at an atom of the residual component of the slot's ligand after deleting that history. Rings and
duplicate leaves are included. -/
theorem reached_history_inComponent
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (frames : ContextFrameCompilation input target unit targetUnit)
    (real : target.1.node.provenance = .realAtom) {a : Fin 4}
    (outward : IsLocalizedActualFrameOutwardCursor input.certified target (frames.frame.cursorAt a))
    (cursor : input.certified.LocalizedRerootCursor (carrierFuel input))
    (reachable : Relation.ReflTransGen (CertifiedLocalizedCIPInput.E input.certified)
      (frames.frame.cursorAt a) cursor) :
    ∃ extra : List input.certified.Atom, extra ≠ [] ∧
      cursor.occurrence.1.node.history = extra ++ target.1.node.history ∧
      (cursor.occurrence.1.node.provenance = .realAtom →
        ∃ atom, cursor.occurrence.1.node.current? = some atom ∧
          RetainedCoherentSymmetry.InComponent input.certified.moleculeGraph
            target.1.node.history
            (input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
              (frames.detectedLigandPermutation a)) atom) := by
  have deeper : target.1.address.length <
      (frames.frame.cursorAt a).occurrence.1.address.length := by
    obtain ⟨k, addressEq⟩ := outward
    rw [addressEq]
    simp
  have firstOut := input.certified.outward_first_cursor target (frames.frame.cursorAt a)
    (frames.childAt a) deeper
  induction reachable with
  | refl =>
      refine ⟨[input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
        (frames.detectedLigandPermutation a)], by simp, ?_, ?_⟩
      · rw [outwardSlot_history singleBonded frames real outward]
        rfl
      · intro startReal
        refine ⟨_, frames.ligandAt a, ?_, SimpleGraph.Reachable.refl _⟩
        have nodup := (LocalizedActualBoundaryObservationReadback.occurrence_history_facts
          input.certified _ startReal).1
        rw [outwardSlot_history singleBonded frames real outward] at nodup
        exact (List.nodup_cons.1 nodup).1
  | @tail c c' path edge ih =>
      obtain ⟨extra, extraNe, history, realC⟩ := ih
      obtain ⟨valid, _dependency, previous, previousEq, shorter⟩ :=
        input.certified.outward_reachable_cursor target (frames.frame.cursorAt a) c firstOut path
      obtain ⟨dropLastEq, lengthEq, rootEq, _previous', _valid'⟩ :=
        input.certified.outward_edge c c' valid previous previousEq shorter edge
      have childNonempty : c'.occurrence.1.address ≠ [] := by
        intro empty
        have lengths := congrArg List.length empty
        rw [lengthEq, List.length_nil] at lengths
        omega
      have childAddr : c'.occurrence.1.address =
          c.occurrence.1.address ++ [c'.occurrence.1.address.getLast childNonempty] := by
        have concatEq := List.dropLast_append_getLast childNonempty
        rw [dropLastEq] at concatEq
        exact concatEq.symm
      have mem := LocalizedActualBoundaryObservationReadback.outwardChild_node_mem input.certified
        c c' rootEq _ childAddr
      have cReal : c.occurrence.1.node.provenance = .realAtom := by
        rcases input.certified.carrierOccurrence_provenance_simple_or_ring singleBonded
            c.occurrence with realProvenance | ⟨distance, ring⟩
        · exact realProvenance
        · exfalso
          have duplicate : c.occurrence.1.node.isDuplicateLeaf = true := by
            simp [OfficialCIPNode.isDuplicateLeaf, ring, OfficialCIPNodeProvenance.isDuplicateLeaf]
          unfold CertifiedLocalizedCIPInput.executableOfficialCIPChildren at mem
          rw [if_pos duplicate] at mem
          simp at mem
      obtain ⟨atom, current, component⟩ := realC cReal
      obtain ⟨next, nodeEq, adjacent, _⟩ :=
        (LocalizedActualBoundaryPathRealization.mem_executableOfficialCIPChildren_iff
          input.certified singleBonded c.occurrence.1.node current cReal _).mp mem
      have historyNext : c'.occurrence.1.node.history = next :: c.occurrence.1.node.history := by
        rw [nodeEq, OfficialCIPNode.extend_history]
      refine ⟨next :: extra, by simp, by rw [historyNext, history]; rfl, ?_⟩
      intro realNext
      have nodupNext := (LocalizedActualBoundaryObservationReadback.occurrence_history_facts
        input.certified c'.occurrence realNext).1
      rw [historyNext, history] at nodupNext
      have nextNotBoundary : next ∉ target.1.node.history := fun member =>
        (List.nodup_cons.1 nodupNext).1 (List.mem_append_right _ member)
      have factsC := LocalizedActualBoundaryObservationReadback.occurrence_history_facts
        input.certified c.occurrence cReal
      have headEq : c.occurrence.1.node.history.head? = some atom := factsC.2.symm.trans current
      have nodupC := factsC.1
      rw [history] at headEq nodupC
      obtain ⟨first, restExtra, extraEq⟩ := List.exists_cons_of_ne_nil extraNe
      rw [extraEq, List.cons_append] at headEq nodupC
      simp only [List.head?_cons, Option.some.injEq] at headEq
      subst headEq
      have atomNotBoundary : first ∉ target.1.node.history := fun member =>
        (List.nodup_cons.1 nodupC).1 (List.mem_append_right _ member)
      refine ⟨next, by rw [nodeEq, OfficialCIPNode.extend_current?], component.1, ?_⟩
      exact component.2.trans
        (SimpleGraph.Adj.reachable ⟨atomNotBoundary, nextNotBoundary, adjacent⟩)

/-- A sign law on the residual component of an outward ligand gives the sign law on everything
the evaluator explores from that slot. -/
theorem signLawFrom_of_component
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (frames : ContextFrameCompilation input target unit targetUnit)
    (real : target.1.node.provenance = .realAtom) {a : Fin 4}
    (outward : IsLocalizedActualFrameOutwardCursor input.certified target (frames.frame.cursorAt a))
    (σ : input.certified.moleculeGraph.Aut)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration) (mirror : Bool)
    (componentLaw : ∀ d : input.certified.detectedMultiCenterMolecule.Center,
      RetainedCoherentSymmetry.InComponent input.certified.moleculeGraph target.1.node.history
        (input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
          (frames.detectedLigandPermutation a)) d.1 →
      input.certified.detectedMultiCenterMolecule.configurationSign cfg d *
          permHandedness (input.certified.detectedMultiCenterMolecule.ligandPermAt
            (input.certified.physicalDetectedAut σ) d) =
        physicalMirrorFactor mirror *
          input.certified.detectedMultiCenterMolecule.configurationSign cfg
            (input.certified.detectedMultiCenterMolecule.centerPerm
              (input.certified.physicalDetectedAut σ) d)) :
    SignLawFrom σ cfg mirror (frames.frame.cursorAt a) := by
  intro cursor reachable cursorReal d current
  obtain ⟨_extra, _nonempty, _history, located⟩ :=
    reached_history_inComponent singleBonded frames real outward cursor reachable
  obtain ⟨atom, current', component⟩ := located cursorReal
  have atomEq : atom = d.1 := Option.some.inj (current'.symm.trans current)
  rw [atomEq] at component
  exact componentLaw d component

/-- **Physical symmetry of two outward branches at an auxiliary occurrence.** The automorphism
fixes every atom of the occurrence's retained history (outer root included), carries outward
ligand `a` to outward ligand `b`, and realizes the proper (`mirror = false`) or mirror
(`mirror = true`) configuration relation at every center of the residual component of `a` after
deleting that history. Only graph and configuration data occur. -/
structure AuxiliaryBranchTransport
    (frames : ContextFrameCompilation input target unit targetUnit)
    (σ : input.certified.moleculeGraph.Aut)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration) (a b : Fin 4)
    (mirror : Bool) : Prop where
  historyFixed : ∀ x ∈ target.1.node.history, (σ : Equiv.Perm input.certified.Atom) x = x
  ligandSent : (σ : Equiv.Perm input.certified.Atom)
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
        (frames.detectedLigandPermutation a)) =
    input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
      (frames.detectedLigandPermutation b)
  componentLaw : ∀ d : input.certified.detectedMultiCenterMolecule.Center,
    RetainedCoherentSymmetry.InComponent input.certified.moleculeGraph target.1.node.history
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
        (frames.detectedLigandPermutation a)) d.1 →
    input.certified.detectedMultiCenterMolecule.configurationSign cfg d *
        permHandedness (input.certified.detectedMultiCenterMolecule.ligandPermAt
          (input.certified.physicalDetectedAut σ) d) =
      physicalMirrorFactor mirror *
        input.certified.detectedMultiCenterMolecule.configurationSign cfg
          (input.certified.detectedMultiCenterMolecule.centerPerm
            (input.certified.physicalDetectedAut σ) d)

/-- The atom-level root-arm equivalence gives the actual Rule-1a tie of the two root arms. -/
theorem rootArms_rule1aTie_of_atoms
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
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (rootFrames.stages i).a.key.constitutional.rule1a
      (rootFrames.stages j).a.key.constitutional.rule1a = .eq := by
  have history := (rootFrame_target_facts rootFrames rootAddress rootReal).2.1
  have historyFixed : ∀ x ∈ rootTarget.1.node.history,
      (e : Equiv.Perm input.certified.Atom) x = x := by
    intro x member
    rw [history, List.mem_singleton] at member
    rw [member]
    exact rootFixed
  have outwardI : IsLocalizedActualFrameOutwardCursor input.certified rootTarget
      (rootFrames.frame.cursorAt i) :=
    ⟨_, (rootFramePair rootFrames rootAddress i i).leftAddress⟩
  have outwardJ : IsLocalizedActualFrameOutwardCursor input.certified rootTarget
      (rootFrames.frame.cursorAt j) :=
    ⟨_, (rootFramePair rootFrames rootAddress j j).leftAddress⟩
  exact rootArms_rule1aTie singleBonded rootFrames e
    (transportCursor_slot_of_history singleBonded rootFrames rootReal e outwardI outwardJ
      historyFixed ligandSent)

/-- **Enantiomorphic auxiliary branches tie through Rule 4 (physical form).** Let a real
occurrence `target` be reached from root slot `i`, whose root arm is constitutionally equivalent
to root arm `j` (an automorphism `e` fixing the root atom and sending ligand `α i` to `α j`).
For two outward slots `a, b` of the target's actual frame and a mirror
`AuxiliaryBranchTransport`, the compiled compounds at `a` and `b` tie through Rules 1–4. -/
theorem auxiliary_priorTie_of_physicalMirror
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
    (frames : ContextFrameCompilation input target unit targetUnit)
    (real : target.1.node.provenance = .realAtom)
    (cursor : input.certified.LocalizedRerootCursor (carrierFuel input))
    (cursorEq : cursor.occurrence = target)
    (reachable : Relation.ReflTransGen (CertifiedLocalizedCIPInput.E input.certified)
      (rootFrames.frame.cursorAt i) cursor)
    {a b : Fin 4}
    (outwardA : IsLocalizedActualFrameOutwardCursor input.certified target
      (frames.frame.cursorAt a))
    (outwardB : IsLocalizedActualFrameOutwardCursor input.certified target
      (frames.frame.cursorAt b))
    (σ : input.certified.moleculeGraph.Aut)
    (transport : AuxiliaryBranchTransport frames σ cfg a b true) :
    input.certified.compareLocalizedRerootCompoundRule4bcKeys
      (frames.compounds a).prior (frames.compounds b).prior = .eq := by
  have tie := rootArms_rule1aTie_of_atoms singleBonded rootFrames rootAddress rootReal e
    rootArmFixed rootArmSent
  obtain ⟨_previousData, _inside, _nonroot, rooted⟩ :=
    cursor_facts rootFrames rootAddress rootReal i cursor reachable
  rw [cursorEq] at rooted
  have rootFixed : input.certified.detectedMultiCenterMolecule.centerPerm
      (input.certified.physicalDetectedAut σ) rootFrames.center = rootFrames.center := by
    apply (RootedTetrahedralBranchSymmetry.centerPerm_eq_iff
      input.certified.detectedMultiCenterMolecule (input.certified.physicalDetectedAut σ)
      rootFrames.center).mpr
    have member : rootFrames.center.1 ∈ target.1.node.history := by
      rw [rooted]
      exact root_mem_history target
    exact transport.historyFixed _ member
  exact auxiliary_priorTie_of_mirror singleBonded rootFrames rootAddress rootReal distinct tie cfg
    domain frames cursor cursorEq reachable outwardA σ rootFixed
    (transportOccurrence_fixed_of_history singleBonded σ target transport.historyFixed)
    (transportCursor_slot_of_history singleBonded frames real σ outwardA outwardB
      transport.historyFixed transport.ligandSent)
    (signLawFrom_of_component singleBonded frames real outwardA σ cfg true
      transport.componentLaw)

/-- **Physically identical auxiliary branches refuse (physical form).** -/
theorem auxiliary_referenceState_none_of_physicalProper
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
    (frames : ContextFrameCompilation input target unit targetUnit)
    (real : target.1.node.provenance = .realAtom)
    (cursor : input.certified.LocalizedRerootCursor (carrierFuel input))
    (cursorEq : cursor.occurrence = target)
    (reachable : Relation.ReflTransGen (CertifiedLocalizedCIPInput.E input.certified)
      (rootFrames.frame.cursorAt i) cursor)
    {a b : Fin 4} (slotsDistinct : a ≠ b)
    (outwardA : IsLocalizedActualFrameOutwardCursor input.certified target
      (frames.frame.cursorAt a))
    (outwardB : IsLocalizedActualFrameOutwardCursor input.certified target
      (frames.frame.cursorAt b))
    (σ : input.certified.moleculeGraph.Aut)
    (transport : AuxiliaryBranchTransport frames σ cfg a b false) :
    referenceState input target = none := by
  have tie := rootArms_rule1aTie_of_atoms singleBonded rootFrames rootAddress rootReal e
    rootArmFixed rootArmSent
  obtain ⟨_previousData, _inside, _nonroot, rooted⟩ :=
    cursor_facts rootFrames rootAddress rootReal i cursor reachable
  rw [cursorEq] at rooted
  have rootFixed : input.certified.detectedMultiCenterMolecule.centerPerm
      (input.certified.physicalDetectedAut σ) rootFrames.center = rootFrames.center := by
    apply (RootedTetrahedralBranchSymmetry.centerPerm_eq_iff
      input.certified.detectedMultiCenterMolecule (input.certified.physicalDetectedAut σ)
      rootFrames.center).mpr
    have member : rootFrames.center.1 ∈ target.1.node.history := by
      rw [rooted]
      exact root_mem_history target
    exact transport.historyFixed _ member
  exact auxiliary_referenceState_none_of_proper singleBonded rootFrames rootAddress rootReal
    distinct tie cfg domain frames cursor cursorEq reachable slotsDistinct outwardA σ rootFixed
    (transportOccurrence_fixed_of_history singleBonded σ target transport.historyFixed)
    (transportCursor_slot_of_history singleBonded frames real σ outwardA outwardB
      transport.historyFixed transport.ligandSent)
    (signLawFrom_of_component singleBonded frames real outwardA σ cfg false
      transport.componentLaw)

end Auxiliary

/-! ## The occurrence read by the whole-molecule report -/

section Final

variable (input : Input) (singleBonded : input.certified.moleculeGraph.SimpleBonded)
  (center : input.certified.TetrahedralCenter)

private theorem domain_final (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : RecursiveAuxiliaryPhysicalDomain input.certified cfg center) :
    RecursiveAuxiliaryPhysicalDomain input.certified cfg
      (finalRootFrames input singleBonded center).center := by
  rw [finalRootFrames_center input singleBonded center]
  exact domain

/-- **Final-root recursive auxiliary law.** For a physical branch transport of two final-root
ligand slots, every occurrence reached from the transported slot has its generated state
transported by `retainedPhysicalLetter`. -/
theorem finalRoot_law_of_reach
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : RecursiveAuxiliaryPhysicalDomain input.certified cfg center)
    (e : input.certified.moleculeGraph.Aut) {i j : Fin 4} (distinct : i ≠ j) (mirror : Bool)
    (transport : input.certified.DetectedBranchTransport e cfg
      (finalRootFrames input singleBonded center).center
      ((finalRootFrames input singleBonded center).detectedLigandPermutation i)
      ((finalRootFrames input singleBonded center).detectedLigandPermutation j) mirror)
    (occurrence : Occurrence input)
    (reach : Reach (finalRootFrames input singleBonded center) i occurrence) :
    Law singleBonded e mirror occurrence :=
  law_of_reach singleBonded (finalRootFrames input singleBonded center)
    (input.certified.localizedFinalOccurrenceExecutable_address (carrierFuel input) center)
    (finalOccurrence_provenance_real input center) cfg
    (domain_final input singleBonded center cfg domain) e distinct mirror transport occurrence
    reach

/-- **Final-root mirror transport gives an actual prior tie.** -/
theorem finalRoot_priorTie_of_mirrorTransport
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : RecursiveAuxiliaryPhysicalDomain input.certified cfg center) {i j : Fin 4}
    (distinct : i ≠ j)
    (mirror : MirrorTransport input.certified.detectedMultiCenterMolecule cfg center
      ((finalRootFrames input singleBonded center).detectedLigandPermutation i)
      ((finalRootFrames input singleBonded center).detectedLigandPermutation j)) :
    input.certified.compareLocalizedRerootCompoundRule4bcKeys
      ((finalRootFrames input singleBonded center).compounds i).prior
      ((finalRootFrames input singleBonded center).compounds j).prior = .eq := by
  have centerEq := finalRootFrames_center input singleBonded center
  apply priorTie_of_mirrorTransport singleBonded (finalRootFrames input singleBonded center)
    (input.certified.localizedFinalOccurrenceExecutable_address (carrierFuel input) center)
    (finalOccurrence_provenance_real input center) distinct cfg
    (domain_final input singleBonded center cfg domain)
  simpa only [centerEq] using mirror

/-- **Final-root physically identical branches refuse.** -/
theorem finalRoot_referenceState_none_of_properTransport
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : RecursiveAuxiliaryPhysicalDomain input.certified cfg center) {i j : Fin 4}
    (distinct : i ≠ j)
    (proper : ProperTransport input.certified.detectedMultiCenterMolecule cfg center
      ((finalRootFrames input singleBonded center).detectedLigandPermutation i)
      ((finalRootFrames input singleBonded center).detectedLigandPermutation j)) :
    referenceState input
      (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center) = none := by
  have centerEq := finalRootFrames_center input singleBonded center
  apply referenceState_none_of_properTransport singleBonded
    (finalRootFrames input singleBonded center)
    (input.certified.localizedFinalOccurrenceExecutable_address (carrierFuel input) center)
    (finalOccurrence_provenance_real input center) distinct cfg
    (domain_final input singleBonded center cfg domain)
  simpa only [centerEq] using proper

/-- **Complete physical descriptor at a constitutionally rigid root, with arbitrary auxiliary
centers.** Let no automorphism fixing the detected root move any of its ligands. On a
simple-bonded input of constant formal charge with calibrated root geometry, the report state is
the uppercase geometric letter in the reader-free constitutional priority order, the report lists
it, the physical enantiomorphic-pair count is zero and the root branches are properly
distinguishable. Nothing is assumed about the other detected centers: they may be
constitutionally symmetric, Rule-4/5-decided, pseudoasymmetric or refused. -/
theorem finalRoot_physical_descriptor_of_rigidRoot
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (rigid : ConstitutionallyRigid input.certified.detectedMultiCenterMolecule center)
    (geometry : LocalizedCyclicRootPhysicalSetup.RootPhysicalGeometry input.certified
      input.certified.detectedMultiCenterMolecule cfg center) :
    ∃ strict : LocalizedCyclicGeneralRigidPriority.FrameConstitutionalStrict
        (finalRootFrames input singleBonded center).frame,
      let raw : RS :=
        if input.certified.detectedMultiCenterMolecule.configurationSign cfg
              (finalRootFrames input singleBonded center).center *
            permHandedness (finalRootFrames input singleBonded center).detectedLigandPermutation *
            permHandedness (LocalizedCyclicGeneralRigidGeneratedLabels.priorityOrder
              (finalRootFrames input singleBonded center) strict singleBonded) = -1
        then .R else .S
      referenceState input
          (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center) =
        some (.chiral raw) ∧
      (center.val.val, some (.chiral raw : LocalizedAuxiliaryLabel)) ∈ analyze input ∧
      physicalEnantiomorphicPairCount input.certified.detectedMultiCenterMolecule cfg center = 0 ∧
      MultiCenterMolecule.PairwiseProperDistinguishable
        input.certified.detectedMultiCenterMolecule cfg center := by
  have centerEq := finalRootFrames_center input singleBonded center
  have rootAddress :=
    input.certified.localizedFinalOccurrenceExecutable_address (carrierFuel input) center
  have rootReal := finalOccurrence_provenance_real input center
  have centerMeaning := (input.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff _
    (finalRootFrames input singleBonded center).center).mp
    (finalRootFrames input singleBonded center).centerComputed
  have rigidGraph : ConstitutionallyRigidGraphAt input.certified.moleculeGraph
      (finalRootFrames input singleBonded center).center.1 := by
    rw [centerEq]
    exact constitutionallyRigidGraphAt_of_constitutionallyRigid_detected input.certified center
      rigid
  have strict : LocalizedCyclicGeneralRigidPriority.FrameConstitutionalStrict
      (finalRootFrames input singleBonded center).frame := fun left right distinct =>
    LocalizedActualBoundaryObservationReadback.outwardSiblings_separated_of_rigidTarget
      input.certified singleBonded charge _ rootReal centerMeaning.2 rigidGraph
      (rootFramePair (finalRootFrames input singleBonded center) rootAddress left right) rfl
      (LocalizedCyclicGeneralRigidPriority.frame_cursorAt_ne _
        (finalRootFrames input singleBonded center).frame
        (LocalizedCyclicGeneralRigidGeneratedLabels.frame_computed
          (finalRootFrames input singleBonded center)) distinct)
  have calibrated : ActualPhysicalGeneralRigidCalibratedCenter input.certified
      input.certified.detectedMultiCenterMolecule cfg
      (finalRootFrames input singleBonded center).center := by
    rw [centerEq]
    exact ⟨rigid, geometry⟩
  have state := LocalizedCyclicGeneralRigidGeneratedLabels.referenceState_eq_chiral_of_calibrated
    (finalRootFrames input singleBonded center) strict singleBonded cfg calibrated
  have noTransport : ∀ (i j : Fin 4) (mirror : Bool), i ≠ j →
      ¬ BranchTransport input.certified.detectedMultiCenterMolecule cfg center i j mirror := by
    rintro i j mirror distinct ⟨e, fixed, sent, _signs⟩
    rw [rigid e fixed] at sent
    exact distinct sent
  have noPair : ∀ i j : Fin 4,
      ¬ Enantiomorphic input.certified.detectedMultiCenterMolecule cfg center i j :=
    fun i j pair => noTransport i j true pair.1 pair.2.1
  refine ⟨strict, state, LocalizedCyclicRootIndependentJudgment.finalRoot_analyze_entry state,
    ?_, ?_⟩
  · simp [physicalEnantiomorphicPairCount, sourceEnantiomorphicPairCount, noPair]
  · exact fun i j distinct => noTransport i j false distinct

end Final

/-! ## Roots whose constitutionally equivalent ligands are enantiomorphic -/

section Pairs

/-- **Physical root hypothesis.** Every two distinct root ligands exchanged by an automorphism
fixing the root form a physical enantiomorphic pair. It mentions only the graph and the
configuration; a constitutionally rigid root satisfies it vacuously. -/
def ConstitutionalPairsEnantiomorphic {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) (cfg : m.Configuration) (c : m.Center) : Prop :=
  ∀ e : m.Aut, m.centerPerm e c = c → ∀ i j : Fin 4, i ≠ j → m.ligandPermAt e c i = j →
    Enantiomorphic m cfg c i j

theorem constitutionalPairsEnantiomorphic_of_rigid {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) (cfg : m.Configuration) (c : m.Center)
    (rigid : ConstitutionallyRigid m c) : ConstitutionalPairsEnantiomorphic m cfg c := by
  intro e fixed i j distinct sent
  rw [rigid e fixed] at sent
  exact (distinct sent).elim

/-- The hypothesis gives physical proper distinguishability of the root branches. -/
theorem pairwiseProperDistinguishable_of_pairs {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) (cfg : m.Configuration) (c : m.Center)
    (pairs : ConstitutionalPairsEnantiomorphic m cfg c) :
    MultiCenterMolecule.PairwiseProperDistinguishable m cfg c := by
  rintro i j distinct ⟨e, fixed, sent, signs⟩
  exact (pairs e fixed i j distinct sent).2.2 ⟨e, fixed, sent, signs⟩

variable {input : Input} {target : Occurrence input}
  {unit : DetectedOccurrence input.certified.moleculeGraph}
  {targetUnit : input.certified.molecularFrameUnit target.1 = unit.1}

/-- **Inverse at the root under the physical hypothesis.** An actual prior tie of two distinct
root slots is a Rule-4a tie; its two current arms tie constitutionally, and the automorphism
witnessed by these arm trees fixes the root and exchanges the two ligands. Auxiliary centers are
arbitrary. -/
theorem enantiomorphic_of_priorTie_of_pairs
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph)
    (frames : ContextFrameCompilation input target unit targetUnit)
    (rootAddress : target.1.address = [])
    (real : target.1.node.provenance = .realAtom)
    {i j : Fin 4} (distinct : i ≠ j)
    (priorTie : input.certified.compareLocalizedRerootCompoundRule4bcKeys
      (frames.compounds i).prior (frames.compounds j).prior = .eq)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (pairs : ConstitutionalPairsEnantiomorphic input.certified.detectedMultiCenterMolecule cfg
      frames.center) :
    Enantiomorphic input.certified.detectedMultiCenterMolecule cfg frames.center
      (frames.detectedLigandPermutation i) (frames.detectedLigandPermutation j) := by
  obtain ⟨rule4aTie, -, -, -⟩ :=
    (input.certified.compareLocalizedRerootCompoundRule4bcKeys_eq_eq_iff _ _).mp priorTie
  obtain ⟨armL⟩ := nonempty_rootArm frames .rule4a i
  obtain ⟨armR⟩ := nonempty_rootArm frames .rule4a j
  have tie := armTie_of_rule4aTie frames armL armR rule4aTie
  obtain ⟨rootCurrent, rootHistory, _rootRoot⟩ := rootFrame_target_facts frames rootAddress real
  obtain ⟨realI, _rootI, _historyI⟩ :=
    rootFrame_cursor_facts singleBonded frames rootAddress real i
  obtain ⟨realJ, _rootJ, _historyJ⟩ :=
    rootFrame_cursor_facts singleBonded frames rootAddress real j
  have rootBoundary :
      (rootFramePair frames rootAddress i j).target.occurrence.1.node.history.reverse =
        [frames.center.1] := by
    show target.1.node.history.reverse = [frames.center.1]
    rw [rootHistory]
    rfl
  obtain ⟨π, hπ, πRoot, a, b, ha, hb, πab, -⟩ :=
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
  exact pairs E rootFixed _ _
    (fun same => distinct (frames.detectedLigandPermutation.injective same)) ligandSent

/-- **Pointwise root classification without auxiliary rigidity.** Under the physical hypothesis,
an actual prior tie of two distinct root slots is exactly a physical enantiomorphic pair. -/
theorem priorTie_iff_enantiomorphic_of_pairs
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph)
    (frames : ContextFrameCompilation input target unit targetUnit)
    (rootAddress : target.1.address = [])
    (real : target.1.node.provenance = .realAtom)
    {i j : Fin 4} (distinct : i ≠ j)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : RecursiveAuxiliaryPhysicalDomain input.certified cfg frames.center)
    (pairs : ConstitutionalPairsEnantiomorphic input.certified.detectedMultiCenterMolecule cfg
      frames.center) :
    input.certified.compareLocalizedRerootCompoundRule4bcKeys
        (frames.compounds i).prior (frames.compounds j).prior = .eq ↔
      Enantiomorphic input.certified.detectedMultiCenterMolecule cfg frames.center
        (frames.detectedLigandPermutation i) (frames.detectedLigandPermutation j) :=
  ⟨fun priorTie => enantiomorphic_of_priorTie_of_pairs singleBonded charge frames rootAddress
      real distinct priorTie cfg pairs,
    fun pair => priorTie_of_mirrorTransport singleBonded frames rootAddress real distinct cfg
      domain pair.2.1⟩

end Pairs

section FinalPairs

open LocalizedCyclicRootPhysicalSetup LocalizedCyclicRootIndependentJudgment

variable (input : Input) (singleBonded : input.certified.moleculeGraph.SimpleBonded)
  (center : input.certified.TetrahedralCenter)

/-- The retained prior pairs of the actual root stage keys are the physical enantiomorphic pairs,
read through the frame alignment. -/
theorem finalRoot_completePriorPair_iff_enantiomorphic_of_pairs
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : RecursiveAuxiliaryPhysicalDomain input.certified cfg center)
    (pairs : ConstitutionalPairsEnantiomorphic input.certified.detectedMultiCenterMolecule cfg
      center) (i j : Fin 4) :
    CompletePriorPair (finalRootFrames input singleBonded center).retainedKeys i j ↔
      Enantiomorphic input.certified.detectedMultiCenterMolecule cfg center
        ((finalRootFrames input singleBonded center).detectedLigandPermutation i)
        ((finalRootFrames input singleBonded center).detectedLigandPermutation j) := by
  have centerEq := finalRootFrames_center input singleBonded center
  have pairs' : ConstitutionalPairsEnantiomorphic input.certified.detectedMultiCenterMolecule cfg
      (finalRootFrames input singleBonded center).center := by
    rw [centerEq]
    exact pairs
  have classify : ∀ {i j : Fin 4}, i ≠ j →
      (input.certified.compareLocalizedRerootCompoundRule4bcKeys
          ((finalRootFrames input singleBonded center).compounds i).prior
          ((finalRootFrames input singleBonded center).compounds j).prior = .eq ↔
        Enantiomorphic input.certified.detectedMultiCenterMolecule cfg center
          ((finalRootFrames input singleBonded center).detectedLigandPermutation i)
          ((finalRootFrames input singleBonded center).detectedLigandPermutation j)) := by
    intro i j distinct
    have law := priorTie_iff_enantiomorphic_of_pairs singleBonded charge
      (finalRootFrames input singleBonded center)
      (input.certified.localizedFinalOccurrenceExecutable_address (carrierFuel input) center)
      (finalOccurrence_provenance_real input center) distinct cfg
      (domain_final input singleBonded center cfg domain) pairs'
    rw [centerEq] at law
    exact law
  constructor
  · rintro ⟨distinct, priorEq⟩
    exact (classify distinct).mp
      (((finalRootFrames input singleBonded center).retainedActual_priorComparison
        singleBonded i j).trans ((completeLigandPriorKey_compare_eq_iff _ _).mpr priorEq))
  · intro pair
    have distinct : i ≠ j := fun same =>
      pair.1 (congrArg (finalRootFrames input singleBonded center).detectedLigandPermutation same)
    refine ⟨distinct, (completeLigandPriorKey_compare_eq_iff _ _).mp ?_⟩
    exact ((finalRootFrames input singleBonded center).retainedActual_priorComparison
      singleBonded i j).symm.trans ((classify distinct).mpr pair)

/-- **The canonical-cut prior-pair count is the physical enantiomorphic pair count**, with
arbitrary auxiliary centers. -/
theorem finalRoot_canonicalCutPairCount_eq_physicalCount_of_pairs
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : RecursiveAuxiliaryPhysicalDomain input.certified cfg center)
    (pairs : ConstitutionalPairsEnantiomorphic input.certified.detectedMultiCenterMolecule cfg
      center) :
    completeRule5PairCount (canonicalCutKeys input singleBonded center) =
      physicalEnantiomorphicPairCount input.certified.detectedMultiCenterMolecule cfg center := by
  classical
  show completeRule5PairCount (retainedContextualFrameKeysAt input.certified.moleculeGraph
      (descriptorMap input) (finalCenterUnit input center)
      ((finalRootFrames input singleBonded center).canonicalCutGraphs singleBonded)
      (finalRootFrames input singleBonded center).W
      (finalRootFrames input singleBonded center).D) = _
  rw [canonicalCutKeys_eq_retainedKeys singleBonded center,
    ← frameEnumeratedEnantiomorphicPairCount_eq input.certified.detectedMultiCenterMolecule cfg
      center (finalRootFrames input singleBonded center).detectedLigandPermutation]
  unfold completeRule5PairCount frameEnumeratedEnantiomorphicPairCount
  exact sourceEnantiomorphicPairCount_congr _ _
    (fun i j _ => finalRoot_completePriorPair_iff_enantiomorphic_of_pairs input singleBonded
      center charge cfg domain pairs i j)

/-- **Physical descriptor at a root with enantiomorphic constitutional pairs, auxiliary centers
arbitrary.** Whenever the actual report state at the evaluator's final root returns a descriptor,
`analyze` lists it, it is lowercase exactly when the physical enantiomorphic pair count is one,
and it is the classification, by that physical count, of the raw letter read in the independent
descending retained-key order, whose `R` is the physical orientation parity. -/
theorem finalRoot_physical_letter_of_pairs
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : RecursiveAuxiliaryPhysicalDomain input.certified cfg center)
    (pairs : ConstitutionalPairsEnantiomorphic input.certified.detectedMultiCenterMolecule cfg
      center)
    (geometry : RootPhysicalGeometry input.certified
      input.certified.detectedMultiCenterMolecule cfg center)
    {descriptor : LocalizedAuxiliaryLabel}
    (returned : referenceState input (finalTarget input center) = some descriptor) :
    (center.val.val, some descriptor) ∈ analyze input ∧
      (descriptor.IsLowercase ↔
        physicalEnantiomorphicPairCount input.certified.detectedMultiCenterMolecule cfg center =
          1) ∧
      ∃ (τ : Equiv.Perm (Fin 4)) (raw : RS),
        [τ 0, τ 1, τ 2, τ 3].Pairwise (fun left right =>
          canonicalCutKeys input singleBonded center right <
            canonicalCutKeys input singleBonded center left) ∧
        (raw = RS.R ↔
          permHandedness
              ((finalRootFrames input singleBonded center).detectedLigandPermutation * τ) *
            input.certified.detectedMultiCenterMolecule.configurationSign cfg center = -1) ∧
        descriptor = classifyTetrahedralRSPseudo raw
          (physicalEnantiomorphicPairCount input.certified.detectedMultiCenterMolecule cfg
            center) := by
  have count := finalRoot_canonicalCutPairCount_eq_physicalCount_of_pairs input singleBonded
    center charge cfg domain pairs
  refine ⟨LocalizedCyclicRootIndependentJudgment.finalRoot_analyze_entry returned, ?_, ?_⟩
  · rw [← count]
    exact (finalRootFrames input singleBonded center).referenceState_lowercase_iff_canonicalCut
      singleBonded returned
  · obtain ⟨points, order, raw, available, permutation, sorted, rational, descriptorEq⟩ :=
      (finalRootFrames input singleBonded center).referenceState_eq_canonicalCut_geometric_reading
        singleBonded returned
    obtain ⟨pointAt, _observed, _nonzero, calibrated, coordinates, _slotNonzero⟩ :=
      frames_coordinates singleBonded center geometry
    have pointsEq : points = fun slot => pointAt
        ((finalRootFrames input singleBonded center).detectedLigandPermutation slot) := by
      funext slot
      exact Option.some.inj ((available slot).symm.trans (coordinates slot))
    subst pointsEq
    obtain ⟨τ, orderEq⟩ := exists_perm_eq_values permutation
    subst orderEq
    refine ⟨τ, raw, sorted, rationalDescriptor_eq_R_iff_orientation calibrated
      ((finalRootFrames input singleBonded center).detectedLigandPermutation * τ) rational, ?_⟩
    rw [descriptorEq, count]

end FinalPairs

end

end TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness

assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness.rootArm_readsAgree
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness.canonicalCut_readsAgree
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness.priorTie_of_mirrorTransport
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness.retainedKeys_eq_of_readsAgree
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness.retainedKeys_eq_of_properTransport
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness.auxiliaryArm_readsAgree
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness.auxiliaryCut_readsAgree
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness.auxiliary_priorTie_of_mirror
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness.auxiliary_retainedKeys_eq_of_proper
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness.auxiliary_referenceState_none_of_proper
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness.root_mem_history
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness.outwardSlot_history
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness.transportOccurrence_fixed_of_history
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness.transportCursor_slot_of_history
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness.reached_history_inComponent
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness.signLawFrom_of_component
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness.AuxiliaryBranchTransport
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness.rootArms_rule1aTie_of_atoms
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness.auxiliary_priorTie_of_physicalMirror
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness.auxiliary_referenceState_none_of_physicalProper
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness.referenceState_none_of_properTransport
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness.finalRoot_law_of_reach
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness.finalRoot_priorTie_of_mirrorTransport
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness.finalRoot_referenceState_none_of_properTransport
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness.finalRoot_physical_descriptor_of_rigidRoot
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness.constitutionalPairsEnantiomorphic_of_rigid
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness.pairwiseProperDistinguishable_of_pairs
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness.enantiomorphic_of_priorTie_of_pairs
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness.priorTie_iff_enantiomorphic_of_pairs
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness.finalRoot_completePriorPair_iff_enantiomorphic_of_pairs
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness.finalRoot_canonicalCutPairCount_eq_physicalCount_of_pairs
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness.finalRoot_physical_letter_of_pairs
