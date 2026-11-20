import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootSuccess
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPhysicalTransport
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusCorrectionInduction
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionBalance
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionOutcomes
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRefusalCharacterization
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedEvenReadings
import TetraStereo.OneCenter.LocalizedChemicalRingPromotionAggregation
import TetraStereo.OneCenter.LocalizedChemicalRingCompletenessMarked
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000














































namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPromotionCancellation

open CertifiedLocalizedCIPInput RetainedCoherentSymmetry
open DeclarativeCIP.ProductionOccurrenceRules456
  (promotionAggregate promotionBalance promotionAggregate_eq_of_balance)
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData observedGeometry referenceAt)
open LocalizedChemicalRingJointPreparedCorrectionWitness (sideState)
open LocalizedChemicalRingJointMarkerFrameExecution (slotKeys selectedSlots selectedSlots_nonempty)
open LocalizedChemicalRingReferenceConsensusCorrectionInduction (reextend_proper)
open LocalizedChemicalRingJointPreparedRootSuccess (root_tie_sourceProper)
open LocalizedChemicalRingJointPreparedRootPhysicalTransport (root_history)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign relativeSign_eq_one_or_neg_one)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)
open LocalizedChemicalRingJointPreparedExecution (keys step step_eq fallback generated)
open LocalizedChemicalRingJointPreparedPromotionOutcomes
open LocalizedChemicalRingJointPreparedPromotionBalance
  (actualAggregate_eq_none_of_oddBoundary actualConsensus_eq_none_of_oddBoundary)
open LocalizedChemicalRingJointPreparedRefusalCharacterization (OddBoundarySymmetry)
open LocalizedChemicalRingPromotionAggregation
  (completedOutcome completedAggregate completedAggregate_of_consensus completed_balance
    readingBalance readingScore)
open LocalizedChemicalRingResidualThreeCycleRefusal (slotAction)
open LocalizedGenericMarkedRecalculation (consensus structuralDepth)

noncomputable section
open scoped Classical

/-! ## Finite cancellation algebra on actual optional readings

These lemmas are independent of the molecular model; they are the exact list algebra used by the
root results below. -/

/-- A completed reading family whose members are all `unresolved` has zero signed balance. -/
theorem readingBalance_eq_zero_of_all_none (readings : List (Option RS))
    (all : ∀ r ∈ readings, r = none) : readingBalance readings = 0 := by
  induction readings with
  | nil => rfl
  | cons head tail ih =>
      have hhead : head = none := all head (by simp)
      have htail : readingBalance tail = 0 :=
        ih (fun r member => all r (by simp [member]))
      have hstep : readingBalance (head :: tail) = readingScore head + readingBalance tail := by
        simp only [readingBalance, List.map_cons, List.sum_cons]
      rw [hstep, hhead, htail]
      simp [readingScore]

/-- A completed reading family containing one `unresolved` reading has empty consensus. -/
theorem consensus_eq_none_of_mem_none {l : List (Option RS)} {a : Option RS}
    (mem : a ∈ l) (ha : a = none) : consensus l = none := by
  have h := LocalizedChemicalRingCompletenessMarked.consensus_map_none l id a mem ha
  simpa only [List.map_id] using h

/-- A nonempty completed reading family whose members all carry the same descriptor has that
descriptor as consensus. -/
theorem consensus_eq_some_of_all_eq_some (l : List (Option RS)) (v : RS)
    (nonempty : l ≠ []) (all : ∀ r ∈ l, r = some v) : consensus l = some v := by
  have h := LocalizedChemicalRingCompletenessMarked.consensus_map_const l nonempty id v
    (fun a ha => all a ha)
  simpa only [List.map_id] using h

/-- An all-`unresolved` completed reading family aggregates to completed non-uniqueness. -/
theorem completedAggregate_eq_none_of_all_none {l : List (Option RS)}
    (all : ∀ r ∈ l, r = none) : completedAggregate l = some none := by
  have zero : readingBalance l = 0 := readingBalance_eq_zero_of_all_none l all
  simp [completedAggregate, promotionAggregate, completed_balance, zero]

/-- Uniform actual readings, as produced by a single even transport orbit, satisfy the completed
cancellation equation with no further hypothesis. -/
theorem completedAggregate_eq_consensus_of_uniform (l : List (Option RS)) (rep : Option RS)
    (nonempty : l ≠ []) (uniform : ∀ r ∈ l, r = rep) :
    completedAggregate l = some (consensus l) := by
  revert uniform
  cases rep with
  | none =>
      intro uniform
      obtain ⟨witness, member⟩ := List.exists_mem_of_ne_nil l nonempty
      have hcons : consensus l = none :=
        consensus_eq_none_of_mem_none member (uniform witness member)
      rw [hcons]
      exact completedAggregate_eq_none_of_all_none uniform
  | some v =>
      intro uniform
      have hcons : consensus l = some v :=
        consensus_eq_some_of_all_eq_some l v nonempty uniform
      rw [hcons]
      exact completedAggregate_of_consensus l v hcons

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
    ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)

/-! ## Root tie to one global proper boundary symmetry -/

include agreement admissible supported charge calibrated in
/-- An actual root key tie yields one molecular automorphism fixing the whole root history,
sending the left tied reference atom to the right one, fixing every retained reference and proper
at every center outside the root history.  No branch certificate, symmetry oracle, label
correspondence or proper-distinguishability premise is supplied. -/
theorem root_tie_boundaryProper
    (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData input mol c node) (reached : Reached mol node)
    (rootAddress : data.target.1.address = []) (_current : node.atom = c.1.val)
    (references : List input.Atom) (reflected : Bool)
    (left right : Fin 4) (distinct : left ≠ right)
    (tie : slotKeys input mol single c node data
        (sideState input mol node (inputGeometry input) references reflected) references left =
      slotKeys input mol single c node data
        (sideState input mol node (inputGeometry input) references reflected) references right) :
    ∃ symmetry : input.detectedMultiCenterMolecule.Aut,
      (∀ atom ∈ data.target.1.node.history, (symmetry : Equiv.Perm input.Atom) atom = atom) ∧
      (symmetry : Equiv.Perm input.Atom) (referenceAt input mol c node data left) =
        referenceAt input mol c node data right ∧
      (∀ reference ∈ references, (symmetry : Equiv.Perm input.Atom) reference = reference) ∧
      ∀ d : input.detectedMultiCenterMolecule.Center, d.1 ∉ data.target.1.node.history →
        relativeSign input.detectedMultiCenterMolecule cfg symmetry d = 1 := by
  obtain ⟨source, fixed, entry, refs, proper⟩ := root_tie_sourceProper input mol agreement
    admissible supported single charge cfg calibrated c node data reached rootAddress references
    reflected left right distinct tie
  have different : referenceAt input mol c node data left ≠
      referenceAt input mol c node data right := by
    intro equal
    exact distinct (data.ligandOf.injective
      (input.detectedMultiCenterMolecule.ligandAtomAt_injective c equal))
  obtain ⟨symmetry, fixedAll, _support, moved, keeps, properAll⟩ := reextend_proper input cfg
    data.target.1.node.history.reverse (referenceAt input mol c node data left)
    (referenceAt input mol c node data right) source
    (fun atom member => fixed atom (List.mem_reverse.mp member)) entry different proper
  exact ⟨symmetry, fun atom member => fixedAll atom (List.mem_reverse.mpr member), moved,
    fun reference member => keeps reference (refs reference member),
    fun d outside => properAll d (fun member => outside (List.mem_reverse.mp member))⟩

/-! ## Root odd boundary implies actual cancellation -/

include agreement admissible supported calibrated in
/-- A root odd boundary symmetry with empty boundary gives the actual fail-closed aggregate as the
actual accepted consensus.  Both the aggregate and the consensus endpoints are derived; no
refusal-to-obstruction implication is used. -/
theorem actualAggregate_eq_consensus_of_rootOddBoundary
    (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData input mol c node) (reached : Reached mol node)
    (current : node.atom = c.1.val) (rootAddress : data.target.1.address = [])
    (references : List input.Atom) (reflected : Bool)
    (obstruction : OddBoundarySymmetry input cfg c [] references) :
    promotionAggregate (actualOutcomes input mol single c node data (structuralDepth mol node)
      references reflected) =
      some (consensus (actualReadings input mol single c node data (structuralDepth mol node)
        references reflected)) := by
  have boundary : data.target.1.node.history.reverse = ([] : List input.Atom) ++ [c.1] := by
    rw [root_history input mol c node data rootAddress current]
    simp
  have outside : c.1 ∉ ([] : List input.Atom) := by simp
  have aggregate := actualAggregate_eq_none_of_oddBoundary input mol agreement admissible supported
    single cfg calibrated c node data reached current [] references boundary outside
    (structuralDepth mol node) reflected obstruction
  have cons := actualConsensus_eq_none_of_oddBoundary input mol agreement admissible supported
    single cfg calibrated c node data reached current [] references boundary outside
    (structuralDepth mol node) reflected obstruction
  rw [aggregate, cons]

include agreement admissible supported calibrated in
/-- The raw descriptor step form of the root odd-boundary cancellation on noninjective actual
keys. -/
theorem actualAggregate_eq_step_of_rootOddBoundary
    (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData input mol c node) (reached : Reached mol node)
    (current : node.atom = c.1.val) (rootAddress : data.target.1.address = [])
    (references : List input.Atom) (reflected : Bool)
    (tied : ¬ Function.Injective (keys input mol single c node data (structuralDepth mol node)
      (observedGeometry input reflected) references))
    (obstruction : OddBoundarySymmetry input cfg c [] references) :
    promotionAggregate (actualOutcomes input mol single c node data (structuralDepth mol node)
      references reflected) =
      some (step input mol node (structuralDepth mol node) (observedGeometry input reflected)
        references) := by
  rw [step_eq input mol agreement admissible supported single c node data, if_neg tied]
  exact actualAggregate_eq_consensus_of_rootOddBoundary input mol agreement admissible supported
    single cfg calibrated c node data reached current rootAddress references reflected obstruction

/-! ## Root tie dichotomy: actual cancellation or an even boundary tie -/

include agreement admissible supported charge calibrated in
/-- Every actual root key tie either already satisfies the desired actual cancellation equation,
or is carried by an even boundary symmetry fixing the whole root history and every retained
reference.  The odd branch is solved outright; the even branch is the precise residual shape. -/
theorem actualAggregate_eq_consensus_or_rootEvenTie
    (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData input mol c node) (reached : Reached mol node)
    (current : node.atom = c.1.val) (rootAddress : data.target.1.address = [])
    (references : List input.Atom) (reflected : Bool)
    (left right : Fin 4) (distinct : left ≠ right)
    (tie : slotKeys input mol single c node data
        (sideState input mol node (inputGeometry input) references reflected) references left =
      slotKeys input mol single c node data
        (sideState input mol node (inputGeometry input) references reflected) references right) :
    (promotionAggregate (actualOutcomes input mol single c node data (structuralDepth mol node)
        references reflected) =
      some (consensus (actualReadings input mol single c node data (structuralDepth mol node)
        references reflected))) ∨
    ∃ symmetry : input.detectedMultiCenterMolecule.Aut,
      (∀ atom ∈ data.target.1.node.history, (symmetry : Equiv.Perm input.Atom) atom = atom) ∧
      (symmetry : Equiv.Perm input.Atom) (referenceAt input mol c node data left) =
        referenceAt input mol c node data right ∧
      (∀ reference ∈ references, (symmetry : Equiv.Perm input.Atom) reference = reference) ∧
      (∀ d : input.detectedMultiCenterMolecule.Center, d.1 ∉ data.target.1.node.history →
        relativeSign input.detectedMultiCenterMolecule cfg symmetry d = 1) ∧
      relativeSign input.detectedMultiCenterMolecule cfg symmetry c = 1 := by
  obtain ⟨symmetry, fixed, moved, keeps, proper⟩ :=
    root_tie_boundaryProper input mol agreement admissible supported single charge cfg calibrated
      c node data reached rootAddress current references reflected left right distinct tie
  rcases relativeSign_eq_one_or_neg_one input.detectedMultiCenterMolecule cfg symmetry c with
    even | odd
  · exact Or.inr ⟨symmetry, fixed, moved, keeps, proper, even⟩
  · refine Or.inl ?_
    have obstruction : OddBoundarySymmetry input cfg c [] references := by
      refine ⟨symmetry, ?_, ?_, odd, ?_⟩
      · intro atom member
        have eq : atom = c.1 := by simpa using member
        rw [eq]
        exact fixed c.1 (by
          rw [root_history input mol c node data rootAddress current]
          simp)
      · intro atom member
        exact keeps atom member
      · intro d outside
        have different : d.1 ≠ c.1 := by simpa using outside
        exact proper d (by
          rw [root_history input mol c node data rootAddress current]
          simpa using different)
    exact actualAggregate_eq_consensus_of_rootOddBoundary input mol agreement admissible supported
      single cfg calibrated c node data reached current rootAddress references reflected obstruction

/-! ## Even root transport of actual fallbacks -/

include agreement admissible supported single calibrated in
/-- An even root boundary symmetry fixing the history and every retained reference leaves each
actual extended-context fallback invariant under its slot action.  Only the root history is used
as the boundary, so no incoming-parent atom and no branch certificate is needed. -/
theorem root_even_fallback_action
    (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData input mol c node) (reached : Reached mol node)
    (current : node.atom = c.1.val) (rootAddress : data.target.1.address = [])
    (references : List input.Atom)
    (e : input.detectedMultiCenterMolecule.Aut)
    (historyFixed : ∀ atom ∈ data.target.1.node.history,
      (e : Equiv.Perm input.Atom) atom = atom)
    (marksFixed : ∀ atom ∈ references, (e : Equiv.Perm input.Atom) atom = atom)
    (properOff : ∀ d : input.detectedMultiCenterMolecule.Center,
      d.1 ∉ data.target.1.node.history →
        relativeSign input.detectedMultiCenterMolecule cfg e d = 1)
    (even : relativeSign input.detectedMultiCenterMolecule cfg e c = 1)
    (depth : Nat) (reflected : Bool) (slot : Fin 4) :
    fallback input mol c node data depth (observedGeometry input reflected) references
        (slotAction input mol e c node data slot) =
      fallback input mol c node data depth (observedGeometry input reflected) references slot := by
  exact LocalizedChemicalRingJointPreparedEvenReadings.fallback_action input mol agreement
    admissible supported single cfg calibrated c node data reached current e historyFixed
    references marksFixed [] (by simp) (by simp)
    (fun d _ different => properOff d (by
      rw [root_history input mol c node data rootAddress current]
      simpa using different))
    even depth reflected slot

/-! ## Uniform actual readings cancel -/

include agreement admissible supported calibrated in
/-- If every actual selected fallback has the same optional reading, the actual fail-closed
aggregate equals the actual accepted consensus.  This is the endpoint of a single even transport
orbit and needs no key-correspondence, symmetry or branch hypothesis. The noninjective-key
premise supplies the nonempty selected population. -/
theorem actualAggregate_eq_consensus_of_uniform_readings
    (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData input mol c node) (depth : Nat) (references : List input.Atom)
    (reflected : Bool)
    (tied : ¬ Function.Injective (keys input mol single c node data depth
      (observedGeometry input reflected) references))
    (rep : Option RS)
    (uniform : ∀ slot, slot ∈ selectedSlots input mol single c node data
        (generated input mol depth (observedGeometry input reflected) node references)
        references →
      fallback input mol c node data depth (observedGeometry input reflected) references slot =
        rep) :
    promotionAggregate (actualOutcomes input mol single c node data depth references reflected) =
      some (consensus (actualReadings input mol single c node data depth references reflected)) := by
  rw [actualAggregate_eq_completed input mol single c node data depth references reflected
    agreement admissible supported cfg (calibrated c)]
  refine completedAggregate_eq_consensus_of_uniform
    (actualReadings input mol single c node data depth references reflected) rep ?_ ?_
  · intro empty
    have selectedNil : selectedSlots input mol single c node data
        (generated input mol depth (observedGeometry input reflected) node references) references = [] := by
      simpa only [actualReadings, List.map_eq_nil_iff] using empty
    exact selectedSlots_nonempty input mol single c node data
      (generated input mol depth (observedGeometry input reflected) node references) references
      tied selectedNil
  · intro r member
    have mapped : r ∈ (selectedSlots input mol single c node data
        (generated input mol depth (observedGeometry input reflected) node references)
        references).map
        (fallback input mol c node data depth (observedGeometry input reflected) references) := by
      simpa only [actualReadings] using member
    obtain ⟨slot, slotMember, rfl⟩ := List.mem_map.mp mapped
    exact uniform slot slotMember

include agreement admissible supported calibrated in
/-- The raw descriptor step form of uniform-reading cancellation on noninjective actual keys. -/
theorem actualAggregate_eq_step_of_uniform_readings
    (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData input mol c node) (depth : Nat) (references : List input.Atom)
    (reflected : Bool)
    (tied : ¬ Function.Injective (keys input mol single c node data depth
      (observedGeometry input reflected) references))
    (rep : Option RS)
    (uniform : ∀ slot, slot ∈ selectedSlots input mol single c node data
        (generated input mol depth (observedGeometry input reflected) node references)
        references →
      fallback input mol c node data depth (observedGeometry input reflected) references slot =
        rep) :
    promotionAggregate (actualOutcomes input mol single c node data depth references reflected) =
      some (step input mol node depth (observedGeometry input reflected) references) := by
  rw [step_eq input mol agreement admissible supported single c node data, if_neg tied]
  exact actualAggregate_eq_consensus_of_uniform_readings input mol agreement admissible supported
    single cfg calibrated c node data depth references reflected tied rep uniform

/-! ## Root one-orbit realization -/

include agreement admissible supported calibrated in
/-- Root one-orbit realization: if every two actual selected slots are related by an even
boundary symmetry that fixes the whole root history, fixes every retained reference and is proper
at every center outside that history, then the actual fail-closed aggregate equals the actual
accepted consensus.  In a four-way or three-way root tie this hypothesis is discharged by the
actual tie symmetries themselves once the odd branch is excluded; in a two-pair root with two
distinct classes it is not, and that is the stated residual gap. -/
theorem actualAggregate_eq_consensus_of_rootEvenConnected
    (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData input mol c node) (reached : Reached mol node)
    (current : node.atom = c.1.val) (rootAddress : data.target.1.address = [])
    (references : List input.Atom) (reflected : Bool)
    (tied : ¬ Function.Injective (keys input mol single c node data (structuralDepth mol node)
      (observedGeometry input reflected) references))
    (connected : ∀ i, i ∈ selectedSlots input mol single c node data
        (generated input mol (structuralDepth mol node) (observedGeometry input reflected)
          node references) references →
      ∀ j, j ∈ selectedSlots input mol single c node data
        (generated input mol (structuralDepth mol node) (observedGeometry input reflected)
          node references) references →
      ∃ e : input.detectedMultiCenterMolecule.Aut,
        (∀ atom ∈ data.target.1.node.history, (e : Equiv.Perm input.Atom) atom = atom) ∧
        (∀ atom ∈ references, (e : Equiv.Perm input.Atom) atom = atom) ∧
        (∀ d : input.detectedMultiCenterMolecule.Center, d.1 ∉ data.target.1.node.history →
          relativeSign input.detectedMultiCenterMolecule cfg e d = 1) ∧
        relativeSign input.detectedMultiCenterMolecule cfg e c = 1 ∧
        slotAction input mol e c node data i = j) :
    promotionAggregate (actualOutcomes input mol single c node data (structuralDepth mol node)
      references reflected) =
      some (consensus (actualReadings input mol single c node data (structuralDepth mol node)
        references reflected)) := by
  obtain ⟨repSlot, repMember⟩ := List.exists_mem_of_ne_nil _
    (selectedSlots_nonempty input mol single c node data
      (generated input mol (structuralDepth mol node) (observedGeometry input reflected)
        node references) references tied)
  apply actualAggregate_eq_consensus_of_uniform_readings input mol agreement admissible supported
    single cfg calibrated c node data (structuralDepth mol node) references reflected tied
    (fallback input mol c node data (structuralDepth mol node) (observedGeometry input reflected)
      references repSlot)
  intro slot member
  obtain ⟨e, historyFixed, marksFixed, properOff, even, action⟩ :=
    connected slot member repSlot repMember
  have transported := root_even_fallback_action input mol agreement admissible supported single cfg
    calibrated c node data reached current rootAddress references e historyFixed marksFixed properOff
    even (structuralDepth mol node) reflected slot
  rw [action] at transported
  exact transported.symm

include agreement admissible supported calibrated in
/-- The raw descriptor step form of root one-orbit cancellation on noninjective actual keys. -/
theorem actualAggregate_eq_step_of_rootEvenConnected
    (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData input mol c node) (reached : Reached mol node)
    (current : node.atom = c.1.val) (rootAddress : data.target.1.address = [])
    (references : List input.Atom) (reflected : Bool)
    (tied : ¬ Function.Injective (keys input mol single c node data (structuralDepth mol node)
      (observedGeometry input reflected) references))
    (connected : ∀ i, i ∈ selectedSlots input mol single c node data
        (generated input mol (structuralDepth mol node) (observedGeometry input reflected)
          node references) references →
      ∀ j, j ∈ selectedSlots input mol single c node data
        (generated input mol (structuralDepth mol node) (observedGeometry input reflected)
          node references) references →
      ∃ e : input.detectedMultiCenterMolecule.Aut,
        (∀ atom ∈ data.target.1.node.history, (e : Equiv.Perm input.Atom) atom = atom) ∧
        (∀ atom ∈ references, (e : Equiv.Perm input.Atom) atom = atom) ∧
        (∀ d : input.detectedMultiCenterMolecule.Center, d.1 ∉ data.target.1.node.history →
          relativeSign input.detectedMultiCenterMolecule cfg e d = 1) ∧
        relativeSign input.detectedMultiCenterMolecule cfg e c = 1 ∧
        slotAction input mol e c node data i = j) :
    promotionAggregate (actualOutcomes input mol single c node data (structuralDepth mol node)
      references reflected) =
      some (step input mol node (structuralDepth mol node) (observedGeometry input reflected)
        references) := by
  rw [step_eq input mol agreement admissible supported single c node data, if_neg tied]
  exact actualAggregate_eq_consensus_of_rootEvenConnected input mol agreement admissible supported
    single cfg calibrated c node data reached current rootAddress references reflected tied
    connected

/-! ## Exact residual reduction -/

include agreement admissible supported calibrated in
/-- The remaining root obligation is exactly the signed reading balance on consensus refusal: with
that premise the actual fail-closed aggregate is the actual consensus, on either geometry side and
every retained reference list, at any occurrence depth. -/
theorem actualAggregate_eq_consensus_of_rootBalanced
    (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData input mol c node) (depth : Nat) (references : List input.Atom)
    (reflected : Bool)
    (balanced : consensus (actualReadings input mol single c node data depth references reflected) =
        none →
      readingBalance (actualReadings input mol single c node data depth references reflected) = 0) :
    promotionAggregate (actualOutcomes input mol single c node data depth references reflected) =
      some (consensus (actualReadings input mol single c node data depth references reflected)) := by
  rw [actualAggregate_eq_completed input mol single c node data depth references reflected
    agreement admissible supported cfg (calibrated c)]
  cases hc : consensus (actualReadings input mol single c node data depth references reflected) with
  | none =>
      have hb : readingBalance
          (actualReadings input mol single c node data depth references reflected) = 0 :=
        balanced hc
      have hbalance : promotionBalance
          ((actualReadings input mol single c node data depth references reflected).map
            completedOutcome) = some 0 := by
        rw [completed_balance, hb]
      change promotionAggregate
        ((actualReadings input mol single c node data depth references reflected).map
          completedOutcome) = some none
      rw [promotionAggregate_eq_of_balance _ 0 hbalance]
      simp
  | some descriptor =>
      exact completedAggregate_of_consensus
        (actualReadings input mol single c node data depth references reflected) descriptor hc

include agreement admissible supported calibrated in
/-- The raw descriptor step form of the signed-balance reduction on noninjective actual keys. -/
theorem actualAggregate_eq_step_of_rootBalanced
    (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData input mol c node) (depth : Nat) (references : List input.Atom)
    (reflected : Bool)
    (tied : ¬ Function.Injective (keys input mol single c node data depth
      (observedGeometry input reflected) references))
    (balanced : consensus (actualReadings input mol single c node data depth references reflected) =
        none →
      readingBalance (actualReadings input mol single c node data depth references reflected) = 0) :
    promotionAggregate (actualOutcomes input mol single c node data depth references reflected) =
      some (step input mol node depth (observedGeometry input reflected) references) := by
  rw [step_eq input mol agreement admissible supported single c node data, if_neg tied]
  exact actualAggregate_eq_consensus_of_rootBalanced input mol agreement admissible supported
    single cfg calibrated c node data depth references reflected balanced

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPromotionCancellation

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPromotionCancellation.readingBalance_eq_zero_of_all_none
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPromotionCancellation.consensus_eq_none_of_mem_none
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPromotionCancellation.consensus_eq_some_of_all_eq_some
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPromotionCancellation.completedAggregate_eq_none_of_all_none
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPromotionCancellation.completedAggregate_eq_consensus_of_uniform
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPromotionCancellation.root_tie_boundaryProper
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPromotionCancellation.actualAggregate_eq_consensus_of_rootOddBoundary
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPromotionCancellation.actualAggregate_eq_step_of_rootOddBoundary
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPromotionCancellation.actualAggregate_eq_consensus_or_rootEvenTie
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPromotionCancellation.root_even_fallback_action
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPromotionCancellation.actualAggregate_eq_consensus_of_uniform_readings
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPromotionCancellation.actualAggregate_eq_step_of_uniform_readings
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPromotionCancellation.actualAggregate_eq_consensus_of_rootEvenConnected
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPromotionCancellation.actualAggregate_eq_step_of_rootEvenConnected
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPromotionCancellation.actualAggregate_eq_consensus_of_rootBalanced
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPromotionCancellation.actualAggregate_eq_step_of_rootBalanced
