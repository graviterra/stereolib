import TetraStereo.OneCenter.SmilesTetrahedral
import TetraStereo.OneCenter.LocalizedOccurrenceExecutableRoots
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.AuxiliaryContextIntegrity






























































/-! ## The localized typed read surface -/

/-- A localized dependency fixes the same root for source and target. -/
theorem localizedDepthDependency_sameRoot
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    {source target : input.LocalizedCIPOccurrence fuel}
    (dependency : input.LocalizedDepthDependency source target) :
    source.1.root = target.1.root :=
  dependency.1

/-- A localized dependency is strictly deeper than its target. -/
theorem localizedDepthDependency_strictlyDeeper
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    {source target : input.LocalizedCIPOccurrence fuel}
    (dependency : input.LocalizedDepthDependency source target) :
    target.1.address.length < source.1.address.length :=
  dependency.2

/-- The localized dependency view returns the state entry at the exact source occurrence.  It does
not project to an atom and does not rebuild an occurrence from the target. -/
theorem localizedDependencyView_read_eq
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel)
    (target source : input.LocalizedCIPOccurrence fuel)
    (dependency : input.LocalizedDepthDependency source target) :
    input.localizedDependencyView state target source dependency = state source := rfl

/-- A localized read retains, simultaneously, the exact occurrence entry, the target's context
root, and the strict-deeper address condition. -/
theorem localizedDependencyView_read_retains_context
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel)
    (target source : input.LocalizedCIPOccurrence fuel)
    (dependency : input.LocalizedDepthDependency source target) :
    source.1.root = target.1.root ∧
      target.1.address.length < source.1.address.length ∧
      input.localizedDependencyView state target source dependency = state source :=
  ⟨dependency.1, dependency.2, rfl⟩

/-- The noncomputable final occurrence's root is the detected center.  The proof routes through
the executable twin, so it does not unfold the `classical` definition. -/
theorem localizedFinalOccurrence_root
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (center : input.TetrahedralCenter) :
    (input.localizedFinalOccurrence fuel center).1.root = center.val := by
  rw [← input.localizedFinalOccurrenceExecutable_eq_localizedFinalOccurrence fuel center]
  exact input.localizedFinalOccurrenceExecutable_root fuel center

/-- The final occurrence is the distinguished root occurrence: its address is empty. -/
theorem localizedFinalOccurrence_address
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (center : input.TetrahedralCenter) :
    (input.localizedFinalOccurrence fuel center).1.address = [] := by
  rw [← input.localizedFinalOccurrenceExecutable_eq_localizedFinalOccurrence fuel center]
  exact input.localizedFinalOccurrenceExecutable_address fuel center

/-- The final occurrence carries the official root node. -/
theorem localizedFinalOccurrence_node
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (center : input.TetrahedralCenter) :
    (input.localizedFinalOccurrence fuel center).1.node =
      OfficialCIPNode.root center.val := by
  rw [← input.localizedFinalOccurrenceExecutable_eq_localizedFinalOccurrence fuel center]
  exact input.localizedFinalOccurrenceExecutable_node fuel center

/-- The final occurrence retains the full remaining-depth budget. -/
theorem localizedFinalOccurrence_remaining
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (center : input.TetrahedralCenter) :
    (input.localizedFinalOccurrence fuel center).1.remaining = fuel + 1 := by
  rw [← input.localizedFinalOccurrenceExecutable_eq_localizedFinalOccurrence fuel center]
  exact input.localizedFinalOccurrenceExecutable_remaining fuel center

/-- Every legal read under the final occurrence has the detected center as its context root. -/
theorem localizedDependencyView_finalTarget_sameRoot
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (_state : input.LocalizedAuxiliaryState fuel)
    (center : input.TetrahedralCenter)
    (source : input.LocalizedCIPOccurrence fuel)
    (dependency : input.LocalizedDepthDependency source
      (input.localizedFinalOccurrence fuel center)) :
    source.1.root = center.val := by
  rw [← localizedFinalOccurrence_root input fuel center]
  exact dependency.1

/-- Every legal read under the final root is a strictly deeper, non-root occurrence. -/
theorem localizedDependencyView_finalTarget_positiveAddress
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (_state : input.LocalizedAuxiliaryState fuel)
    (center : input.TetrahedralCenter)
    (source : input.LocalizedCIPOccurrence fuel)
    (dependency : input.LocalizedDepthDependency source
      (input.localizedFinalOccurrence fuel center)) :
    source.1.address ≠ [] := by
  have hlen := dependency.2
  rw [localizedFinalOccurrence_address input fuel center, List.length_nil] at hlen
  intro hempty
  rw [hempty, List.length_nil] at hlen
  exact Nat.lt_irrefl 0 hlen

/-! ## Occurrence keys versus atom keys -/

/-- The production occurrence key is exactly the pair of path history and provenance.  In
particular the node's `atom` and `parent` fields are not part of the key; the atom is recovered
separately by the occurrence fact constructor. -/
theorem canonicalOccurrenceKey_eq_iff
    {left right : RawMolecule.CanonicalBranchNode} :
    canonicalOccurrenceKey left = canonicalOccurrenceKey right ↔
      left.history = right.history ∧ left.provenance = right.provenance := by
  constructor
  · intro h
    exact ⟨congrArg CanonicalOccurrenceKey.history h,
      congrArg CanonicalOccurrenceKey.provenance h⟩
  · rintro ⟨hhistory, hprovenance⟩
    cases left
    cases right
    dsimp only [canonicalOccurrenceKey] at hhistory hprovenance ⊢
    rw [hhistory, hprovenance]

/-- When the documented invariant `history.head? = some atom` holds, the occurrence key determines
the atom.  The invariant is what production construction maintains; the key itself stores only the
history and provenance. -/
theorem canonicalOccurrenceKey_atom_eq_of_history_head
    {left right : RawMolecule.CanonicalBranchNode}
    (hkey : canonicalOccurrenceKey left = canonicalOccurrenceKey right)
    (hleft : left.history.head? = some left.atom)
    (hright : right.history.head? = some right.atom) :
    left.atom = right.atom := by
  have hhistory : left.history = right.history :=
    (canonicalOccurrenceKey_eq_iff.mp hkey).1
  have hhead : left.history.head? = right.history.head? := by rw [hhistory]
  exact Option.some.inj (hleft.symm.trans (hhead.trans hright))

/-- The center-root occurrence used by the authoritative evaluator. -/
def contextRootNode : RawMolecule.CanonicalBranchNode :=
  { atom := 0, parent := 0, history := [0],
    provenance := RawMolecule.CanonicalNodeProvenance.realAtom }

/-- The same atom reached by one more step, so the history differs. -/
def contextReturnNode : RawMolecule.CanonicalBranchNode :=
  { atom := 0, parent := 0, history := [0, 0],
    provenance := RawMolecule.CanonicalNodeProvenance.realAtom }

/-- The same atom with the same history but a ring-duplicate provenance. -/
def contextDuplicateNode : RawMolecule.CanonicalBranchNode :=
  { atom := 0, parent := 0, history := [0],
    provenance := RawMolecule.CanonicalNodeProvenance.ringDuplicate 0 }

theorem contextRootNode_atom_eq_return :
    contextRootNode.atom = contextReturnNode.atom := rfl

theorem contextRootNode_atom_eq_duplicate :
    contextRootNode.atom = contextDuplicateNode.atom := rfl

theorem contextRootNode_history_ne_return :
    contextRootNode.history ≠ contextReturnNode.history := by
  intro h
  simp only [contextRootNode, contextReturnNode] at h
  have htail : ([] : List Nat) = [0] := List.tail_eq_of_cons_eq h
  exact List.cons_ne_nil 0 ([] : List Nat) htail.symm

theorem contextRootNode_provenance_ne_duplicate :
    contextRootNode.provenance ≠ contextDuplicateNode.provenance := by
  intro h
  simp only [contextRootNode, contextDuplicateNode] at h
  cases h

/-- Two occurrences of one atom with different path histories have different occurrence keys. -/
theorem contextRootNode_key_ne_return :
    canonicalOccurrenceKey contextRootNode ≠ canonicalOccurrenceKey contextReturnNode := by
  intro h
  exact contextRootNode_history_ne_return (canonicalOccurrenceKey_eq_iff.mp h).1

/-- Two occurrences with the same path history but different provenance have different
occurrence keys.  This is the ring-duplicate distinction that an atom-keyed state erases. -/
theorem contextRootNode_key_ne_duplicate :
    canonicalOccurrenceKey contextRootNode ≠ canonicalOccurrenceKey contextDuplicateNode := by
  intro h
  exact contextRootNode_provenance_ne_duplicate (canonicalOccurrenceKey_eq_iff.mp h).2

/-- An occurrence-state lookup is key-verified and the returned fact is a member of the state. -/
theorem occurrenceAuxState_factAt?_key_and_mem
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (fact : OccurrenceAuxFact)
    (found : OccurrenceAuxState.factAt? state node = some fact) :
    fact.key = canonicalOccurrenceKey node ∧ fact ∈ state := by
  unfold OccurrenceAuxState.factAt? at found
  have hpred : (fact.key == canonicalOccurrenceKey node) = true :=
    List.find?_some
      (p := fun (entry : OccurrenceAuxFact) => entry.key == canonicalOccurrenceKey node) found
  have hmem : fact ∈ state :=
    List.mem_of_find?_eq_some
      (p := fun (entry : OccurrenceAuxFact) => entry.key == canonicalOccurrenceKey node) found
  exact ⟨eq_of_beq hpred, hmem⟩

/-- The molecule-global descriptor state, by contrast, is keyed by the atom alone. -/
theorem rawDescriptorState_factAt?_atom
    (state : RawDescriptorState) (atom : Nat) (fact : RawDescriptorFact)
    (found : RawDescriptorState.factAt? state atom = some fact) :
    fact.atom = atom := by
  unfold RawDescriptorState.factAt? at found
  exact eq_of_beq
    (List.find?_some (p := fun (entry : RawDescriptorFact) => entry.atom == atom) found)

/-! ## The authoritative occurrence fact pins its key and atom -/

theorem legacyOccurrenceFactAuthoritative?_key_atom (mol : RawMolecule) (fuel : Nat)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (fact : OccurrenceAuxFact)
    (computed : legacyOccurrenceFactAuthoritative? mol fuel state node = some fact) :
    fact.key = canonicalOccurrenceKey node ∧ fact.atom = node.atom := by
  unfold legacyOccurrenceFactAuthoritative? at computed
  dsimp only [Bind.bind] at computed
  simp only [Option.bind_eq_some_iff] at computed
  rcases computed with ⟨spec, -, parity, -, roots, -, sorted, -, positions, -, decisions, -, hfinal⟩
  split at hfinal
  · simp at hfinal
  · have hfact := Option.some.inj hfinal
    subst fact
    exact ⟨rfl, rfl⟩

theorem framedOccurrenceFactAuthoritative?_key_atom (mol : RawMolecule) (fuel : Nat)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (fact : OccurrenceAuxFact)
    (computed : framedOccurrenceFactAuthoritative? mol fuel state node = some fact) :
    fact.key = canonicalOccurrenceKey node ∧ fact.atom = node.atom := by
  unfold framedOccurrenceFactAuthoritative? at computed
  dsimp only [Bind.bind] at computed
  simp only [Option.bind_eq_some_iff] at computed
  rcases computed with
    ⟨profile, -, spec, -, parity, -, roots, -, sorted, -, positions, -, decisions, -, hfinal⟩
  split at hfinal
  · simp at hfinal
  · have hfact := Option.some.inj hfinal
    subst fact
    exact ⟨rfl, rfl⟩

theorem occurrenceFactAuthoritative?_key_atom (mol : RawMolecule) (fuel : Nat)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (fact : OccurrenceAuxFact)
    (computed : occurrenceFactAuthoritative? mol fuel state node = some fact) :
    fact.key = canonicalOccurrenceKey node ∧ fact.atom = node.atom := by
  cases hprofile : FrameRuntime.profile? mol node with
  | none =>
      have hlegacy : legacyOccurrenceFactAuthoritative? mol fuel state node = some fact := by
        simpa only [occurrenceFactAuthoritative?, hprofile] using computed
      exact legacyOccurrenceFactAuthoritative?_key_atom mol fuel state node fact hlegacy
  | some profile =>
      have hframed : framedOccurrenceFactAuthoritative? mol fuel state node = some fact := by
        simpa only [occurrenceFactAuthoritative?, hprofile] using computed
      exact framedOccurrenceFactAuthoritative?_key_atom mol fuel state node fact hframed

/-- Legacy non-authoritative evaluator: the constructor still labels the node's own occurrence key
and atom. -/
theorem legacyOccurrenceFact?_key_atom (mol : RawMolecule) (fuel : Nat)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (fact : OccurrenceAuxFact)
    (computed : legacyOccurrenceFact? mol fuel state node = some fact) :
    fact.key = canonicalOccurrenceKey node ∧ fact.atom = node.atom := by
  unfold legacyOccurrenceFact? at computed
  dsimp only [Bind.bind] at computed
  simp only [Option.bind_eq_some_iff] at computed
  rcases computed with ⟨spec, -, parity, -, roots, -, sorted, -, positions, -, compared, -, hfinal⟩
  split at hfinal
  · simp at hfinal
  · have hfact := Option.some.inj hfinal
    subst fact
    exact ⟨rfl, rfl⟩

theorem framedOccurrenceFact?_key_atom (mol : RawMolecule) (fuel : Nat)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (fact : OccurrenceAuxFact)
    (computed : framedOccurrenceFact? mol fuel state node = some fact) :
    fact.key = canonicalOccurrenceKey node ∧ fact.atom = node.atom := by
  unfold framedOccurrenceFact? at computed
  dsimp only [Bind.bind] at computed
  simp only [Option.bind_eq_some_iff] at computed
  rcases computed with
    ⟨profile, -, spec, -, parity, -, roots, -, sorted, -, positions, -, compared, -, hfinal⟩
  split at hfinal
  · simp at hfinal
  · have hfact := Option.some.inj hfinal
    subst fact
    exact ⟨rfl, rfl⟩

theorem occurrenceFact?_key_atom (mol : RawMolecule) (fuel : Nat)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (fact : OccurrenceAuxFact)
    (computed : occurrenceFact? mol fuel state node = some fact) :
    fact.key = canonicalOccurrenceKey node ∧ fact.atom = node.atom := by
  cases hprofile : FrameRuntime.profile? mol node with
  | none =>
      have hlegacy : legacyOccurrenceFact? mol fuel state node = some fact := by
        simpa only [occurrenceFact?, hprofile] using computed
      exact legacyOccurrenceFact?_key_atom mol fuel state node fact hlegacy
  | some profile =>
      have hframed : framedOccurrenceFact? mol fuel state node = some fact := by
        simpa only [occurrenceFact?, hprofile] using computed
      exact framedOccurrenceFact?_key_atom mol fuel state node fact hframed

/-- The authoritative public fact is obtained by one state build and one occurrence-local read.
The returned fact records exactly the occurrence's descriptor, case bit, and priority positions,
and the occurrence key is the fixed center-root key. -/
theorem tetrahedralOccurrenceFactAuthoritative?_exact_read
    (mol : RawMolecule) (fuel center : Nat) (fact : RawDescriptorFact)
    (computed : tetrahedralOccurrenceFactAuthoritative? mol fuel center = some fact) :
    ∃ (state : OccurrenceAuxState) (occurrence : OccurrenceAuxFact),
      buildOccurrenceAuxStateFullyAuthoritative? mol fuel center = some state ∧
      occurrenceFactAuthoritative? mol fuel state (canonicalCenterRoot center) = some occurrence ∧
      occurrence.key = canonicalOccurrenceKey (canonicalCenterRoot center) ∧
      occurrence.atom = center ∧
      fact = { atom := center
               descriptor := occurrence.descriptor
               uppercase := occurrence.uppercase
               evidenceSize := max 1 state.length
               decisiveRule? := none
               descriptorDependentPairs := state.length
               priorityPositions := occurrence.priorityPositions } := by
  unfold tetrahedralOccurrenceFactAuthoritative? at computed
  dsimp only [Bind.bind] at computed
  simp only [Option.bind_eq_some_iff] at computed
  rcases computed with ⟨state, hstate, occurrence, hoccur, hfinal⟩
  have hfact := Option.some.inj hfinal
  subst fact
  have hkey := (occurrenceFactAuthoritative?_key_atom mol fuel state
    (canonicalCenterRoot center) occurrence hoccur).1
  have hatom := (occurrenceFactAuthoritative?_key_atom mol fuel state
    (canonicalCenterRoot center) occurrence hoccur).2
  exact ⟨state, occurrence, hstate, hoccur, hkey,
    by simpa [canonicalCenterRoot] using hatom, rfl⟩

/-- The public routing entry point is definitionally the authoritative one, so the exact-read
theorem applies without any additional assumption. -/
theorem tetrahedralOccurrenceFact?_exact_read
    (mol : RawMolecule) (fuel center : Nat) (fact : RawDescriptorFact)
    (computed : tetrahedralOccurrenceFact? mol fuel center = some fact) :
    ∃ (state : OccurrenceAuxState) (occurrence : OccurrenceAuxFact),
      buildOccurrenceAuxStateFullyAuthoritative? mol fuel center = some state ∧
      occurrenceFactAuthoritative? mol fuel state (canonicalCenterRoot center) = some occurrence ∧
      occurrence.key = canonicalOccurrenceKey (canonicalCenterRoot center) ∧
      occurrence.atom = center ∧
      fact = { atom := center
               descriptor := occurrence.descriptor
               uppercase := occurrence.uppercase
               evidenceSize := max 1 state.length
               decisiveRule? := none
               descriptorDependentPairs := state.length
               priorityPositions := occurrence.priorityPositions } := by
  unfold tetrahedralOccurrenceFact? at computed
  exact tetrahedralOccurrenceFactAuthoritative?_exact_read mol fuel center fact computed

/-! ## How the priority reads use the stored descriptor -/

/-- The occurrence-local priority path reads the key-verified occurrence fact and uses that
fact's own descriptor and case bit.  No molecule-global fact is substituted. -/
theorem occurrenceNodePriority_realAtom
    (state : OccurrenceAuxState) (stage : RawDescriptorRuleStage) (leftSide : Bool)
    (cursor : CanonicalRerootCursor) (fact : OccurrenceAuxFact)
    (provenance : cursor.node.provenance =
      RawMolecule.CanonicalNodeProvenance.realAtom)
    (found : OccurrenceAuxState.factAt? state cursor.node = some fact) :
    occurrenceNodePriority state stage leftSide cursor =
      match stage with
      | RawDescriptorRuleStage.rule4a => if fact.uppercase then 2 else 1
      | RawDescriptorRuleStage.rule4b leftReference rightReference =>
          let reference := if leftSide then leftReference else rightReference
          if fact.uppercase && fact.descriptor == reference then 1 else 0
      | RawDescriptorRuleStage.rule4c =>
          if fact.uppercase then 0 else if fact.descriptor == RS.R then 2 else 1
      | RawDescriptorRuleStage.rule5 leftReference rightReference =>
          let reference := if leftSide then leftReference else rightReference
          if fact.uppercase && fact.descriptor == reference then 1 else 0 := by
  cases stage <;> simp only [occurrenceNodePriority, provenance, found]

/-- The raw atom-keyed path still looks the fact up by atom, but replaces its stored sense with
the occurrence-local sense before using the descriptor in Rules 4b, 4c, and 5. -/
theorem rawDescriptorNodePriority_realAtom
    (mol : RawMolecule) (state : RawDescriptorState)
    (stage : RawDescriptorRuleStage) (leftSide : Bool)
    (node : RawMolecule.CanonicalBranchNode) (fact : RawDescriptorFact)
    (provenance : node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (found : RawDescriptorState.factAt? state node.atom = some fact) :
    rawDescriptorNodePriority mol state stage leftSide node =
      match stage with
      | RawDescriptorRuleStage.rule4a => if fact.uppercase then 2 else 1
      | RawDescriptorRuleStage.rule4b leftReference rightReference =>
          let reference := if leftSide then leftReference else rightReference
          if fact.uppercase && rawAuxiliaryOccurrenceSense mol node fact == reference then
            1
          else 0
      | RawDescriptorRuleStage.rule4c =>
          if fact.uppercase then 0
          else if rawAuxiliaryOccurrenceSense mol node fact == RS.R then 2 else 1
      | RawDescriptorRuleStage.rule5 leftReference rightReference =>
          let reference := if leftSide then leftReference else rightReference
          if fact.uppercase && rawAuxiliaryOccurrenceSense mol node fact == reference then
            1
          else 0 := by
  cases stage <;> simp only [rawDescriptorNodePriority, provenance, found]

/-- Adversarial residual observation.  The case bit (`uppercase`) is still taken from the
atom-keyed fact.  Only the descriptor sense is corrected occurrence-locally.  This theorem makes
the boundary explicit rather than claiming more than the implementation proves. -/
theorem rawDescriptorNodePriority_rule4a_atomGlobal
    (mol : RawMolecule) (state : RawDescriptorState) (leftSide : Bool)
    (node : RawMolecule.CanonicalBranchNode) (fact : RawDescriptorFact)
    (provenance : node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (found : RawDescriptorState.factAt? state node.atom = some fact) :
    rawDescriptorNodePriority mol state RawDescriptorRuleStage.rule4a leftSide node =
      if fact.uppercase then 2 else 1 := by
  simp only [rawDescriptorNodePriority, provenance, found]

/-! ## Re-rooting the stored sense at the actual occurrence -/

/-- Complete-position behavior of the actual authoritative sense function: when the stored
priority positions cover all ligands, the incoming parent is found, and the parent's position is
promoted to the front, the returned sense is exactly the parity recomputed from the promoted
occurrence order.  The stored `descriptor` field is not consulted. -/
theorem rawAuxiliaryOccurrenceSense_eq_parentPromotion
    (mol : RawMolecule) (node : RawMolecule.CanonicalBranchNode)
    (fact : RawDescriptorFact) (spec : AtomSpec) (parity : TetrahedralInputParity)
    (ligands : List Nat) (parentEntry : Nat × Nat)
    (specEq : mol.atomAt? node.atom = some spec)
    (parityEq : spec.tetrahedral? = some parity)
    (ligandsEq : mol.ligandsWithLonePair node.atom = ligands)
    (parentEq : ligands.zipIdx.find? (fun entry => entry.1 == node.parent) = some parentEntry)
    (positionsLength : fact.priorityPositions.length = ligands.length) :
    rawAuxiliaryOccurrenceSense mol node fact =
      RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven
          (parentEntry.2 :: fact.priorityPositions.erase parentEntry.2)) := by
  have hlength : (fact.priorityPositions.length == ligands.length) = true := by
    rw [positionsLength]
    exact beq_self_eq_true _
  simp only [rawAuxiliaryOccurrenceSense, rawAuxiliaryOccurrenceSenseAuthoritative,
    specEq, parityEq, ligandsEq, parentEq, hlength, if_true]

/-- When the incoming parent is not a ligand (the center-root case, where `parent = atom`), the
actual sense function returns the stored descriptor unchanged. -/
theorem rawAuxiliaryOccurrenceSense_eq_stored_of_parent_absent
    (mol : RawMolecule) (node : RawMolecule.CanonicalBranchNode)
    (fact : RawDescriptorFact) (spec : AtomSpec) (parity : TetrahedralInputParity)
    (ligands : List Nat)
    (specEq : mol.atomAt? node.atom = some spec)
    (parityEq : spec.tetrahedral? = some parity)
    (ligandsEq : mol.ligandsWithLonePair node.atom = ligands)
    (parentAbsent : ligands.zipIdx.find? (fun entry => entry.1 == node.parent) = none) :
    rawAuxiliaryOccurrenceSense mol node fact = fact.descriptor := by
  simp only [rawAuxiliaryOccurrenceSense, rawAuxiliaryOccurrenceSenseAuthoritative,
    specEq, parityEq, ligandsEq, parentAbsent]

/-- Two stored facts with the same complete priority positions induce the same occurrence sense,
whatever their stored `descriptor` fields are.  This is the formal statement that a final
molecular descriptor cannot leak into the resolved auxiliary sense. -/
theorem rawAuxiliaryOccurrenceSense_independent_of_storedDescriptor
    (mol : RawMolecule) (node : RawMolecule.CanonicalBranchNode)
    (left right : RawDescriptorFact) (spec : AtomSpec) (parity : TetrahedralInputParity)
    (ligands : List Nat) (parentEntry : Nat × Nat)
    (specEq : mol.atomAt? node.atom = some spec)
    (parityEq : spec.tetrahedral? = some parity)
    (ligandsEq : mol.ligandsWithLonePair node.atom = ligands)
    (parentEq : ligands.zipIdx.find? (fun entry => entry.1 == node.parent) = some parentEntry)
    (leftPositions : left.priorityPositions.length = ligands.length)
    (rightPositions : right.priorityPositions.length = ligands.length)
    (positionsEq : left.priorityPositions = right.priorityPositions) :
    rawAuxiliaryOccurrenceSense mol node left =
      rawAuxiliaryOccurrenceSense mol node right := by
  rw [rawAuxiliaryOccurrenceSense_eq_parentPromotion mol node left spec parity ligands parentEntry
      specEq parityEq ligandsEq parentEq leftPositions,
    rawAuxiliaryOccurrenceSense_eq_parentPromotion mol node right spec parity ligands parentEntry
      specEq parityEq ligandsEq parentEq rightPositions,
    positionsEq]

/-! ## Parity arithmetic for the concrete witness -/

/-- Promoting the second position to the front is one transposition. -/
theorem parentPromotion_secondPosition_eq :
    1 :: ([0, 1, 2, 3].erase 1) = [1, 0, 2, 3] := rfl

/-- Promoting the first position to the front is the identity order. -/
theorem parentPromotion_firstPosition_eq :
    0 :: ([0, 1, 2, 3].erase 0) = [0, 1, 2, 3] := rfl

/-- The reference priority order is even. -/
theorem permutationIsEven_reference :
    RawMolecule.permutationIsEven [0, 1, 2, 3] = true := rfl

/-- The second-position promotion is odd. -/
theorem permutationIsEven_parentPromoted :
    RawMolecule.permutationIsEven [1, 0, 2, 3] = false := rfl

/-- The second-position promotion flips the parity bit. -/
theorem permutationIsEven_parentPromoted_neg :
    RawMolecule.permutationIsEven [1, 0, 2, 3] =
      !(RawMolecule.permutationIsEven [0, 1, 2, 3]) := by
  rw [permutationIsEven_reference, permutationIsEven_parentPromoted]
  rfl

/-- Flipping the parity flips the descriptor for either written parity. -/
theorem descriptorOfParity_not
    (parity : TetrahedralInputParity) (evenPermutation : Bool) :
    RawMolecule.descriptorOfParity parity (!evenPermutation) =
      RS.swap (RawMolecule.descriptorOfParity parity evenPermutation) := by
  cases parity <;> cases evenPermutation <;> rfl

/-- `RS.swap` has no fixed point. -/
theorem rs_swap_ne_self (value : RS) : RS.swap value ≠ value := by
  cases value <;> simp [RS.swap]

/-- If the incoming parent is the second established position, the actual occurrence sense is the
swap of the descriptor computed from the unpromoted established order. -/
theorem rawAuxiliaryOccurrenceSense_eq_swap_of_secondParent
    (mol : RawMolecule) (node : RawMolecule.CanonicalBranchNode)
    (fact : RawDescriptorFact) (spec : AtomSpec) (parity : TetrahedralInputParity)
    (ligands : List Nat) (parentEntry : Nat × Nat)
    (specEq : mol.atomAt? node.atom = some spec)
    (parityEq : spec.tetrahedral? = some parity)
    (ligandsEq : mol.ligandsWithLonePair node.atom = ligands)
    (parentEq : ligands.zipIdx.find? (fun entry => entry.1 == node.parent) = some parentEntry)
    (positionsLength : fact.priorityPositions.length = ligands.length)
    (parentIs : parentEntry.2 = 1)
    (positionsAre : fact.priorityPositions = [0, 1, 2, 3])
    (storedEq : fact.descriptor =
      RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven [0, 1, 2, 3])) :
    rawAuxiliaryOccurrenceSense mol node fact = RS.swap fact.descriptor := by
  rw [rawAuxiliaryOccurrenceSense_eq_parentPromotion mol node fact spec parity ligands parentEntry
    specEq parityEq ligandsEq parentEq positionsLength]
  simp only [parentIs, positionsAre, parentPromotion_secondPosition_eq,
    permutationIsEven_parentPromoted_neg, storedEq]
  exact descriptorOfParity_not parity (RawMolecule.permutationIsEven [0, 1, 2, 3])

/-- If the incoming parent is already the first established position, the actual occurrence sense
is the stored descriptor unchanged. -/
theorem rawAuxiliaryOccurrenceSense_eq_stored_of_firstParent
    (mol : RawMolecule) (node : RawMolecule.CanonicalBranchNode)
    (fact : RawDescriptorFact) (spec : AtomSpec) (parity : TetrahedralInputParity)
    (ligands : List Nat) (parentEntry : Nat × Nat)
    (specEq : mol.atomAt? node.atom = some spec)
    (parityEq : spec.tetrahedral? = some parity)
    (ligandsEq : mol.ligandsWithLonePair node.atom = ligands)
    (parentEq : ligands.zipIdx.find? (fun entry => entry.1 == node.parent) = some parentEntry)
    (positionsLength : fact.priorityPositions.length = ligands.length)
    (parentIs : parentEntry.2 = 0)
    (positionsAre : fact.priorityPositions = [0, 1, 2, 3])
    (storedEq : fact.descriptor =
      RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven [0, 1, 2, 3])) :
    rawAuxiliaryOccurrenceSense mol node fact = fact.descriptor := by
  rw [rawAuxiliaryOccurrenceSense_eq_parentPromotion mol node fact spec parity ligands parentEntry
    specEq parityEq ligandsEq parentEq positionsLength]
  simp only [parentIs, positionsAre, parentPromotion_firstPosition_eq]
  exact storedEq.symm

/-! ## Concrete witness in the actual function

The molecule is a tetrahedral carbon (atom `0`) bonded to iodine, bromine, chlorine, and fluorine
in that written order.  The written order is also the descending CIP order, so the established
priority positions are `[0, 1, 2, 3]` and the descriptor computed from the established order is
`R`.  The center-root occurrence has `parent = atom = 0`, which is not a ligand, and therefore
returns the stored descriptor.  The occurrence reached through the second written ligand (bromine,
atom `2`, position `1`) promotes that incoming edge to the front, changes parity, and returns the
opposite sense, `S`.

The two occurrence records denote the same atom but have different canonical occurrence keys, so
they are two reads of the auxiliary environment, not two perturbations of one state.  The witness
supplies the atom-keyed fact directly; it isolates the read function's frame dependence and does
not claim that the production final descriptor of this molecule is `R`.
-/

/-- The tetrahedral center specification: a clockwise-written carbon. -/
def witnessSpec : AtomSpec :=
  { element := Element.C, tetrahedral? := some TetrahedralInputParity.clockwise }

/-- Five atoms: the center, then I, Br, Cl, F in the written neighbour order of the center. -/
def witnessMolecule : RawMolecule :=
  { atoms := [witnessSpec,
              { element := Element.I },
              { element := Element.Br },
              { element := Element.Cl },
              { element := Element.F }],
    bonds := [ { source := 0, target := 1, kind := ParsedBondKind.single },
               { source := 0, target := 2, kind := ParsedBondKind.single },
               { source := 0, target := 3, kind := ParsedBondKind.single },
               { source := 0, target := 4, kind := ParsedBondKind.single } ],
    neighborOrder := [[1, 2, 3, 4], [0], [0], [0], [0]] }

/-- The non-root occurrence of atom `0` reached from its second written ligand (bromine, atom 2). -/
def witnessNode : RawMolecule.CanonicalBranchNode :=
  { atom := 0, parent := 2, history := [0, 2],
    provenance := RawMolecule.CanonicalNodeProvenance.realAtom }

/-- The center-root occurrence of the same atom. -/
def witnessRootNode : RawMolecule.CanonicalBranchNode :=
  { atom := 0, parent := 0, history := [0],
    provenance := RawMolecule.CanonicalNodeProvenance.realAtom }

/-- The atom-keyed fact whose descriptor is the value computed from the established order
`[0, 1, 2, 3]`. -/
def witnessFact : RawDescriptorFact :=
  { atom := 0
    descriptor := RawMolecule.descriptorOfParity TetrahedralInputParity.clockwise
      (RawMolecule.permutationIsEven [0, 1, 2, 3])
    uppercase := true
    priorityPositions := [0, 1, 2, 3] }

theorem witnessMolecule_atomAt_zero :
    witnessMolecule.atomAt? 0 = some witnessSpec := rfl

theorem witnessSpec_tetrahedral :
    witnessSpec.tetrahedral? = some TetrahedralInputParity.clockwise := rfl

theorem witnessMolecule_ligands :
    witnessMolecule.ligandsWithLonePair 0 = [1, 2, 3, 4] := rfl

theorem witnessNode_parent :
    witnessNode.parent = 2 := rfl

theorem witnessRootNode_parent :
    witnessRootNode.parent = 0 := rfl

theorem witnessNode_find :
    ([1, 2, 3, 4].zipIdx.find?
      (fun entry => entry.1 == witnessNode.parent)) = some (2, 1) := rfl

theorem witnessRoot_find_none :
    ([1, 2, 3, 4].zipIdx.find?
      (fun entry => entry.1 == witnessRootNode.parent)) = none := rfl

theorem witnessFact_positions :
    witnessFact.priorityPositions = [0, 1, 2, 3] := rfl

theorem witnessFact_descriptor :
    witnessFact.descriptor =
      RawMolecule.descriptorOfParity TetrahedralInputParity.clockwise
        (RawMolecule.permutationIsEven [0, 1, 2, 3]) := rfl

/-- The two occurrence records have the same atom. -/
theorem witnessRootNode_atom_eq_witnessNode :
    witnessRootNode.atom = witnessNode.atom := rfl

/-- The two occurrence records are distinct occurrences: their histories differ, so their
canonical occurrence keys differ even though both are real atoms with the same atom index. -/
theorem witnessRootNode_key_ne_witnessNode :
    canonicalOccurrenceKey witnessRootNode ≠ canonicalOccurrenceKey witnessNode := by
  intro h
  have hhistory := (canonicalOccurrenceKey_eq_iff.mp h).1
  dsimp only [witnessRootNode, witnessNode] at hhistory
  exact List.cons_ne_nil 2 ([] : List Nat)
    (List.tail_eq_of_cons_eq hhistory).symm

/-- At the center-root occurrence, the actual function returns the stored descriptor. -/
theorem witness_rootSense_eq_stored :
    rawAuxiliaryOccurrenceSense witnessMolecule witnessRootNode witnessFact =
      witnessFact.descriptor :=
  rawAuxiliaryOccurrenceSense_eq_stored_of_parent_absent witnessMolecule witnessRootNode
    witnessFact witnessSpec TetrahedralInputParity.clockwise [1, 2, 3, 4]
    rfl rfl rfl witnessRoot_find_none

/-- At the occurrence reached through the second written ligand, the actual function returns the
swap of the stored descriptor. -/
theorem witness_auxiliarySense_eq_swap :
    rawAuxiliaryOccurrenceSense witnessMolecule witnessNode witnessFact =
      RS.swap witnessFact.descriptor :=
  rawAuxiliaryOccurrenceSense_eq_swap_of_secondParent witnessMolecule witnessNode witnessFact
    witnessSpec TetrahedralInputParity.clockwise [1, 2, 3, 4] (2, 1)
    rfl rfl rfl rfl rfl rfl rfl rfl

/-- The auxiliary sense at the non-root occurrence differs from the stored (root/final) value. -/
theorem witness_auxiliarySense_ne_stored :
    rawAuxiliaryOccurrenceSense witnessMolecule witnessNode witnessFact ≠
      witnessFact.descriptor := by
  rw [witness_auxiliarySense_eq_swap]
  exact rs_swap_ne_self witnessFact.descriptor

/-- The two occurrences of the same atom carry opposite auxiliary senses while the stored
atom-global descriptor is unchanged. -/
theorem witness_two_occurrences_opposite :
    rawAuxiliaryOccurrenceSense witnessMolecule witnessRootNode witnessFact =
        witnessFact.descriptor ∧
      rawAuxiliaryOccurrenceSense witnessMolecule witnessNode witnessFact =
        RS.swap witnessFact.descriptor :=
  ⟨witness_rootSense_eq_stored, witness_auxiliarySense_eq_swap⟩

/-- The stored root descriptor of the witness is `R`. -/
theorem witnessFact_descriptor_eq_R :
    witnessFact.descriptor = RS.R := rfl

/-- The actual sense read at the center-root occurrence is `R`. -/
theorem witnessRootNode_auxiliarySense_eq_R :
    rawAuxiliaryOccurrenceSense witnessMolecule witnessRootNode witnessFact = RS.R := by
  rw [witness_rootSense_eq_stored, witnessFact_descriptor_eq_R]

/-- The actual sense read at the occurrence reached through the second written ligand is `S`. -/
theorem witnessNode_auxiliarySense_eq_S :
    rawAuxiliaryOccurrenceSense witnessMolecule witnessNode witnessFact = RS.S := by
  rw [witness_auxiliarySense_eq_swap, witnessFact_descriptor_eq_R]
  rfl

/-- Concrete label values at the three relevant locations: the stored atom-keyed value is `R`,
the root-occurrence read is `R`, and the non-root occurrence read is `S`.  For this supplied
atom-keyed fact, the stored value is not a substitute for the occurrence-specific auxiliary
value. -/
theorem witness_stored_root_occurrence_values :
    witnessFact.descriptor = RS.R ∧
      rawAuxiliaryOccurrenceSense witnessMolecule witnessRootNode witnessFact = RS.R ∧
      rawAuxiliaryOccurrenceSense witnessMolecule witnessNode witnessFact = RS.S :=
  ⟨witnessFact_descriptor_eq_R, witnessRootNode_auxiliarySense_eq_R,
    witnessNode_auxiliarySense_eq_S⟩

/-! ## Kernel-authority certificates -/

assert_kernel_only localizedDepthDependency_sameRoot
assert_kernel_only localizedDepthDependency_strictlyDeeper
assert_kernel_only localizedDependencyView_read_eq
assert_kernel_only localizedDependencyView_read_retains_context
assert_kernel_only localizedFinalOccurrence_root
assert_kernel_only localizedFinalOccurrence_address
assert_kernel_only localizedFinalOccurrence_node
assert_kernel_only localizedFinalOccurrence_remaining
assert_kernel_only localizedDependencyView_finalTarget_sameRoot
assert_kernel_only localizedDependencyView_finalTarget_positiveAddress
assert_kernel_only canonicalOccurrenceKey_eq_iff
assert_kernel_only canonicalOccurrenceKey_atom_eq_of_history_head
assert_kernel_only contextRootNode_key_ne_return
assert_kernel_only contextRootNode_key_ne_duplicate
assert_kernel_only occurrenceAuxState_factAt?_key_and_mem
assert_kernel_only rawDescriptorState_factAt?_atom
assert_kernel_only legacyOccurrenceFactAuthoritative?_key_atom
assert_kernel_only framedOccurrenceFactAuthoritative?_key_atom
assert_kernel_only occurrenceFactAuthoritative?_key_atom
assert_kernel_only legacyOccurrenceFact?_key_atom
assert_kernel_only framedOccurrenceFact?_key_atom
assert_kernel_only occurrenceFact?_key_atom
assert_kernel_only tetrahedralOccurrenceFactAuthoritative?_exact_read
assert_kernel_only tetrahedralOccurrenceFact?_exact_read
assert_kernel_only occurrenceNodePriority_realAtom
assert_kernel_only rawDescriptorNodePriority_realAtom
assert_kernel_only rawDescriptorNodePriority_rule4a_atomGlobal
assert_kernel_only rawAuxiliaryOccurrenceSense_eq_parentPromotion
assert_kernel_only rawAuxiliaryOccurrenceSense_eq_stored_of_parent_absent
assert_kernel_only rawAuxiliaryOccurrenceSense_independent_of_storedDescriptor
assert_kernel_only parentPromotion_secondPosition_eq
assert_kernel_only parentPromotion_firstPosition_eq
assert_kernel_only permutationIsEven_reference
assert_kernel_only permutationIsEven_parentPromoted
assert_kernel_only permutationIsEven_parentPromoted_neg
assert_kernel_only descriptorOfParity_not
assert_kernel_only rs_swap_ne_self
assert_kernel_only rawAuxiliaryOccurrenceSense_eq_swap_of_secondParent
assert_kernel_only rawAuxiliaryOccurrenceSense_eq_stored_of_firstParent
assert_kernel_only witnessRootNode_key_ne_witnessNode
assert_kernel_only witness_rootSense_eq_stored
assert_kernel_only witness_auxiliarySense_eq_swap
assert_kernel_only witness_auxiliarySense_ne_stored
assert_kernel_only witness_two_occurrences_opposite
assert_kernel_only witnessFact_descriptor_eq_R
assert_kernel_only witnessRootNode_auxiliarySense_eq_R
assert_kernel_only witnessNode_auxiliarySense_eq_S
assert_kernel_only witness_stored_root_occurrence_values

end TetraStereo.OneCenter.AuxiliaryContextIntegrity
