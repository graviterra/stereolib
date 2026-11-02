import TetraStereo.OneCenter.LocalizedMarkedRawCarrierBridge
import TetraStereo.OneCenter.LocalizedMarkedTerminalGaugeRefusal
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Structural support of actual generated promotion snapshots

For arbitrary comparison operations, every fact in `underWith` is emitted at a real, framed,
strictly deeper descendant under the same original root. The source and fact occurrences are
constructed in the actual certified finite carrier, with exact raw history/key readback and a
strict carrier-depth dependency. Rings are permitted. Caller-supplied facts are not covered.

Framing alone does not imply membership in the degree-four detected inventory: a three-coordinate
frame may contain the runtime phantom. The structural theorems below do not assume or assert
detection, comparison correctness, or a chemical interpretation of the emitted descriptor.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedGeneratedSnapshotSupport

open LocalizedMarkedOperationEvaluator LocalizedMarkedOperationSimulation
open LocalizedMarkedReachableConfigurations LocalizedMarkedReachedFrameNeighbors
open LocalizedMarkedTerminalReferenceScope LocalizedMarkedGeneratedFactUniqueness
open LocalizedMarkedRawCarrierBridge RawLocalizedChildNodeTransport
open LocalizedGenericMarkedRecalculation (Geometry frameAtoms? factOf)

abbrev Node := RawMolecule.CanonicalBranchNode

theorem real_of_frame (mol : RawMolecule) (node : Node) (atoms : List Nat)
    (frame : frameAtoms? mol node = some atoms) : node.provenance = .realAtom := by
  have notLeaf : node.forcedLeaf = false := by
    cases leaf : node.forcedLeaf with
    | false => rfl
    | true =>
        rw [LocalizedGenericMarkedRecalculation.frameAtoms?_forcedLeaf mol node leaf] at frame
        contradiction
  cases provenance : node.provenance <;>
    simp [RawMolecule.CanonicalBranchNode.forcedLeaf, provenance] at notLeaf
  rfl

/-- The actual upward snapshot has a real source, the actual descriptor computation, and strict
history growth. No property of the comparison operations or coordinates is needed. -/
theorem snapshot_fact_source_strict (mol : RawMolecule) (ops : Operations) (depth : Nat)
    (geom : Geometry) (state : OccurrenceAuxState) (source : Node) (mark : Nat)
    (fact : OccurrenceAuxFact)
    (member : fact ∈ underWith mol ops geom state source (facts mol ops depth) mark) :
    ∃ target descriptor remaining atoms,
      StrictDescendant mol source target ∧
      frameAtoms? mol target = some atoms ∧ target.provenance = .realAtom ∧
      descriptorWith? mol ops geom state (some mark) target (facts mol ops remaining) =
        some descriptor ∧
      fact = factOf target descriptor ∧
      source.history.length < target.history.length := by
  obtain ⟨child, selected, member⟩ := List.mem_flatMap.mp member
  have edge := mem_tiedChildren_actual mol ops state source child selected
  have suffix := history_suffix mol ops depth geom state (some mark) child fact member
  obtain ⟨target, descriptor, remaining, path, computed, value⟩ :=
    LocalizedMarkedTerminalGaugeRefusal.snapshot_fact_source mol ops geom state (some mark)
      depth child fact member
  have frame : ∃ atoms, frameAtoms? mol target = some atoms := by
    cases framed : frameAtoms? mol target with
    | some atoms => exact ⟨atoms, rfl⟩
    | none =>
        rw [descriptor_none_of_frame mol ops geom state (some mark) target _ framed] at computed
        contradiction
  obtain ⟨atoms, framed⟩ := frame
  refine ⟨target, descriptor, remaining, atoms, ⟨child, edge, path⟩, framed,
    real_of_frame mol target atoms framed, computed, value, ?_⟩
  have bound := suffix.length_le
  rw [mol.canonicalChildren_history source child edge, List.length_cons, value,
    factOf_key] at bound
  change source.history.length + 1 ≤ target.history.length at bound
  omega

/-- Every generated snapshot fact has actual certified source and fact occurrences. Their
dependency is proved from strict raw history growth and the executable path grading. -/
theorem snapshot_fact_carriers
    (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : SingleBonded mol) (root : Nat) (valid : root < mol.atomCount)
    (ops : Operations) (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState)
    (source : Node) (sourcePath : ReachedFrom mol root source) (mark : Nat)
    (fact : OccurrenceAuxFact)
    (member : fact ∈ underWith mol ops geom state source (facts mol ops depth) mark) :
    ∃ (target : Node)
      (sourceOccurrence factOccurrence :
        input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1)),
      ReachedFrom mol root target ∧ target.provenance = .realAtom ∧
      sourceOccurrence.1.root.val = root ∧
      NodeCorresponds (fun atom : input.Atom => atom.val) sourceOccurrence.1.node source ∧
      NodeCorresponds (fun atom : input.Atom => atom.val) factOccurrence.1.node target ∧
      input.LocalizedDepthDependency factOccurrence sourceOccurrence ∧
      factOccurrence.1.node.provenance = .realAtom ∧
      fact.key = canonicalOccurrenceKey target ∧
      fact.key.history = factOccurrence.1.node.history.map (fun atom : input.Atom => atom.val) := by
  obtain ⟨target, descriptor, remaining, atoms, strictPath, _, real, _, value, longer⟩ :=
    snapshot_fact_source_strict mol ops depth geom state source mark fact member
  have targetPath : ReachedFrom mol root target := by
    obtain ⟨child, edge, rest⟩ := strictPath
    exact (sourcePath.tail edge).trans rest
  obtain ⟨sourceAddress, sourceNode, sourceExpansion, sourceCorr⟩ :=
    reachedFrom_unbounded_corresponds mol input agreement wellFormed unique supported single
      root valid source sourcePath
  obtain ⟨factAddress, factNode, factExpansion, factCorr⟩ :=
    reachedFrom_unbounded_corresponds mol input agreement wellFormed unique supported single
      root valid target targetPath
  have sourceLength := input.unboundedOfficialSubtree_history_length sourceExpansion
  have factLength := input.unboundedOfficialSubtree_history_length factExpansion
  have sourceHistoryLength := congrArg List.length sourceCorr.history
  have factHistoryLength := congrArg List.length factCorr.history
  simp only [List.length_map] at sourceHistoryLength factHistoryLength
  have addressLt : sourceAddress.length < factAddress.length := by omega
  have officialReal : factNode.provenance = .realAtom := by
    have provenance := factCorr.provenance
    rw [real] at provenance
    have force : ∀ {p : OfficialCIPNodeProvenance},
        NodeProvenanceCorresponds p .realAtom → p = .realAtom := by
      intro p related
      cases related
      rfl
    exact force provenance
  have key : fact.key = canonicalOccurrenceKey target := by rw [value, factOf_key]
  refine ⟨target,
    input.localizedUnboundedOccurrenceAtAtom
      (localizedIndexOf mol input agreement ⟨root, valid⟩) sourceExpansion,
    input.localizedUnboundedOccurrenceAtAtom
      (localizedIndexOf mol input agreement ⟨root, valid⟩) factExpansion,
    targetPath, real, rfl, sourceCorr, factCorr, ⟨rfl, addressLt⟩, officialReal, key, ?_⟩
  change fact.key.history = factNode.history.map (fun atom : input.Atom => atom.val)
  rw [key]
  exact factCorr.history.symm

/-- A successful lookup in the actual generated snapshot has the same full occurrence key as
the real certified dependency constructed above. No reachability assumption on the lookup query
is needed: its key is validated by the successful lookup itself. -/
theorem snapshot_factAt_carriers
    (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : SingleBonded mol) (root : Nat) (valid : root < mol.atomCount)
    (ops : Operations) (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState)
    (source : Node) (sourcePath : ReachedFrom mol root source) (mark : Nat)
    (query : Node) (fact : OccurrenceAuxFact)
    (lookup : (underWith mol ops geom state source (facts mol ops depth) mark).factAt? query =
      some fact) :
    ∃ (target : Node)
      (sourceOccurrence factOccurrence :
        input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1)),
      ReachedFrom mol root target ∧ target.provenance = .realAtom ∧
      sourceOccurrence.1.root.val = root ∧
      NodeCorresponds (fun atom : input.Atom => atom.val) sourceOccurrence.1.node source ∧
      NodeCorresponds (fun atom : input.Atom => atom.val) factOccurrence.1.node target ∧
      input.LocalizedDepthDependency factOccurrence sourceOccurrence ∧
      factOccurrence.1.node.provenance = .realAtom ∧
      canonicalOccurrenceKey query = canonicalOccurrenceKey target ∧
      query.history = factOccurrence.1.node.history.map (fun atom : input.Atom => atom.val) := by
  have member : fact ∈ underWith mol ops geom state source (facts mol ops depth) mark :=
    List.mem_of_find?_eq_some lookup
  have key : fact.key = canonicalOccurrenceKey query := by
    have test := List.find?_some lookup
    simpa only [beq_iff_eq] using test
  obtain ⟨target, sourceOccurrence, factOccurrence, path, real, rootEq, sourceCorr, factCorr,
    dependency, officialReal, factKey, history⟩ :=
    snapshot_fact_carriers mol input agreement wellFormed unique supported single root valid
      ops depth geom state source sourcePath mark fact member
  refine ⟨target, sourceOccurrence, factOccurrence, path, real, rootEq, sourceCorr, factCorr,
    dependency, officialReal, key.symm.trans factKey, ?_⟩
  rw [key] at history
  exact history

end TetraStereo.OneCenter.LocalizedMarkedGeneratedSnapshotSupport

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedGeneratedSnapshotSupport.real_of_frame
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedGeneratedSnapshotSupport.snapshot_fact_source_strict
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedGeneratedSnapshotSupport.snapshot_fact_carriers
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedGeneratedSnapshotSupport.snapshot_factAt_carriers
