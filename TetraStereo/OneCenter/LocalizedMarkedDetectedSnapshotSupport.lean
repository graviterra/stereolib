import TetraStereo.OneCenter.LocalizedMarkedGeneratedSnapshotSupport
import TetraStereo.OneCenter.LocalizedMarkedConfigurationTransport
import TetraStereo.OneCenter.LocalizedContextCyclicReaderBridge
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Generated snapshot facts belong to the detected physical inventory

Successful comparison operations must return permutations of their actual four frame positions.
This is an order-shape contract, not a comparison result or chemical-priority assumption.
If the supplied geometry has no coordinate for the runtime phantom, a three-coordinate frame
cannot emit a descriptor. Every actual snapshot fact therefore comes from a degree-four atom.
Together with structural snapshot support this supplies real detected strict carrier dependencies,
including in finite single-bond rings, for arbitrary operation instances meeting that contract.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedDetectedSnapshotSupport

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedMarkedOperationEvaluator LocalizedMarkedOperationSimulation
open LocalizedMarkedReachableConfigurations LocalizedMarkedReachedFrameNeighbors
open LocalizedMarkedTerminalReferenceScope LocalizedMarkedGeneratedFactUniqueness
open LocalizedMarkedGeneratedSnapshotSupport LocalizedMarkedConfigurationTransport
open LocalizedMarkedUncappedOperations (generated_of_reachedFrom)
open RawLocalizedChildNodeTransport
open LocalizedGenericMarkedRecalculation
  (Geometry frameAtoms? readback? atomsAt? rankedAtoms? consistent strict eligibleOf
    appendFacts? consensus caseFromMirror? factOf)

abbrev Node := RawMolecule.CanonicalBranchNode

/-- Only the shape of successful orders is required; operations may refuse and may return ties. -/
def FramePermutationSound (ops : Operations) : Prop :=
  (∀ state node sorted adjacent, ops.ordinary state node = some (sorted, adjacent) →
    sorted.Perm [0, 1, 2, 3]) ∧
  (∀ state node mark ranking, ops.marked state node mark = some ranking →
    ranking.positions.Perm [0, 1, 2, 3])

/-- The shipped uncapped operations satisfy the shape contract on every successful output,
without a totality, chemical-ranking or expected-result premise. -/
theorem uncapped_framePermutationSound (mol : RawMolecule) :
    FramePermutationSound (LocalizedMarkedUncappedEvaluator.operations mol) := by
  open AuthoritativeCIPRule6Scheduler AuthoritativeCIPRule6P92Enumeration in
    constructor
    · intro state node sorted adjacent computed
      change LocalizedMarkedUncappedOperations.ordinary? mol state node =
        some (sorted, adjacent) at computed
      cases frame : occurrenceLigandFrame? mol node with
      | none => simp [LocalizedMarkedUncappedOperations.ordinary?, frame] at computed
      | some roots =>
          cases sorting : sortAuthoritativeRule6InitialPositions? mol state
              (LocalizedMarkedUncappedOperations.comparisonFuel mol) roots
              (List.range roots.length) with
          | none => simp [LocalizedMarkedUncappedOperations.ordinary?, frame, sorting] at computed
          | some result =>
              cases comparison : compareAuthoritativeRule6InitialAdjacent? mol state
                  (LocalizedMarkedUncappedOperations.comparisonFuel mol) roots result with
              | none =>
                  simp [LocalizedMarkedUncappedOperations.ordinary?, frame, sorting, comparison]
                    at computed
              | some observations =>
                  simp [LocalizedMarkedUncappedOperations.ordinary?, frame, sorting, comparison]
                    at computed
                  obtain ⟨rfl, rfl⟩ := computed
                  have permutation := sortAuthoritativeRule6InitialPositions?_perm mol state _
                    roots _ _ sorting
                  simpa [occurrenceLigandFrame?_result_length mol node roots frame] using permutation
    · intro state node mark ranking computed
      change LocalizedMarkedUncappedOperations.marked? mol state node mark = some ranking at computed
      cases frame : occurrenceLigandFrame? mol node with
      | none => simp [LocalizedMarkedUncappedOperations.marked?, frame] at computed
      | some roots =>
          unfold LocalizedMarkedUncappedOperations.marked? at computed
          simp only [frame] at computed
          dsimp only [Bind.bind, Option.bind] at computed
          split at computed
          · contradiction
          · have permutation := authoritativeOccurrenceRule6PositionRankingBackend_positions_perm
              mol state _ roots _ _ ranking computed
            simpa [occurrenceLigandFrame?_result_length mol node roots frame] using permutation

theorem reordered_frame_none (mol : RawMolecule) (geom : Geometry) (node : Node)
    (atoms positions : List Nat) (frame : frameAtoms? mol node = some atoms)
    (permutation : positions.Perm [0, 1, 2, 3]) (absent : readback? geom atoms = none) :
    (atomsAt? atoms positions).bind (readback? geom) = none := by
  have length := frame_length mol node atoms frame
  rcases atoms with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, tail⟩⟩⟩⟩ <;> simp at length
  subst tail
  have formula := reordered_readback_partial geom ![a, b, c, d] positions permutation
  simpa [absent] using formula

private theorem consensus_replicate_none (count : Nat) :
    consensus (List.replicate count (none : Option RS)) = none := by
  cases count with
  | zero => rfl
  | succ count => cases count <;> rfl

/-- A missing base-frame readback cannot be repaired by reordering or by a promotion snapshot. -/
theorem rawStep_none_of_frame_readback_none (mol : RawMolecule) (ops : Operations)
    (sound : FramePermutationSound ops) (geom : Geometry) (state : OccurrenceAuxState)
    (ctx : Option Nat) (node : Node) (under : Nat → OccurrenceAuxState)
    (atoms : List Nat) (frame : frameAtoms? mol node = some atoms)
    (absent : readback? geom atoms = none) :
    rawStep? mol ops geom state ctx node under = none := by
  have markedAbsent : ∀ temp mark, markedReading? mol ops geom temp node mark = none := by
    intro temp mark
    cases computed : ops.marked temp node mark with
    | none => simp [markedReading?, frame, computed]
    | some ranking =>
        have reordered := reordered_frame_none mol geom node atoms ranking.positions frame
          (sound.2 temp node mark ranking computed) absent
        by_cases unique : ranking.unique = true
        · simpa [markedReading?, frame, computed, rankedAtoms?, unique, atomsAt?] using reordered
        · simp [markedReading?, frame, computed, rankedAtoms?, unique]
  have evaluations : ∀ mark,
      (appendFacts? state (under mark)).bind
        (fun temp => markedReading? mol ops geom temp node mark) = none := by
    intro mark
    cases appendFacts? state (under mark) <;> simp [markedAbsent]
  cases computed : ops.ordinary state node with
  | none => simp [rawStep?, frame, computed]
  | some pair =>
      obtain ⟨sorted, adjacent⟩ := pair
      have reordered := reordered_frame_none mol geom node atoms sorted frame
        (sound.1 state node sorted adjacent computed) absent
      by_cases bad : ¬ atoms.Nodup ∨ consistent adjacent = false
      · simp [rawStep?, frame, computed, bad]
      · by_cases separated : strict adjacent = true
        · simpa [rawStep?, frame, computed, bad, separated] using reordered
        · cases ctx <;>
            simp [rawStep?, frame, computed, separated, evaluations, consensus_replicate_none]

/-- Successful descriptor generation at a reached occurrence forces four physical neighbors.
The three-neighbor alternative contains the phantom and is excluded by actual geometry refusal. -/
theorem descriptor_degree_four (mol : RawMolecule) (ops : Operations)
    (sound : FramePermutationSound ops) (wellFormed : mol.WellFormed)
    (single : SingleBonded mol) (geom : Geometry) (phantom : geom mol.atomCount = none)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : Node) (reached : Reached mol node)
    (sub : Geometry → OccurrenceAuxState → Option Nat → Node → OccurrenceAuxState)
    (descriptor : LocalizedTetrahedralRSPseudoDescriptor)
    (computed : descriptorWith? mol ops geom state ctx node sub = some descriptor) :
    (mol.canonicalIncidentNeighbors node.atom).length = 4 := by
  cases frame : frameAtoms? mol node with
  | none =>
      rw [descriptor_none_of_frame mol ops geom state ctx node sub frame] at computed
      contradiction
  | some atoms =>
      rcases frame_atoms_perm_neighbors mol wellFormed single node reached atoms frame with
        ⟨four, _⟩ | ⟨_, permutation⟩
      · exact four
      · have member : mol.atomCount ∈ atoms := permutation.mem_iff.mpr (by simp)
        have absent := readback_none_of_missing geom atoms mol.atomCount member phantom
        have rawAbsent := rawStep_none_of_frame_readback_none mol ops sound geom state ctx
          node (underWith mol ops geom state node sub) atoms frame absent
        simp [descriptorWith?, rawWith?, rawAbsent, caseFromMirror?] at computed

/-- A generated snapshot fact keyed at an actual reached query has physical degree four.
Its source is recovered from execution and identified by the full occurrence key. -/
theorem snapshot_factAt_degree_four (mol : RawMolecule) (ops : Operations)
    (sound : FramePermutationSound ops) (wellFormed : mol.WellFormed)
    (single : SingleBonded mol) (geom : Geometry) (phantom : geom mol.atomCount = none)
    (state : OccurrenceAuxState) (depth : Nat) (source : Node) (sourceReached : Reached mol source)
    (mark : Nat) (query : Node) (queryReached : Reached mol query) (fact : OccurrenceAuxFact)
    (lookup : (underWith mol ops geom state source (facts mol ops depth) mark).factAt? query =
      some fact) :
    (mol.canonicalIncidentNeighbors query.atom).length = 4 := by
  have member := List.mem_of_find?_eq_some lookup
  have key : fact.key = canonicalOccurrenceKey query := by
    simpa only [beq_iff_eq] using List.find?_some lookup
  obtain ⟨target, descriptor, remaining, _, path, _, _, computed, value, _⟩ :=
    snapshot_fact_source_strict mol ops depth geom state source mark fact member
  have targetReached : Reached mol target := by
    obtain ⟨child, edge, rest⟩ := path
    exact descendant_reached (reached_child mol source child sourceReached edge) rest
  have degree := descriptor_degree_four mol ops sound wellFormed single geom phantom state
    (some mark) target targetReached (facts mol ops remaining) descriptor computed
  rw [value, factOf_key] at key
  obtain ⟨targetRoot, _, targetPath⟩ := targetReached
  obtain ⟨queryRoot, _, queryPath⟩ := queryReached
  have same := LocalizedMarkedTerminalGaugeRefusal.generated_eq_of_key
    (generated_of_reachedFrom mol targetRoot target targetPath)
    (generated_of_reachedFrom mol queryRoot query queryPath) key
  simpa [same] using degree

/-- Raw degree four is the certified detected inventory, transported through the actual intake. -/
theorem raw_degree_four_detected (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (atom : Fin mol.atomCount) (four : (mol.canonicalIncidentNeighbors atom.val).length = 4) :
    IsDetectedCenter input.moleculeGraph (localizedIndexOf mol input agreement atom) := by
  have permutation := canonicalIncidentNeighbors_perm_sortedNeighborAtoms mol input agreement
    wellFormed unique supported atom
  have length := permutation.length_eq
  rw [four] at length
  simpa [IsDetectedCenter, sortedNeighborAtoms] using length.symm

theorem certified_simple_of_raw_single (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : SingleBonded mol) : input.moleculeGraph.SimpleBonded := by
  intro left right adjacent
  have bond := moleculeGraph_bond_eq_rawBondOrder mol input agreement wellFormed unique
    supported left right
  change 0 < input.moleculeGraph.bond left right at adjacent
  rw [bond] at adjacent ⊢
  exact Nat.le_antisymm (single left.val right.val) (Nat.succ_le_of_lt adjacent)

/-- Detection belongs to the actual carrier unit, not merely to an unrelated atom with that name. -/
theorem carrier_detected_of_raw_degree (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : SingleBonded mol) {fuel : Nat} (occurrence : input.LocalizedCIPOccurrence fuel)
    (node : Node) (valid : node.atom < mol.atomCount)
    (corresponds : NodeCorresponds (fun atom : input.Atom => atom.val) occurrence.1.node node)
    (four : (mol.canonicalIncidentNeighbors node.atom).length = 4) :
    IsDetectedCenter input.moleculeGraph (input.molecularFrameUnit occurrence.1).atom := by
  obtain ⟨current, currentEq⟩ := NodeCorresponds.exists_current corresponds
  have currentVal : current.val = node.atom := by
    have mapped := corresponds.current
    rw [currentEq] at mapped
    exact Option.some.inj mapped
  have currentIndex : current = localizedIndexOf mol input agreement ⟨node.atom, valid⟩ :=
    Fin.ext currentVal
  have head := corresponds.head.trans currentEq
  have last := input.carrierOccurrence_history_getLast_eq_root
    (certified_simple_of_raw_single mol input agreement wellFormed unique supported single) occurrence
  rw [input.molecularFrameUnit_atom_eq_current occurrence.1 head last, currentIndex]
  exact raw_degree_four_detected mol input agreement wellFormed unique supported
    ⟨node.atom, valid⟩ four

/-- Actual successful snapshot lookup constructs a real detected strict dependency, with the same
full raw occurrence key and history. No detected-source or carrier-existence premise is supplied.
The two nonstructural inputs are phantom-free geometry and successful-output permutation shape. -/
theorem snapshot_factAt_detected_carriers
    (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : SingleBonded mol) (root : Nat) (valid : root < mol.atomCount)
    (ops : Operations) (sound : FramePermutationSound ops) (depth : Nat)
    (geom : Geometry) (phantom : geom mol.atomCount = none) (state : OccurrenceAuxState)
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
      IsDetectedCenter input.moleculeGraph (input.molecularFrameUnit factOccurrence.1).atom ∧
      canonicalOccurrenceKey query = canonicalOccurrenceKey target ∧
      query.history = factOccurrence.1.node.history.map (fun atom : input.Atom => atom.val) := by
  obtain ⟨target, sourceOccurrence, factOccurrence, path, real, rootEq, sourceCorr, factCorr,
    dependency, officialReal, key, history⟩ :=
    snapshot_factAt_carriers mol input agreement wellFormed unique supported single root valid
      ops depth geom state source sourcePath mark query fact lookup
  have targetLookup :
      (underWith mol ops geom state source (facts mol ops depth) mark).factAt? target = some fact := by
    unfold OccurrenceAuxState.factAt? at lookup ⊢
    rw [← key]
    exact lookup
  have targetReached : Reached mol target := ⟨root, valid, path⟩
  have degree := snapshot_factAt_degree_four mol ops sound wellFormed single geom phantom state
    depth source ⟨root, valid, sourcePath⟩ mark target targetReached fact targetLookup
  have detected := carrier_detected_of_raw_degree mol input agreement wellFormed unique supported
    single factOccurrence target (reached_atom_valid mol wellFormed target targetReached) factCorr degree
  exact ⟨target, sourceOccurrence, factOccurrence, path, real, rootEq, sourceCorr, factCorr,
    dependency, officialReal, detected, key, history⟩

/-- Actual uncapped generated snapshots have detected support. The operation-shape obligation
is discharged from the existing successful-output permutation laws. -/
theorem uncapped_snapshot_factAt_detected_carriers
    (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : SingleBonded mol) (root : Nat) (valid : root < mol.atomCount)
    (depth : Nat) (geom : Geometry) (phantom : geom mol.atomCount = none)
    (state : OccurrenceAuxState) (source : Node) (sourcePath : ReachedFrom mol root source)
    (mark : Nat) (query : Node) (fact : OccurrenceAuxFact)
    (lookup : (underWith mol (LocalizedMarkedUncappedEvaluator.operations mol) geom state source
      (facts mol (LocalizedMarkedUncappedEvaluator.operations mol) depth) mark).factAt? query =
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
      IsDetectedCenter input.moleculeGraph (input.molecularFrameUnit factOccurrence.1).atom ∧
      canonicalOccurrenceKey query = canonicalOccurrenceKey target ∧
      query.history = factOccurrence.1.node.history.map (fun atom : input.Atom => atom.val) :=
  snapshot_factAt_detected_carriers mol input agreement wellFormed unique supported single root
    valid (LocalizedMarkedUncappedEvaluator.operations mol) (uncapped_framePermutationSound mol)
    depth geom phantom state source sourcePath mark query fact lookup

end TetraStereo.OneCenter.LocalizedMarkedDetectedSnapshotSupport

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedDetectedSnapshotSupport.FramePermutationSound
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedDetectedSnapshotSupport.uncapped_framePermutationSound
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedDetectedSnapshotSupport.reordered_frame_none
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedDetectedSnapshotSupport.rawStep_none_of_frame_readback_none
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedDetectedSnapshotSupport.descriptor_degree_four
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedDetectedSnapshotSupport.snapshot_factAt_degree_four
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedDetectedSnapshotSupport.raw_degree_four_detected
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedDetectedSnapshotSupport.certified_simple_of_raw_single
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedDetectedSnapshotSupport.carrier_detected_of_raw_degree
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedDetectedSnapshotSupport.snapshot_factAt_detected_carriers
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedDetectedSnapshotSupport.uncapped_snapshot_factAt_detected_carriers
