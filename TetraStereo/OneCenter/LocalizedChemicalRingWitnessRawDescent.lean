import TetraStereo.OneCenter.LocalizedChemicalRingBoundaryWitnessExecution
import TetraStereo.OneCenter.LocalizedChemicalRingTwoFixedNeighbors
import TetraStereo.OneCenter.LocalizedMarkedRawCarrierBridge
import TetraStereo.OneCenter.LocalizedActualFrameChildClassification
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
Residual molecular witness paths in an actual outward comparison tree are paths of the
raw evaluator's canonical children. The official-to-raw child correspondence supplies
every edge, and generated histories identify the endpoint with its complete original-root
raw query. No successful label, fact lookup, or selected-child premise is used.

Selection of the first child remains a separate obligation. Once supplied, the result
can feed the actual snapshot fact-completeness theorem.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingWitnessRawDescent

open CertifiedLocalizedCIPInput DeclarativeCIP RetainedCoherentSymmetry
open LocalizedCumulativeDecoratedTree LocalizedActualBoundaryPathRealization
open LocalizedChemicalRingBoundaryWitnessFactMatch LocalizedChemicalRingWitnessFactMatch
open LocalizedChemicalRingWitnessExecution LocalizedChemicalRingTwoFixedNeighbors
open LocalizedMarkedRetainedCanonicalFrame LocalizedMarkedRetainedPromotedRanking
open LocalizedMarkedRetainedStateReader LocalizedMarkedRetainedMolecularSelection
open LocalizedMarkedCarrierLookup LocalizedMarkedReachableConfigurations
open LocalizedMarkedTerminalReferenceScope LocalizedMarkedRawCarrierBridge
open RawLocalizedChildNodeTransport RawLocalizedOxidoPathInvariant
open LocalizedMarkedCertifiedTerminalRefusal (raw_single)
open LocalizedMarkedUncappedOperations (generated_of_reachedFrom)

abbrev Node := RawMolecule.CanonicalBranchNode

private theorem provenance_real {p : RawMolecule.CanonicalNodeProvenance}
    (h : NodeProvenanceCorresponds .realAtom p) : p = .realAtom := by
  cases h
  rfl

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)

include agreement admissible supported single in
/-- An actual official expansion edge has a corresponding actual raw canonical edge. -/
theorem official_child_raw (raw : Node) (reached : Reached mol raw)
    (official next : OfficialCIPNode input.Atom)
    (corresponds : NodeCorresponds Fin.val official raw)
    (edge : next ∈ input.executableOfficialCIPChildren official) :
    ∃ child ∈ mol.canonicalChildren raw, NodeCorresponds Fin.val next child := by
  obtain ⟨root, bound, path⟩ := reached
  have rawSingle := raw_single mol input agreement admissible.1.1 admissible.1.2 supported single
  obtain ⟨aligned, alignment, permutation⟩ :=
    reachableCIPChildren_forall₂_canonicalChildren mol input agreement admissible.1.1
      admissible.1.2 supported (canonicalCenterRoot root) rfl bound
      (noOxidoRootEdgeAtRootCopies_of_singleBonded mol rawSingle _)
      raw official (reachedFrom_reachableCanonical mol root raw path) corresponds
  obtain ⟨child, member, related⟩ := exists_mem_of_forall₂_left alignment edge
  exact ⟨child, permutation.mem_iff.mp member, related⟩

include agreement admissible supported single in
/-- Looking up a node in a generated source tree constructs its raw canonical descent.
The tree's sorting order need not agree with the raw child-list order. -/
theorem source_lookup_raw_descent (address : List Nat) :
    ∀ (tree : OfficialCIPSourceTree input.Atom) (raw : Node),
      tree.GeneratedBy input.executableOfficialCIPChildren → Reached mol raw →
      NodeCorresponds Fin.val tree.source raw →
      ∀ query : OfficialCIPNode input.Atom,
        tree.sourceAtAddress? address = some query →
        ∃ rawQuery, Descends mol raw rawQuery ∧ NodeCorresponds Fin.val query rawQuery := by
  induction address with
  | nil =>
      intro tree raw generated reached corresponds query found
      have source := source_eq_of_sourceAtAddress?_nil found
      exact ⟨raw, .refl, source ▸ corresponds⟩
  | cons slot rest ih =>
      intro tree raw generated reached corresponds query found
      cases tree with
      | node source children =>
          obtain ⟨subtree, member, lookup⟩ := exists_child_of_sourceAtAddress?_cons found
          obtain ⟨subGenerated, officialEdge⟩ := child_generated_and_mem generated member
          obtain ⟨child, rawEdge, childCorresponds⟩ :=
            official_child_raw input mol agreement admissible supported single raw reached
              source subtree.source corresponds officialEdge
          obtain ⟨rawQuery, descent, queryCorresponds⟩ := ih subtree child subGenerated
            (reached_child mol raw child reached rawEdge) childCorresponds query lookup
          exact ⟨rawQuery, (Relation.ReflTransGen.single rawEdge).trans descent,
            queryCorresponds⟩

include single in
/-- Actual generated history and real provenance determine the entire raw witness node,
including the incoming parent. -/
theorem raw_eq_boundary_query {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel) (p : List input.Atom)
    (raw : Node) (reached : Reached mol raw)
    (corresponds : NodeCorresponds Fin.val
      (boundaryNode target.1.node.history.reverse p) raw) :
    raw = rawPathNode target.1.root (boundaryPath target p) := by
  have history : raw.history =
      (rawPathNode target.1.root (boundaryPath target p)).history := by
    rw [boundaryPath_raw_history single target p]
    simpa only [boundaryNode_history, List.reverse_append, List.reverse_reverse] using
      corresponds.history.symm
  have real : raw.provenance = .realAtom := by
    have h := corresponds.provenance
    change NodeProvenanceCorresponds .realAtom raw.provenance at h
    exact provenance_real h
  obtain ⟨center, _, generated⟩ := reached
  apply generated_eq_rawPathNode target.1.root (boundaryPath target p)
    (generated_of_reachedFrom mol center raw generated)
  change (⟨raw.history, raw.provenance⟩ : CanonicalOccurrenceKey) =
    ⟨(rawPathNode target.1.root (boundaryPath target p)).history, .realAtom⟩
  rw [history, real]

include agreement single in
/-- A valid residual witness extends an actual real carrier history without repeating
atoms, so its complete raw history fits in the molecular atom count. -/
theorem boundary_query_length_le {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (real : target.1.node.provenance = .realAtom) (atom : input.Atom) (p : List input.Atom)
    (valid : ResidualObsPath input.moleculeGraph target.1.node.history.reverse atom p) :
    (rawPathNode target.1.root (boundaryPath target p)).history.length ≤ mol.atomCount := by
  have history := (LocalizedActualBoundaryObservationReadback.occurrence_history_facts
    input target real).1
  have distinct := nodup_boundary_append (List.nodup_reverse.mpr history) valid
  have bound : (target.1.node.history.reverse ++ p).length ≤
      input.certified.input.molecule.atomCount := by
    simpa only [Fintype.card_fin] using distinct.length_le_card
  have count := mol.toSemanticMolecule?_atomCount input.certified.input.molecule agreement.1
  change ((target.1.root :: boundaryPath target p).reverse.map Fin.val).length ≤ _
  rw [List.length_map, List.length_reverse, root_cons_boundaryPath single target p]
  exact bound.trans_eq count

include agreement single in
/-- The evaluator's structural depth supplies every such witness's exact history budget. -/
theorem boundary_query_adequate {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (real : target.1.node.provenance = .realAtom) (atom : input.Atom) (p : List input.Atom)
    (valid : ResidualObsPath input.moleculeGraph target.1.node.history.reverse atom p)
    (source : Node) :
    (rawPathNode target.1.root (boundaryPath target p)).history.length ≤
      LocalizedGenericMarkedRecalculation.structuralDepth mol source + source.history.length := by
  have bound := boundary_query_length_le input mol agreement single target real atom p valid
  unfold LocalizedGenericMarkedRecalculation.structuralDepth
  omega

/-- An actual frame slot whose atom is fresh for the target history cannot be the
incoming parent. Its original root and outward child address are therefore derived. -/
theorem frame_fresh_outward {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (slot : Fin 4) (atom : input.Atom)
    (current : (frame.cursorAt slot).occurrence.1.node.current? = some atom)
    (fresh : atom ∉ target.1.node.history) :
    ∃ childSlot, (frame.cursorAt slot).occurrence.1.root = target.1.root ∧
      (frame.cursorAt slot).occurrence.1.address = target.1.address ++ [childSlot] := by
  rcases input.localizedOccurrenceFourLigandFrame_cursorAt_classification
      target frame computed slot with parent | outward
  · obtain ⟨certificate, cursorEq, _⟩ := parent
    obtain ⟨_, parentAtom, _, _, parentCurrent, shape, _⟩ := certificate.history_shape input
    rw [cursorEq] at current
    have same : parentAtom = atom := Option.some.inj (parentCurrent.symm.trans current)
    exact False.elim (fresh (by rw [shape, same]; simp))
  · obtain ⟨⟨childSlot, address⟩, root, _, _⟩ := outward
    exact ⟨childSlot, root, address⟩

include agreement admissible supported single in
/-- Every residual witness in an actual real outward slot is reached from a corresponding
raw child. The source tree, its generated law, and the witness address are all derived
from the actual retained frame. The conclusion keeps the original root and full history. -/
theorem actual_boundary_path_descent (raw : Node) (reached : Reached mol raw)
    (state : OccurrenceAuxState)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (found : lookup? input raw = some target)
    (real : target.1.node.provenance = .realAtom)
    (unit : DetectedOccurrence input.moleculeGraph)
    (targetUnit : input.molecularFrameUnit target.1 = unit.1)
    (slot : Fin 4) (atom : input.Atom)
    (current : ((frames input single state target real unit targetUnit).frame.cursorAt slot).occurrence.1.node.current? = some atom)
    (childReal : ((frames input single state target real unit targetUnit).frame.cursorAt slot).occurrence.1.node.provenance = .realAtom)
    (sameRoot : ((frames input single state target real unit targetUnit).frame.cursorAt slot).occurrence.1.root = target.1.root)
    (childSlot : Nat)
    (address : ((frames input single state target real unit targetUnit).frame.cursorAt slot).occurrence.1.address = target.1.address ++ [childSlot])
    (p : List input.Atom)
    (valid : ResidualObsPath input.moleculeGraph target.1.node.history.reverse atom p) :
    ∃ child ∈ mol.canonicalChildren raw,
      child.atom = atom.val ∧ child.provenance = .realAtom ∧
      Descends mol child (rawPathNode target.1.root (boundaryPath target p)) := by
  let frame := frames input single state target real unit targetUnit
  let cursor := frame.frame.cursorAt slot
  let tree := toOfficialSourceTree (frame.stages slot).a.tree
  have rooted := (outward_slot_boundary input single (rawStateDescriptorMap input state)
    target frame real slot atom current childReal sameRoot childSlot address).1
  have edge := LocalizedActualBoundaryObservationReadback.outwardChild_node_mem input
    ⟨target, none⟩ cursor sameRoot childSlot address
  obtain ⟨child, rawEdge, related⟩ := official_child_raw input mol agreement admissible
    supported single raw reached target.1.node cursor.occurrence.1.node
    (lookup?_sound input raw target found) edge
  have atomEq : child.atom = atom.val := by
    have h := related.current
    rw [current] at h
    exact (Option.some.inj h).symm
  have rawReal : child.provenance = .realAtom := by
    have h := related.provenance
    rw [childReal] at h
    exact provenance_real h
  have childReached := reached_child mol raw child reached rawEdge
  have sourceRelated : NodeCorresponds Fin.val tree.source child := by
    simpa only [tree, toOfficialSourceTree_source, (frame.stages slot).a.sourceEq] using related
  obtain ⟨witnessAddress, lookup⟩ := exists_address_of_residualObsPath single rooted valid
  obtain ⟨rawQuery, descent, queryRelated⟩ := source_lookup_raw_descent input mol agreement
    admissible supported single witnessAddress tree child rooted.generated childReached
    sourceRelated (boundaryNode target.1.node.history.reverse p) lookup
  have exactQuery := raw_eq_boundary_query input mol single target p rawQuery
    (descendant_reached childReached descent) queryRelated
  exact ⟨child, rawEdge, atomEq, rawReal, exactQuery ▸ descent⟩

include agreement admissible supported single in
/-- Freshness alone eliminates the outward-root/address premises of the preceding actual
facade. In a reconstructed moved-attachment symmetry, history fixation derives freshness. -/
theorem actual_fresh_boundary_path_descent (raw : Node) (reached : Reached mol raw)
    (state : OccurrenceAuxState)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (found : lookup? input raw = some target)
    (real : target.1.node.provenance = .realAtom)
    (unit : DetectedOccurrence input.moleculeGraph)
    (targetUnit : input.molecularFrameUnit target.1 = unit.1)
    (slot : Fin 4) (atom : input.Atom)
    (current : ((frames input single state target real unit targetUnit).frame.cursorAt slot).occurrence.1.node.current? = some atom)
    (childReal : ((frames input single state target real unit targetUnit).frame.cursorAt slot).occurrence.1.node.provenance = .realAtom)
    (fresh : atom ∉ target.1.node.history)
    (p : List input.Atom)
    (valid : ResidualObsPath input.moleculeGraph target.1.node.history.reverse atom p) :
    ∃ child ∈ mol.canonicalChildren raw,
      child.atom = atom.val ∧ child.provenance = .realAtom ∧
      Descends mol child (rawPathNode target.1.root (boundaryPath target p)) := by
  let frame := frames input single state target real unit targetUnit
  have computed : input.localizedOccurrenceFourLigandFrame? target = some frame.frame := by
    rw [← input.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?]
    exact frame.frameComputed
  obtain ⟨childSlot, sameRoot, address⟩ :=
    frame_fresh_outward input target frame.frame computed slot atom current fresh
  exact actual_boundary_path_descent input mol agreement admissible supported single raw reached
    state target found real unit targetUnit slot atom current childReal sameRoot childSlot address p valid

end TetraStereo.OneCenter.LocalizedChemicalRingWitnessRawDescent

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingWitnessRawDescent.official_child_raw
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingWitnessRawDescent.source_lookup_raw_descent
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingWitnessRawDescent.raw_eq_boundary_query
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingWitnessRawDescent.boundary_query_length_le
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingWitnessRawDescent.boundary_query_adequate
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingWitnessRawDescent.frame_fresh_outward
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingWitnessRawDescent.actual_boundary_path_descent
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingWitnessRawDescent.actual_fresh_boundary_path_descent
