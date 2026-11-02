import TetraStereo.OneCenter.LocalizedCyclicSpatialDescriptorWitness
import TetraStereo.OneCenter.LocalizedRetainedContextAllOccurrences
import TetraStereo.OneCenter.DeclarativeCIPCompleteRule5Order
import TetraStereo.OneCenter.LocalizedParametricCumulativeLabels
import TetraStereo.OneCenter.LocalizedRuleMajorRule4aAgreement
import TetraStereo.OneCenter.LocalizedContextCompoundReadback
import TetraStereo.OneCenter.LocalizedRuleMajorCompoundReadback
import TetraStereo.OneCenter.LocalizedSimpleBondFourLigandFrames
import TetraStereo.OneCenter.LocalizedOutwardDecoratedSourceFaithfulness
import TetraStereo.OneCenter.LocalizedActualFrameChildClassification
import TetraStereo.OneCenter.LocalizedTetrahedralRootDoubleBondBound
import TetraStereo.OneCenter.LocalizedConstitutionalRootSeparation
import TetraStereo.OneCenter.LocalizedOuterDigraphConstitutionalPriority
import TetraStereo.OneCenter.OfficialRuleMajorKey
import TetraStereo.UniversalProof.NextFrontier.NativeRingRuntimeGraphFacts
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 8192


















namespace TetraStereo.OneCenter.LocalizedCyclicSpatialRootLetter

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.LocalizedRuleMajorReference
open TetraStereo.OneCenter.DeclarativeCIP
open TetraStereo.OneCenter.LocalizedCyclicInputWitness
open TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness
open TetraStereo.OneCenter.LocalizedCyclicSpatialDescriptorWitness
open TetraStereo.OneCenter.MoleculeGraph
open TetraStereo.OneCenter.CartesianPoint3
open TetraStereo.OneCenter.OfficialCIPNode
open TetraStereo.OneCenter.SemanticMolecule
open TetraStereo.OneCenter.SemanticInteraction
open TetraStereo.OneCenter.ConstitutionalLexAlgebra
open TetraStereo.UniversalProof.NativeRingDomain
open TetraStereo.UniversalProof.NativeRingHydrogenFacts
open TetraStereo.UniversalProof.GeneralRingPhysicalAdmission
open TetraStereo.UniversalProof.NativeRingRuntimeGraphFacts
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery

noncomputable section
open scoped Classical

abbrev spatialRootTarget : cyclicSpatialCertified.LocalizedCIPOccurrence
    (carrierFuel cyclicSpatialReference) :=
  cyclicSpatialCertified.localizedFinalOccurrenceExecutable
    (carrierFuel cyclicSpatialReference) spatialRootCenter

abbrev spatialRootFrames : ContextFrameCompilation cyclicSpatialReference spatialRootTarget
    (finalCenterUnit cyclicSpatialReference spatialRootCenter)
    (finalOccurrence_molecularFrameUnit cyclicSpatialReference spatialRootCenter) :=
  cyclicContextFrameCompilation cyclicSpatialReference spatial_simpleBonded spatialRootTarget
    (finalOccurrence_provenance_real cyclicSpatialReference spatialRootCenter)
    (finalCenterUnit cyclicSpatialReference spatialRootCenter)
    (finalOccurrence_molecularFrameUnit cyclicSpatialReference spatialRootCenter)

private theorem priority_volume : orientedVolume P1 P2 P4 P5 = -24 := by
  simp only [CartesianPoint3.orientedVolume, P1, P2, P4, P5]
  norm_num

/-! ## Graph atomic numbers and record adjacency -/

private theorem semanticConverted :
    cyclicExpanded.toSemanticMolecule? = some cyclicSource.molecule :=
  cyclicExpanded.toAuthoritativeChemicalInput?_molecule cyclicSource source_conversion

private theorem cyclicExpandedWell : cyclicExpanded.WellFormed :=
  (expanded_stereochemical_admissible 0 TetrahedralInputParity.anticlockwise).1.1

private theorem covalentRecord_of_single (bond : RawBond)
    (member : bond ∈ cyclicExpanded.bonds) :
    bond.toSemanticInteraction.localizedCovalentRecord? = some (bond.edgeKey, 1) := by
  rw [localizedCovalentRecord?_toSemanticInteraction]
  have single := expanded_bonds_single 0 TetrahedralInputParity.anticlockwise bond member
  simp [single, ParsedBondKind.localizedBondOrder?]

private theorem connects_semantic (bond : RawBond) (left right : ℕ) :
    bond.connects left right = true ↔
      semanticEdgeKey bond.source bond.target = semanticEdgeKey left right := by
  rcases bond with ⟨source, target, _⟩
  simp only [semanticEdgeKey, RawBond.connects, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  by_cases sourceTarget : source ≤ target <;>
    by_cases leftRight : left ≤ right <;>
      simp [Nat.min_def, Nat.max_def, sourceTarget, leftRight] <;> omega

private theorem record_order_one {key : ℕ × ℕ} {order : ℕ}
    (present : (key, order) ∈ cyclicSource.molecule.localizedCovalentRecords) :
    order = 1 := by
  rw [SemanticMolecule.localizedCovalentRecords, List.mem_filterMap] at present
  obtain ⟨interaction, interactionMember, observed⟩ := present
  rw [cyclicExpanded.toSemanticMolecule?_interactions cyclicSource.molecule semanticConverted,
    List.mem_map] at interactionMember
  obtain ⟨bond, bondMember, bondEq⟩ := interactionMember
  have recorded := covalentRecord_of_single bond bondMember
  rw [← bondEq] at observed
  exact ((Prod.mk.inj (Option.some.inj (recorded.symm.trans observed))).2).symm

private theorem semanticRecord_iff (left right : ℕ) :
    (semanticEdgeKey left right, 1) ∈ cyclicSource.molecule.localizedCovalentRecords ↔
      ∃ bond ∈ cyclicExpanded.bonds, bond.connects left right = true := by
  constructor
  · intro present
    rw [SemanticMolecule.localizedCovalentRecords, List.mem_filterMap] at present
    obtain ⟨interaction, interactionMember, observed⟩ := present
    rw [cyclicExpanded.toSemanticMolecule?_interactions cyclicSource.molecule semanticConverted,
      List.mem_map] at interactionMember
    obtain ⟨bond, bondMember, bondEq⟩ := interactionMember
    have recorded := covalentRecord_of_single bond bondMember
    rw [← bondEq] at observed
    have pair := Option.some.inj (recorded.symm.trans observed)
    exact ⟨bond, bondMember, (connects_semantic bond left right).mpr (Prod.mk.inj pair).1⟩
  · rintro ⟨bond, bondMember, connects⟩
    rw [SemanticMolecule.localizedCovalentRecords,
      cyclicExpanded.toSemanticMolecule?_interactions cyclicSource.molecule semanticConverted,
      List.mem_filterMap]
    refine ⟨bond.toSemanticInteraction, List.mem_map.mpr ⟨bond, bondMember, rfl⟩, ?_⟩
    rw [covalentRecord_of_single bond bondMember]
    rw [show bond.edgeKey = semanticEdgeKey bond.source bond.target from rfl]
    rw [(connects_semantic bond left right).mp connects]

private theorem source_neighbor_mem (center neighbor : cyclicCertified.Atom) :
    cyclicCertified.moleculeGraph.Adj center neighbor ↔
      neighbor.val ∈ recordNeighbors cyclicExpanded center.val := by
  constructor
  · intro adjacent
    have distinct : center ≠ neighbor := by
      intro equal
      subst neighbor
      simp [MoleculeGraph.Adj, cyclicCertified.moleculeGraph.bond_self center] at adjacent
    have distinctVal : center.val ≠ neighbor.val := fun same => distinct (Fin.ext same)
    rcases (cyclicSource.molecule.toLocalizedMoleculeGraph_adj_iff_record
        cyclicCertified.graphReady center neighbor distinct).mp adjacent with
      ⟨order, present, _⟩
    rw [record_order_one present] at present
    obtain ⟨bond, bondMember, connects⟩ :=
      (semanticRecord_iff center.val neighbor.val).mp present
    exact (recordNeighbor_positive_iff cyclicExpanded cyclicExpandedWell
      center.val neighbor.val).mpr
        ((cyclicExpanded.bondOrder_pos_iff_exists_bond distinctVal).mpr
          ⟨bond, bondMember, connects⟩)
  · intro member
    have distinctVal : center.val ≠ neighbor.val :=
      Ne.symm (recordNeighbor_bounds cyclicExpandedWell member).2
    have distinct : center ≠ neighbor := fun equal => distinctVal (congrArg Fin.val equal)
    obtain ⟨bond, bondMember, connects⟩ :=
      (cyclicExpanded.bondOrder_pos_iff_exists_bond distinctVal).mp
        ((recordNeighbor_positive_iff cyclicExpanded cyclicExpandedWell
          center.val neighbor.val).mp member)
    have present := (semanticRecord_iff center.val neighbor.val).mpr
      ⟨bond, bondMember, connects⟩
    have bondOne := cyclicSource.molecule.toLocalizedMoleculeGraph_bond_eq_of_record
      center neighbor 1 cyclicCertified.graphReady distinct present
    have graphOne : cyclicCertified.moleculeGraph.bond center neighbor = 1 := by
      simpa [CertifiedLocalizedCIPInput.moleculeGraph] using bondOne
    rw [MoleculeGraph.Adj, graphOne]
    exact Nat.zero_lt_one

private theorem adj_transport
    {left right : SemanticMolecule} (equal : left = right) {i j : ℕ}
    {bi : i < left.atomCount} {bj : j < left.atomCount} :
    left.toLocalizedMoleculeGraph.Adj ⟨i, bi⟩ ⟨j, bj⟩ ↔
      right.toLocalizedMoleculeGraph.Adj ⟨i, equal ▸ bi⟩ ⟨j, equal ▸ bj⟩ := by
  subst equal
  exact Iff.rfl

private theorem spatial_neighbor_mem (center neighbor : Fin 9) :
    cyclicSpatialCertified.moleculeGraph.Adj (SA center) (SA neighbor) ↔
      neighbor.val ∈ recordNeighbors cyclicExpanded center.val := by
  have source := source_neighbor_mem (atom center) (atom neighbor)
  have castEq := adj_transport molecule_eq.symm
    (i := center.val) (j := neighbor.val)
    (bi := (atom center).isLt) (bj := (atom neighbor).isLt)
  have centerCast : SA center =
      (⟨center.val, molecule_eq.symm ▸ (atom center).isLt⟩ : cyclicSpatialCertified.Atom) :=
    Fin.ext (by simp [SA_val])
  have neighborCast : SA neighbor =
      (⟨neighbor.val, molecule_eq.symm ▸ (atom neighbor).isLt⟩ : cyclicSpatialCertified.Atom) :=
    Fin.ext (by simp [SA_val])
  constructor
  · intro adjacent
    have spatialAdj := adjacent
    rw [centerCast, neighborCast] at spatialAdj
    exact source.mp ((castEq).mpr
      (by simpa [CertifiedLocalizedCIPInput.moleculeGraph] using spatialAdj))
  · intro member
    have sourceAdj := source.mpr member
    have spatialAdj := castEq.mp
      (by simpa [CertifiedLocalizedCIPInput.moleculeGraph] using sourceAdj)
    simpa [centerCast, neighborCast, CertifiedLocalizedCIPInput.moleculeGraph] using spatialAdj

private theorem record_perm (center : ℕ) (values : List ℕ)
    (bound : center < 9) (written : cyclicExpanded.writtenNeighbors center = values) :
    (recordNeighbors cyclicExpanded center).Perm values := by
  have perm := expanded_records_perm_written 0 TetrahedralInputParity.anticlockwise center
    (by omega)
  simpa [cyclicExpanded, written] using perm

private theorem root_record_perm : (recordNeighbors cyclicExpanded 0).Perm [5, 1, 2, 4] :=
  record_perm 0 [5, 1, 2, 4] (by decide) root_written_row

private theorem arm_record_perm : (recordNeighbors cyclicExpanded 2).Perm [0, 6, 3, 4] :=
  record_perm 2 [0, 6, 3, 4] (by decide) arm_written_row

private theorem closing_record_perm : (recordNeighbors cyclicExpanded 4).Perm [2, 7, 8, 0] :=
  record_perm 4 [2, 7, 8, 0] (by decide) closing_written_row

private theorem root_neighbor_iff (neighbor : Fin 9) :
    cyclicSpatialCertified.moleculeGraph.Adj (SA ⟨0, by decide⟩) (SA neighbor) ↔
      neighbor.val ∈ [5, 1, 2, 4] := by
  rw [spatial_neighbor_mem]
  exact (root_record_perm).mem_iff

private theorem arm_neighbor_iff (neighbor : Fin 9) :
    cyclicSpatialCertified.moleculeGraph.Adj (SA ⟨2, by decide⟩) (SA neighbor) ↔
      neighbor.val ∈ [0, 6, 3, 4] := by
  rw [spatial_neighbor_mem]
  exact arm_record_perm.mem_iff

private theorem closing_neighbor_iff (neighbor : Fin 9) :
    cyclicSpatialCertified.moleculeGraph.Adj (SA ⟨4, by decide⟩) (SA neighbor) ↔
      neighbor.val ∈ [2, 7, 8, 0] := by
  rw [spatial_neighbor_mem]
  exact closing_record_perm.mem_iff

private theorem spatial_graph_atomicNumber (index : Fin 9) (spec : AtomSpec)
    (lookup : cyclicExpanded.atomAt? index.val = some spec) :
    cyclicSpatialCertified.moleculeGraph.atomZ (SA index) = spec.element.atomicNumber := by
  let rawIndex : Fin cyclicExpanded.atomCount :=
    ⟨index.val, by rw [expandedAtomCount]; exact index.isLt⟩
  obtain ⟨sourceAtom, semanticListed, converted⟩ :=
    cyclicExpanded.toSemanticMolecule?_atomAtFin cyclicSpatialSource.molecule
      spatial_agreement.1.1 rawIndex
  have rawBound : index.val < cyclicExpanded.atoms.length := by
    rw [← RawMolecule.atomCount, expandedAtomCount]
    exact index.isLt
  have rawGet : cyclicExpanded.atoms.get ⟨index.val, rawBound⟩ = spec := by
    apply Option.some.inj
    exact (listGet?_eq_some_get cyclicExpanded.atoms ⟨index.val, rawBound⟩).symm.trans
      (by simpa [RawMolecule.atomAt?] using lookup)
  have convertedSpec : spec.toSemanticAtom? = some sourceAtom := by
    rw [← rawGet]
    simpa [RawMolecule.atomCount, rawIndex] using converted
  have numberEq := (AtomSpec.toSemanticAtom?_exact spec sourceAtom convertedSpec).1
  have semCount := cyclicExpanded.toSemanticMolecule?_atomCount cyclicSpatialSource.molecule
    spatial_agreement.1.1
  have semanticBound : index.val < cyclicSpatialSource.molecule.atoms.length := by
    have countBound : index.val < cyclicSpatialSource.molecule.atomCount := by
      rw [semCount, expandedAtomCount]
      exact index.isLt
    simpa [SemanticMolecule.atomCount] using countBound
  have semanticGet : cyclicSpatialSource.molecule.atoms.get ⟨index.val, semanticBound⟩ =
      sourceAtom := by
    apply Option.some.inj
    exact (listGet?_eq_some_get cyclicSpatialSource.molecule.atoms
      ⟨index.val, semanticBound⟩).symm.trans semanticListed
  simp only [CertifiedLocalizedCIPInput.moleculeGraph,
    SemanticMolecule.toLocalizedMoleculeGraph_atomZ, cyclicSpatialCertified, SA,
    semanticGet, numberEq]

private theorem atomicNumber_at (index : Fin 9) (z : ℕ)
    (fact : ∃ spec, cyclicExpanded.atomAt? index.val = some spec ∧
      spec.element.atomicNumber = z) :
    cyclicSpatialCertified.moleculeGraph.atomZ (SA index) = z := by
  obtain ⟨spec, lookup, hz⟩ := fact
  rw [spatial_graph_atomicNumber index spec lookup, hz]

private theorem z_fluorine : cyclicSpatialCertified.moleculeGraph.atomZ (SA ⟨1, by decide⟩) = 9 :=
  atomicNumber_at ⟨1, by decide⟩ 9 (by
    obtain ⟨spec, lookup, _, z⟩ := fluorine_source_atomicNumber
    exact ⟨spec, lookup, z⟩)

private theorem z_arm : cyclicSpatialCertified.moleculeGraph.atomZ (SA ⟨2, by decide⟩) = 6 :=
  atomicNumber_at ⟨2, by decide⟩ 6 (by
    obtain ⟨spec, lookup, _, z⟩ := armCarbon_source_atomicNumber
    exact ⟨spec, lookup, z⟩)

private theorem z_chlorine : cyclicSpatialCertified.moleculeGraph.atomZ (SA ⟨3, by decide⟩) = 17 :=
  atomicNumber_at ⟨3, by decide⟩ 17 (by
    obtain ⟨spec, lookup, _, z⟩ := chlorine_source_atomicNumber
    exact ⟨spec, lookup, z⟩)

private theorem z_closing : cyclicSpatialCertified.moleculeGraph.atomZ (SA ⟨4, by decide⟩) = 6 :=
  atomicNumber_at ⟨4, by decide⟩ 6 (by
    obtain ⟨spec, lookup, _, z⟩ := closingCarbon_source_atomicNumber
    exact ⟨spec, lookup, z⟩)

private theorem z_hydrogenFive :
    cyclicSpatialCertified.moleculeGraph.atomZ (SA ⟨5, by decide⟩) = 1 :=
  atomicNumber_at ⟨5, by decide⟩ 1 (by
    obtain ⟨spec, lookup, _, z⟩ := hydrogenFive_source_atomicNumber
    exact ⟨spec, lookup, z⟩)

private theorem z_terminal (index : Fin 9) (low : 5 ≤ index.val) (high : index.val < 9) :
    cyclicSpatialCertified.moleculeGraph.atomZ (SA index) = 1 :=
  atomicNumber_at index 1 (by
    obtain ⟨spec, lookup, _, z⟩ := terminalHydrogen_source_atomicNumber index.val low high
    exact ⟨spec, lookup, z⟩)

/-! ## Constitutional shape of one compiled arm -/

private theorem node_label_atomicNumber
    (node : OfficialCIPNode cyclicSpatialCertified.Atom) (atom : cyclicSpatialCertified.Atom)
    (current : node.current? = some atom) :
    (ofLex (cyclicSpatialCertified.moleculeGraph.officialNodeAtomLabel node)).1 =
      cyclicSpatialCertified.moleculeGraph.atomZ atom := by
  cases provenance : node.provenance <;>
    simp [MoleculeGraph.officialNodeAtomLabel, current, provenance, MoleculeGraph.rawCIPAtomLabel,
      ofLex_toLex]

private theorem declarative_head {fuel : Nat}
    {cursor : cyclicSpatialCertified.LocalizedRerootCursor (carrierFuel cyclicSpatialReference)}
    {key : OfficialRuleMajorKey cyclicSpatialCertified.Atom}
    (derived : cyclicSpatialCertified.DeclarativeLocalizedRerootRuleMajorKey fuel cursor key) :
    key.rule1a.head? = some [([], (ofLex
      (cyclicSpatialCertified.moleculeGraph.officialNodeAtomLabel cursor.occurrence.1.node)).1)] := by
  cases derived with
  | terminal _ _ =>
      simp [MoleculeGraph.officialRuleMajorRootKey]
  | branch _ _ _ _ _ =>
      simp [OfficialRuleMajorKey.assemble, MoleculeGraph.officialRuleMajorRootKey]

private theorem sphere_of_head {V : Type*} {key : OfficialRuleMajorKey V} {z : ℕ}
    (head : key.rule1a.head? = some [([], z)]) :
    key.rule1a.getD 0 [] = [([], z)] := by
  cases rule : key.rule1a with
  | nil => simp [rule] at head
  | cons first rest =>
      simp [rule] at head
      exact head

private theorem stage_derived (slot : Fin 4) :
    cyclicSpatialCertified.DeclarativeLocalizedRerootRuleMajorKey
      (2 * (carrierFuel cyclicSpatialReference + 1)) (spatialRootFrames.frame.cursorAt slot)
      (spatialRootFrames.stages slot).a.key.constitutional := by
  have built := (spatialRootFrames.stages slot).a.built
  rw [cyclicSpatialReference.certified.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized] at built
  exact cyclicSpatialReference.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_declarative
    .rule4a (contextOccurrenceRead cyclicSpatialReference spatialRootTarget)
    (2 * (carrierFuel cyclicSpatialReference + 1)) (spatialRootFrames.frame.cursorAt slot)
    (spatialRootFrames.stages slot).a.key built

private theorem stage_rule4a (slot : Fin 4) :
    (spatialRootFrames.compounds slot).prior.rule4aKey = (spatialRootFrames.stages slot).a.key := by
  let view := contextOccurrenceView cyclicSpatialReference spatialRootTarget
  let read := fun source =>
    cyclicSpatialCertified.localizedDependencyLabel spatialRootTarget view source
  have uniformBuilt :
      cyclicSpatialCertified.buildRuleMajorCompoundRule45KeyWith?
        (fun stage position => cyclicSpatialCertified.buildRuleMajorCumulativeWithRead? stage read
          (2 * (carrierFuel cyclicSpatialReference + 1)) position)
        (spatialRootFrames.frame.cursorAt slot) = some (spatialRootFrames.compounds slot) := by
    rw [← cyclicSpatialCertified.buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor]
    rw [← cyclicSpatialCertified.buildActualRuleMajorCompoundRule45KeyExec?_eq]
    exact spatialRootFrames.compoundBuilt slot
  exact (cyclicSpatialCertified.contextStages_compound_readback
    (spatialRootFrames.stages slot) uniformBuilt).1

private theorem slot_head (slot : Fin 4) :
    (spatialRootFrames.stages slot).a.key.constitutional.rule1a.head? =
      some [([], cyclicSpatialCertified.moleculeGraph.atomZ
        (spatialRootFrames.actualLigandAtoms slot))] := by
  have derived := stage_derived slot
  have head := declarative_head derived
  have current := spatialRootFrames.ligandAt slot
  rw [node_label_atomicNumber _ _ current] at head
  simpa [ContextFrameCompilation.actualLigandAtoms] using head

private theorem compare_gt_of_heads
    {left right : OfficialRuleMajorKey cyclicSpatialCertified.Atom} {leftZ rightZ : ℕ}
    (leftHead : left.rule1a.head? = some [([], leftZ)])
    (rightHead : right.rule1a.head? = some [([], rightZ)])
    (higher : rightZ < leftZ) :
    OfficialRuleMajorKey.compare left right = Ordering.gt := by
  have layers := officialRuleMajorKey_compare_rule1a_gt_of_heads_gt leftHead rightHead higher
  rw [OfficialRuleMajorKey.compare_eq_rule1a_of_decisive (by rw [layers]; decide), layers]

/-! ## Second-sphere head of an assembled branch -/

private theorem le_foldl_max {β : Type*} (measure : β → ℕ) :
    ∀ (children : List β) (accumulator : ℕ),
      accumulator ≤ children.foldl (fun longest child => max longest (measure child)) accumulator
  | [], _ => Nat.le_refl _
  | head :: tail, accumulator => by
      simp only [List.foldl_cons]
      exact Nat.le_trans (Nat.le_max_left accumulator (measure head))
        (le_foldl_max measure tail (max accumulator (measure head)))

private theorem getD_zero_map_range {γ : Type*} {count : ℕ} (positive : 0 < count)
    (f : ℕ → γ) (fallback : γ) :
    ((List.range count).map f).getD 0 fallback = f 0 := by
  cases count with
  | zero => exact absurd positive (Nat.lt_irrefl 0)
  | succ _ =>
      rw [List.range_succ_eq_map]
      rfl

private theorem merge_first_head {V : Type*}
    (head : OfficialRuleMajorKey V) (tail : List (OfficialRuleMajorKey V)) {z : ℕ}
    (sphere : head.rule1a.getD 0 [] = [([], z)]) :
    ((OfficialRuleMajorKey.mergeChildren (head :: tail) OfficialRuleMajorKey.rule1a).getD
      0 []).head? = some ([0], z) := by
  have present : head.rule1a ≠ [] := by
    intro empty
    rw [empty] at sphere
    simp at sphere
  have countPos : 0 < OfficialRuleMajorKey.childLayerCount (head :: tail)
      OfficialRuleMajorKey.rule1a := by
    unfold OfficialRuleMajorKey.childLayerCount
    simp only [List.foldl_cons, Nat.zero_max]
    exact Nat.lt_of_lt_of_le (List.length_pos_iff.mpr present)
      (le_foldl_max (fun child : OfficialRuleMajorKey V => child.rule1a.length) tail
        head.rule1a.length)
  unfold OfficialRuleMajorKey.mergeChildren
  rw [getD_zero_map_range countPos, List.zipIdx_cons, List.flatMap_cons, sphere]
  simp [OfficialRuleMajorKey.prefixLayer, List.head?_cons]

private theorem assemble_second_head {V : Type*} [Fintype V] [DecidableEq V]
    (graph : MoleculeGraph V) (node : OfficialCIPNode V)
    (sorted : List (OfficialRuleMajorKey V)) {z : ℕ} (nonempty : sorted ≠ [])
    (sphere : (sorted.head nonempty).rule1a.getD 0 [] = [([], z)]) :
    ((OfficialRuleMajorKey.assemble (graph.officialRuleMajorRootKey node false) sorted).rule1a.getD
      1 []).head? = some ([0], z) := by
  cases sorted with
  | nil => exact (nonempty rfl).elim
  | cons head tail =>
      have sphere' : head.rule1a.getD 0 [] = [([], z)] := by simpa using sphere
      have merged := merge_first_head head tail sphere'
      simpa [OfficialRuleMajorKey.assemble, MoleculeGraph.officialRuleMajorRootKey,
        List.singleton_append, List.getD_cons_succ] using merged

private theorem cons_of_getD_zero {α : Type*} {l : List α} {a fallback : α}
    (h : l.getD 0 fallback = a) (ne : a ≠ fallback) : ∃ tail, l = a :: tail := by
  cases l with
  | nil => exact absurd h.symm ne
  | cons head tail =>
      simp at h
      exact ⟨tail, by rw [h]⟩

private theorem compareNat_self (z : ℕ) : OfficialRuleMajorKey.compareNat z z = Ordering.eq := by
  simp [OfficialRuleMajorKey.compareNat]

private theorem singleton_layer_eq (z : ℕ) :
    OfficialRuleMajorKey.compareSparseLayer OfficialRuleMajorKey.compareNat
      [([], z)] [([], z)] = Ordering.eq := by
  simp [OfficialRuleMajorKey.compareSparseLayer, OfficialRuleMajorKey.compareSparseEntry,
    List.compareLex, compareLex, Ordering.byKey, flip, compareNat_self]

private theorem entry_gt (a b : ℕ) (higher : b < a) :
    OfficialRuleMajorKey.compareSparseEntry OfficialRuleMajorKey.compareNat
      ([0], a) ([0], b) = Ordering.gt := by
  have compared : OfficialRuleMajorKey.compareNat a b = Ordering.gt :=
    compare_gt_iff_gt.mpr higher
  unfold OfficialRuleMajorKey.compareSparseEntry compareLex Ordering.byKey
  simp only [List.compareLex, flip, compared]
  rw [compareNat_self]
  rfl

private theorem rule1a_gt_of_second_sphere
    {left right : OfficialRuleMajorKey cyclicSpatialCertified.Atom} {z a b : ℕ}
    (left0 : left.rule1a.getD 0 [] = [([], z)])
    (right0 : right.rule1a.getD 0 [] = [([], z)])
    (left1 : (left.rule1a.getD 1 []).head? = some ([0], a))
    (right1 : (right.rule1a.getD 1 []).head? = some ([0], b))
    (higher : b < a) :
    OfficialRuleMajorKey.compare left right = Ordering.gt := by
  obtain ⟨leftTail, leftEq⟩ := cons_of_getD_zero left0 (by simp)
  obtain ⟨rightTail, rightEq⟩ := cons_of_getD_zero right0 (by simp)
  have leftMore : ∃ layer rest, leftTail = layer :: rest ∧ layer.head? = some ([0], a) := by
    cases leftTail with
    | nil => simp [leftEq] at left1
    | cons layer rest => exact ⟨layer, rest, rfl, by simpa [leftEq] using left1⟩
  obtain ⟨leftLayer, leftRest, leftTailEq, leftHead⟩ := leftMore
  have rightMore : ∃ layer rest, rightTail = layer :: rest ∧ layer.head? = some ([0], b) := by
    cases rightTail with
    | nil => simp [rightEq] at right1
    | cons layer rest => exact ⟨layer, rest, rfl, by simpa [rightEq] using right1⟩
  obtain ⟨rightLayer, rightRest, rightTailEq, rightHead⟩ := rightMore
  have leftEntries : ∃ rest, leftLayer = ([0], a) :: rest := by
    cases leftLayer with
    | nil => simp at leftHead
    | cons entry rest =>
        simp at leftHead
        exact ⟨rest, by rw [leftHead]⟩
  obtain ⟨leftEntries, leftLayerEq⟩ := leftEntries
  have rightEntries : ∃ rest, rightLayer = ([0], b) :: rest := by
    cases rightLayer with
    | nil => simp at rightHead
    | cons entry rest =>
        simp at rightHead
        exact ⟨rest, by rw [rightHead]⟩
  obtain ⟨rightEntries, rightLayerEq⟩ := rightEntries
  have layerGt : OfficialRuleMajorKey.compareSparseLayer OfficialRuleMajorKey.compareNat
      leftLayer rightLayer = Ordering.gt := by
    rw [leftLayerEq, rightLayerEq]
    simp [OfficialRuleMajorKey.compareSparseLayer, List.compareLex, entry_gt a b higher]
  have layersGt : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      left.rule1a right.rule1a = Ordering.gt := by
    rw [leftEq, rightEq, leftTailEq, rightTailEq]
    simp [OfficialRuleMajorKey.compareSparseLayers, List.compareLex,
      singleton_layer_eq z, layerGt]
  rw [OfficialRuleMajorKey.compare_eq_rule1a_of_decisive (by rw [layersGt]; decide), layersGt]

/-! ## Ligand cursors are the root's outward children -/

private theorem occurrence_frame :
    cyclicSpatialCertified.localizedOccurrenceFourLigandFrame? spatialRootTarget =
      some spatialRootFrames.frame := by
  rw [← cyclicSpatialCertified.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?
    spatialRootTarget]
  exact spatialRootFrames.frameComputed

private theorem center_val : spatialRootFrames.center.val = SA ⟨0, by decide⟩ := by
  rw [spatialRootFrames.centerEq, finalCenterUnit, OccurrenceUnit.atom]
  simp [List.getLast?, spatialRootCenter]

private theorem root_node :
    spatialRootTarget.1.node = OfficialCIPNode.root (SA ⟨0, by decide⟩) := by
  unfold spatialRootTarget CertifiedLocalizedCIPInput.localizedFinalOccurrenceExecutable
    CertifiedLocalizedCIPInput.localizedFinalRootFrame spatialRootCenter
  rfl

private theorem cursor_present (slot : Fin 4) :
    spatialRootFrames.frame.cursorAt slot ∈ spatialRootFrames.frame.cursors := by
  rw [LocalizedOccurrenceFourLigandFrame.cursorAt]
  exact List.get_mem spatialRootFrames.frame.cursors
    (Fin.cast spatialRootFrames.frame.length_eq.symm slot)

private structure SlotShape (slot : Fin 4) : Prop where
  nodeEq : (spatialRootFrames.frame.cursorAt slot).occurrence.1.node =
    (OfficialCIPNode.root (SA ⟨0, by decide⟩)).extend
      (spatialRootFrames.actualLigandAtoms slot) 0
  parent : (spatialRootFrames.frame.cursorAt slot).occurrence.1.node.parent? =
    some (SA ⟨0, by decide⟩)
  real : (spatialRootFrames.frame.cursorAt slot).occurrence.1.node.provenance =
    OfficialCIPNodeProvenance.realAtom
  duplicateFree : (spatialRootFrames.frame.cursorAt slot).occurrence.1.node.isDuplicateLeaf = false
  previous : (spatialRootFrames.frame.cursorAt slot).previous? = some spatialRootTarget
  sameRoot : spatialRootTarget.1.root =
    (spatialRootFrames.frame.cursorAt slot).occurrence.1.root
  addressDrop : spatialRootTarget.1.address =
    (spatialRootFrames.frame.cursorAt slot).occurrence.1.address.dropLast
  addressStep : spatialRootTarget.1.address.length + 1 =
    (spatialRootFrames.frame.cursorAt slot).occurrence.1.address.length

private theorem slotShape (slot : Fin 4) : SlotShape slot := by
  have previous := cyclicSpatialCertified.localizedOccurrenceFourLigandFrame_cursor_previous
    spatialRootTarget spatialRootFrames.frame occurrence_frame _ (cursor_present slot)
  have sameRoot := cyclicSpatialCertified.localizedOccurrenceFourLigandFrame_cursor_root
    spatialRootTarget spatialRootFrames.frame occurrence_frame _ (cursor_present slot)
  have neighborMem :=
    cyclicSpatialCertified.localizedOccurrenceFourLigandFrame_cursor_mem_neighborFrames
      spatialRootTarget spatialRootFrames.frame occurrence_frame _
      (cursor_present slot)
  have outwardEq :=
    cyclicSpatialCertified.localizedRerootNeighborFrames_eq_outwardChildFrames_of_address_nil
      spatialRootTarget spatialRoot_address
  have outwardMem : (spatialRootFrames.frame.cursorAt slot).occurrence.1 ∈
      cyclicSpatialCertified.localizedCarrierOutwardChildFrames
        (fuel := carrierFuel cyclicSpatialReference) spatialRootTarget.1 := by
    rw [← outwardEq]
    exact neighborMem
  have currentRoot : spatialRootTarget.1.node.current? = some (SA ⟨0, by decide⟩) := by
    simp [OfficialCIPNode.root, spatialRootTarget,
      CertifiedLocalizedCIPInput.localizedFinalOccurrenceExecutable,
      CertifiedLocalizedCIPInput.localizedFinalRootFrame, spatialRootCenter]
  obtain ⟨w, childSlot, nodeEq, current, _rootEq, addressEq, _zip, _notParent, graphAdjacent⟩ :=
    cyclicSpatialCertified.simpleBond_outwardFrame_extend_zero spatial_simpleBonded
      spatialRootTarget currentRoot spatialRoot_provenance _
      outwardMem
  have ligandCurrent := spatialRootFrames.ligandAt slot
  have wEq : w = spatialRootFrames.actualLigandAtoms slot := by
    apply Option.some.inj
    rw [← current]
    simpa [ContextFrameCompilation.actualLigandAtoms] using ligandCurrent
  have nodeEq' : (spatialRootFrames.frame.cursorAt slot).occurrence.1.node =
      (OfficialCIPNode.root (SA ⟨0, by decide⟩)).extend w 0 := by
    rw [nodeEq, root_node]
  have parent : (spatialRootFrames.frame.cursorAt slot).occurrence.1.node.parent? =
      some (SA ⟨0, by decide⟩) := by
    rw [nodeEq']
    simp [OfficialCIPNode.extend, OfficialCIPNode.root, OfficialCIPNode.parent?]
  have notHistory : w ∉ (OfficialCIPNode.root (SA ⟨0, by decide⟩)).history := by
    simp only [OfficialCIPNode.root, List.mem_singleton]
    intro equal
    have loop : cyclicSpatialCertified.moleculeGraph.Adj w w := by
      simpa [equal] using graphAdjacent
    simp [MoleculeGraph.Adj, cyclicSpatialCertified.moleculeGraph.bond_self] at loop
  have real : (spatialRootFrames.frame.cursorAt slot).occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom := by
    rw [nodeEq', OfficialCIPNode.extend, OfficialCIPNode.childProvenance]
    simp only [if_neg notHistory, if_true]
  have duplicateFree :=
    cyclicSpatialCertified.isDuplicateLeaf_eq_false_of_provenance_real _ real
  have addressNil : (spatialRootFrames.frame.cursorAt slot).occurrence.1.address = [childSlot] := by
    simpa [spatialRoot_address] using addressEq
  refine {
    nodeEq := by rw [← wEq]; exact nodeEq'
    parent := parent
    real := real
    duplicateFree := duplicateFree
    previous := previous
    sameRoot := sameRoot.symm
    addressDrop := by simp [addressNil]
    addressStep := by simp [addressNil] }

private theorem outward_perm (slot : Fin 4) (shape : SlotShape slot) :
    (cyclicSpatialCertified.intendedLocalizedRerootChildFrames
      (spatialRootFrames.frame.cursorAt slot)).Perm
      (cyclicSpatialCertified.localizedCarrierOutwardChildFrames
        (fuel := carrierFuel cyclicSpatialReference)
        (spatialRootFrames.frame.cursorAt slot).occurrence.1) :=
  cyclicSpatialCertified.intendedLocalizedRerootChildFrames_perm_outward
    (spatialRootFrames.frame.cursorAt slot) spatialRootTarget shape.previous shape.sameRoot
    shape.addressDrop shape.addressStep shape.duplicateFree

private theorem fuel_enough :
    cyclicSpatialCertified.certified.input.molecule.atomCount ≤
      carrierFuel cyclicSpatialReference := by
  rw [spatialAtomCount, spatialRoot_fuel]
  decide

private def indexOf (atom : cyclicSpatialCertified.Atom) : Fin 9 :=
  ⟨atom.val, by rw [← spatialAtomCount]; exact atom.isLt⟩

private theorem indexOf_eq (atom : cyclicSpatialCertified.Atom) : atom = SA (indexOf atom) :=
  Fin.ext (by simp [indexOf, SA_val])

private theorem slot_of_atom (index : Fin 9)
    (adjacent : cyclicSpatialCertified.moleculeGraph.Adj (SA ⟨0, by decide⟩) (SA index)) :
    ∃ slot : Fin 4, spatialRootFrames.actualLigandAtoms slot = SA index := by
  have adjacentCenter : cyclicSpatialCertified.moleculeGraph.Adj spatialRootFrames.center.val
      (SA index) := by
    rw [center_val]
    exact adjacent
  obtain ⟨i, atomEq⟩ :=
    cyclicSpatialCertified.detectedMultiCenterMolecule.ligandAtomAt_surjective
      spatialRootFrames.center (SA index) adjacentCenter
  refine ⟨spatialRootFrames.detectedLigandPermutation.symm i, ?_⟩
  unfold cyclicSpatialReference
  simp [ContextFrameCompilation.actualLigandAtoms, Equiv.apply_symm_apply, atomEq]

private theorem slot_mem (slot : Fin 4) :
    (indexOf (spatialRootFrames.actualLigandAtoms slot)).val ∈ [5, 1, 2, 4] := by
  have raw := cyclicSpatialCertified.detectedMultiCenterMolecule.ligandAtomAt_adj
    spatialRootFrames.center (spatialRootFrames.detectedLigandPermutation slot)
  rw [center_val] at raw
  have ligandEq : spatialRootFrames.actualLigandAtoms slot =
      cyclicSpatialCertified.detectedMultiCenterMolecule.ligandAtomAt
        spatialRootFrames.center (spatialRootFrames.detectedLigandPermutation slot) := by
    unfold cyclicSpatialReference
    simp [ContextFrameCompilation.actualLigandAtoms]
  rw [← ligandEq, indexOf_eq (spatialRootFrames.actualLigandAtoms slot)] at raw
  exact (root_neighbor_iff _).mp raw

/-! ## Carbon arms: the unique senior child decides sphere 2 -/

private theorem list_key_of_mem {fuel : Nat}
    {cursors : List (cyclicSpatialCertified.LocalizedRerootCursor
      (carrierFuel cyclicSpatialReference))}
    {keys : List (OfficialRuleMajorKey cyclicSpatialCertified.Atom)}
    (derived : cyclicSpatialCertified.DeclarativeLocalizedRerootRuleMajorKeyList
      fuel cursors keys)
    {cursor : cyclicSpatialCertified.LocalizedRerootCursor (carrierFuel cyclicSpatialReference)}
    (present : cursor ∈ cursors) :
    ∃ key, key ∈ keys ∧
      cyclicSpatialCertified.DeclarativeLocalizedRerootRuleMajorKey fuel cursor key := by
  cases derived with
  | nil _ => simp at present
  | cons head tail =>
      simp at present
      rcases present with rfl | later
      · exact ⟨_, List.mem_cons_self, head⟩
      · obtain ⟨key, mem, derivedKey⟩ := list_key_of_mem tail later
        exact ⟨key, List.mem_cons_of_mem _ mem, derivedKey⟩
termination_by cursors.length

private theorem child_key_head {fuel : Nat}
    {cursor : cyclicSpatialCertified.LocalizedRerootCursor (carrierFuel cyclicSpatialReference)}
    {key : OfficialRuleMajorKey cyclicSpatialCertified.Atom}
    (derived : cyclicSpatialCertified.DeclarativeLocalizedRerootRuleMajorKey fuel cursor key)
    {atom : cyclicSpatialCertified.Atom}
    (current : cursor.occurrence.1.node.current? = some atom) :
    key.rule1a.head? = some [([], cyclicSpatialCertified.moleculeGraph.atomZ atom)] := by
  rw [declarative_head derived, node_label_atomicNumber _ _ current]

private theorem list_cursor_of_key {fuel : Nat}
    {cursors : List (cyclicSpatialCertified.LocalizedRerootCursor
      (carrierFuel cyclicSpatialReference))}
    {keys : List (OfficialRuleMajorKey cyclicSpatialCertified.Atom)}
    (derived : cyclicSpatialCertified.DeclarativeLocalizedRerootRuleMajorKeyList
      fuel cursors keys)
    {key : OfficialRuleMajorKey cyclicSpatialCertified.Atom}
    (present : key ∈ keys) :
    ∃ cursor, cursor ∈ cursors ∧
      cyclicSpatialCertified.DeclarativeLocalizedRerootRuleMajorKey fuel cursor key := by
  cases derived with
  | nil _ => simp at present
  | cons head tail =>
      simp at present
      rcases present with rfl | later
      · exact ⟨_, List.mem_cons_self, head⟩
      · obtain ⟨cursor, mem, derivedCursor⟩ := list_cursor_of_key tail later
        exact ⟨cursor, List.mem_cons_of_mem _ mem, derivedCursor⟩
termination_by keys.length

private theorem slot_current (slot : Fin 4) (ligand : Fin 9)
    (ligandEq : spatialRootFrames.actualLigandAtoms slot = SA ligand) :
    (spatialRootFrames.frame.cursorAt slot).occurrence.1.node.current? = some (SA ligand) := by
  have shape := slotShape slot
  rw [shape.nodeEq, ligandEq]
  simp

/-! A branch key's second Rule-1a entry is the first sphere of its senior child. -/

private theorem carbon_second (slot : Fin 4) (ligand maxIndex : Fin 9)
    (neighbors : List ℕ)
    (ligandEq : spatialRootFrames.actualLigandAtoms slot = SA ligand)
    (neighborIff : ∀ n : Fin 9,
      cyclicSpatialCertified.moleculeGraph.Adj (SA ligand) (SA n) ↔ n.val ∈ neighbors)
    (maxMem : maxIndex.val ∈ neighbors) (maxNe : maxIndex.val ≠ 0) (maxZ : ℕ)
    (maxAtomic : cyclicSpatialCertified.moleculeGraph.atomZ (SA maxIndex) = maxZ)
    (bounded : ∀ n : Fin 9, n.val ∈ neighbors → n.val ≠ 0 →
      cyclicSpatialCertified.moleculeGraph.atomZ (SA n) ≤ maxZ) :
    ((spatialRootFrames.stages slot).a.key.constitutional.rule1a.getD 1 []).head? =
      some ([0], maxZ) := by
  let shape := slotShape slot
  let slotCursor := spatialRootFrames.frame.cursorAt slot
  have currentLigand := slot_current slot ligand ligandEq
  have notParent : slotCursor.occurrence.1.node.parent? ≠ some (SA maxIndex) := by
    rw [shape.parent]
    intro same
    injection same with atomEq
    have vals := congrArg (fun a : cyclicSpatialCertified.Atom => a.val) atomEq
    have zeroEq : maxIndex.val = 0 := by
      simpa [SA_val] using vals.symm
    exact maxNe zeroEq
  have adjacent := (neighborIff maxIndex).mpr maxMem
  obtain ⟨maxFrame, childSlot, addressStep, sameRootFrame, currentMax, nodeExtend, occurrenceMem,
      memOut⟩ :=
    cyclicSpatialCertified.realCenter_outwardChildFrame_of_notParent fuel_enough
      slotCursor.occurrence currentLigand adjacent notParent shape.real
  have perm := outward_perm slot shape
  have derived := stage_derived slot
  generalize _hkey : (spatialRootFrames.stages slot).a.key.constitutional = key at derived
  cases derived with
  | terminal frame empty =>
      exfalso
      have mapEq := frame.1
      simp [empty, cyclicSpatialReference] at mapEq
      have outwardPerm :
          [].Perm (cyclicSpatialCertified.localizedCarrierOutwardChildFrames
            (fuel := carrierFuel cyclicSpatialReference)
            (spatialRootFrames.frame.cursorAt slot).occurrence.1) := by
        simpa [mapEq] using perm
      have outwardNil := List.Perm.nil_eq outwardPerm
      rw [← outwardNil] at memOut
      simp at memOut
  | branch frame nonempty childDerivations ranking descending =>
      rename_i children childKeys sorted
      have keyBound : ∀ childKey, childKey ∈ childKeys →
          ∃ z, childKey.rule1a.head? = some [([], z)] ∧ z ≤ maxZ := by
        intro childKey childKeyMem
        obtain ⟨child, childMem, childDerived⟩ :=
          list_cursor_of_key childDerivations childKeyMem
        have frameEq := frame.1
        simp [cyclicSpatialReference] at frameEq
        have frameMem : child.occurrence.1 ∈
            cyclicSpatialCertified.intendedLocalizedRerootChildFrames slotCursor := by
          rw [← frameEq]
          exact List.mem_map.mpr ⟨child, childMem, rfl⟩
        have outwardFrame := perm.mem_iff.mp frameMem
        obtain ⟨w, _, _, currentW, _, _, _, notParentW, adjW⟩ :=
          cyclicSpatialCertified.simpleBond_outwardFrame_extend_zero spatial_simpleBonded
            slotCursor.occurrence currentLigand shape.real child.occurrence.1 outwardFrame
        have wNotRoot : w ≠ SA ⟨0, by decide⟩ := by
          intro equal
          exact notParentW (by rw [equal, shape.parent])
        have indexAdj : cyclicSpatialCertified.moleculeGraph.Adj (SA ligand)
            (SA (indexOf w)) := by
          rw [indexOf_eq w] at adjW
          exact adjW
        have indexMem := (neighborIff (indexOf w)).mp indexAdj
        have indexNe : (indexOf w).val ≠ 0 := by
          intro zero
          apply wNotRoot
          rw [indexOf_eq w]
          exact Fin.ext (by simpa [SA_val] using zero)
        refine ⟨cyclicSpatialCertified.moleculeGraph.atomZ w,
          child_key_head childDerived currentW, ?_⟩
        rw [indexOf_eq w]
        exact bounded (indexOf w) indexMem indexNe
      have memIntended : maxFrame ∈
          cyclicSpatialCertified.intendedLocalizedRerootChildFrames slotCursor :=
        perm.mem_iff.mpr memOut
      have frameEq := frame.1
      simp [cyclicSpatialReference] at frameEq
      rw [← frameEq] at memIntended
      obtain ⟨maxChild, maxChildMem, maxChildEq⟩ := List.mem_map.mp memIntended
      obtain ⟨maxKey, maxKeyMem, maxDerived⟩ := list_key_of_mem childDerivations maxChildMem
      have maxCurrent : maxChild.occurrence.1.node.current? = some (SA maxIndex) := by
        rw [maxChildEq]
        exact currentMax
      have maxHead := child_key_head maxDerived maxCurrent
      rw [maxAtomic] at maxHead
      cases sorted with
      | nil =>
          exact absurd (ranking.mem_iff.mpr maxKeyMem) (by simp)
      | cons headKey tail =>
          obtain ⟨z, headHead, zLe⟩ := keyBound headKey
            (ranking.mem_iff.mp List.mem_cons_self)
          have zEq : z = maxZ := by
            by_contra different
            have zlt : z < maxZ := Nat.lt_of_le_of_ne zLe different
            letI : Std.TransCmp (@OfficialRuleMajorKey.compare cyclicSpatialCertified.Atom) :=
              OfficialRuleMajorKey.compare_transCmp
            have childGt := compare_gt_of_heads maxHead headHead zlt
            have headLt : OfficialRuleMajorKey.compare headKey maxKey = Ordering.lt := by
              rw [← Std.OrientedCmp.gt_iff_lt]
              exact childGt
            have maxSorted : maxKey ∈ headKey :: tail := ranking.mem_iff.mpr maxKeyMem
            rcases List.mem_cons.mp maxSorted with same | later
            · rw [← same] at headHead
              have heads := headHead.symm.trans maxHead
              injection heads with layerEq
              injection layerEq with entryEq
              injection entryEq with addrEq zEq'
              exact different zEq'
            · exact (List.pairwise_cons.mp descending).1 maxKey later headLt
          have sphere : headKey.rule1a.getD 0 [] = [([], maxZ)] := by
            rw [sphere_of_head headHead, zEq]
          exact assemble_second_head cyclicSpatialCertified.moleculeGraph
            slotCursor.occurrence.1.node (headKey :: tail) (by simp)
            (by simpa [List.head_cons] using sphere)

private theorem arm_child_le (n : Fin 9) (mem : n.val ∈ [0, 6, 3, 4]) (neZero : n.val ≠ 0) :
    cyclicSpatialCertified.moleculeGraph.atomZ (SA n) ≤ 17 := by
  have mem' : n.val = 0 ∨ n.val = 6 ∨ n.val = 3 ∨ n.val = 4 := by
    simpa [List.mem_cons, List.mem_nil_iff, or_false] using mem
  rcases mem' with h | h | h | h
  · exact absurd h neZero
  · have : n = ⟨6, by decide⟩ := Fin.ext h
    rw [this, z_terminal ⟨6, by decide⟩ (by decide) (by decide)]
    decide
  · have : n = ⟨3, by decide⟩ := Fin.ext h
    rw [this, z_chlorine]
  · have : n = ⟨4, by decide⟩ := Fin.ext h
    rw [this, z_closing]
    decide

private theorem closing_child_le (n : Fin 9) (mem : n.val ∈ [2, 7, 8, 0]) (neZero : n.val ≠ 0) :
    cyclicSpatialCertified.moleculeGraph.atomZ (SA n) ≤ 6 := by
  have mem' : n.val = 2 ∨ n.val = 7 ∨ n.val = 8 ∨ n.val = 0 := by
    simpa [List.mem_cons, List.mem_nil_iff, or_false] using mem
  rcases mem' with h | h | h | h
  · have : n = ⟨2, by decide⟩ := Fin.ext h
    rw [this, z_arm]
  · have : n = ⟨7, by decide⟩ := Fin.ext h
    rw [this, z_terminal ⟨7, by decide⟩ (by decide) (by decide)]
    decide
  · have : n = ⟨8, by decide⟩ := Fin.ext h
    rw [this, z_terminal ⟨8, by decide⟩ (by decide) (by decide)]
    decide
  · exact absurd h neZero

private theorem constitutional_gt_of_atomic (left right : Fin 4)
    (leftIndex rightIndex : Fin 9) (leftZ rightZ : ℕ)
    (leftEq : spatialRootFrames.actualLigandAtoms left = SA leftIndex)
    (rightEq : spatialRootFrames.actualLigandAtoms right = SA rightIndex)
    (leftAtomic : cyclicSpatialCertified.moleculeGraph.atomZ (SA leftIndex) = leftZ)
    (rightAtomic : cyclicSpatialCertified.moleculeGraph.atomZ (SA rightIndex) = rightZ)
    (higher : rightZ < leftZ) :
    OfficialRuleMajorKey.compare (spatialRootFrames.stages left).a.key.constitutional
      (spatialRootFrames.stages right).a.key.constitutional = Ordering.gt := by
  apply compare_gt_of_heads
  · have head := slot_head left
    rw [leftEq, leftAtomic] at head
    exact head
  · have head := slot_head right
    rw [rightEq, rightAtomic] at head
    exact head
  · exact higher

private theorem constitutional_carbons (slotCarbonTwo slotCarbonFour : Fin 4)
    (twoEq : spatialRootFrames.actualLigandAtoms slotCarbonTwo = SA ⟨2, by decide⟩)
    (fourEq : spatialRootFrames.actualLigandAtoms slotCarbonFour = SA ⟨4, by decide⟩) :
    OfficialRuleMajorKey.compare
      (spatialRootFrames.stages slotCarbonTwo).a.key.constitutional
      (spatialRootFrames.stages slotCarbonFour).a.key.constitutional = Ordering.gt := by
  have secondTwo := carbon_second slotCarbonTwo ⟨2, by decide⟩ ⟨3, by decide⟩
    [0, 6, 3, 4] twoEq arm_neighbor_iff (by simp) (by decide) 17 z_chlorine arm_child_le
  have secondFour := carbon_second slotCarbonFour ⟨4, by decide⟩ ⟨2, by decide⟩
    [2, 7, 8, 0] fourEq closing_neighbor_iff (by simp) (by decide) 6 z_arm closing_child_le
  apply rule1a_gt_of_second_sphere
  · have head := slot_head slotCarbonTwo
    rw [twoEq, z_arm] at head
    exact sphere_of_head head
  · have head := slot_head slotCarbonFour
    rw [fourEq, z_closing] at head
    exact sphere_of_head head
  · exact secondTwo
  · exact secondFour
  · decide

private theorem compound_gt_of_constitutional (left right : Fin 4)
    (constGt : OfficialRuleMajorKey.compare
      (spatialRootFrames.stages left).a.key.constitutional
      (spatialRootFrames.stages right).a.key.constitutional = Ordering.gt) :
    cyclicSpatialCertified.compareLocalizedRerootCompoundRule4bcKeys
      (spatialRootFrames.compounds left).prior (spatialRootFrames.compounds right).prior =
      Ordering.gt := by
  have cumulative : cyclicSpatialCertified.compareLocalizedRerootCumulativeRule45Keys
      (spatialRootFrames.compounds left).prior.rule4aKey
      (spatialRootFrames.compounds right).prior.rule4aKey = Ordering.gt := by
    rw [stage_rule4a left, stage_rule4a right,
      cyclicSpatialCertified.compareLocalizedRerootCumulativeRule45Keys_eq_of_constitutional_decisive
        _ _ (by rw [constGt]; decide)]
    exact constGt
  rw [cyclicSpatialCertified.compareLocalizedRerootCompoundRule4bcKeys_eq_rule4a_of_ne
    _ _ (by rw [cumulative]; decide), cumulative]

private theorem prior_gt_of_constitutional (left right : Fin 4)
    (constGt : OfficialRuleMajorKey.compare
      (spatialRootFrames.stages left).a.key.constitutional
      (spatialRootFrames.stages right).a.key.constitutional = Ordering.gt) :
    compare (ofLex (spatialRootFrames.retainedKeys left)).1
      (ofLex (spatialRootFrames.retainedKeys right)).1 = Ordering.gt := by
  rw [← spatialRootFrames.retainedActual_priorComparison spatial_simpleBonded left right]
  exact compound_gt_of_constitutional left right constGt

private theorem retained_gt_of_constitutional (left right : Fin 4)
    (constGt : OfficialRuleMajorKey.compare
      (spatialRootFrames.stages left).a.key.constitutional
      (spatialRootFrames.stages right).a.key.constitutional = Ordering.gt) :
    compare (spatialRootFrames.retainedKeys left) (spatialRootFrames.retainedKeys right) =
      Ordering.gt := by
  have compoundGt := compound_gt_of_constitutional left right constGt
  have rule45 : cyclicSpatialCertified.compareLocalizedRerootCompoundRule45Keys
      (spatialRootFrames.compounds left) (spatialRootFrames.compounds right) = Ordering.gt := by
    unfold CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundRule45Keys compareLex
      Ordering.byKey
    rw [compoundGt]
    rfl
  have through := cyclicSpatialCertified.compareLocalizedRerootCompoundThroughRule5_ordering
    (spatialRootFrames.compounds left) (spatialRootFrames.compounds right)
  rw [rule45] at through
  rw [← spatialRootFrames.retainedActual_fullOrdering spatial_simpleBonded left right]
  exact through

private noncomputable def slotFluorine : Fin 4 :=
  Classical.choose (slot_of_atom ⟨1, by decide⟩
    ((root_neighbor_iff ⟨1, by decide⟩).mpr (by simp)))

private theorem slotFluorine_atom :
    spatialRootFrames.actualLigandAtoms slotFluorine = SA ⟨1, by decide⟩ :=
  Classical.choose_spec (slot_of_atom ⟨1, by decide⟩
    ((root_neighbor_iff ⟨1, by decide⟩).mpr (by simp)))

private noncomputable def slotCarbonTwo : Fin 4 :=
  Classical.choose (slot_of_atom ⟨2, by decide⟩
    ((root_neighbor_iff ⟨2, by decide⟩).mpr (by simp)))

private theorem slotCarbonTwo_atom :
    spatialRootFrames.actualLigandAtoms slotCarbonTwo = SA ⟨2, by decide⟩ :=
  Classical.choose_spec (slot_of_atom ⟨2, by decide⟩
    ((root_neighbor_iff ⟨2, by decide⟩).mpr (by simp)))

private noncomputable def slotCarbonFour : Fin 4 :=
  Classical.choose (slot_of_atom ⟨4, by decide⟩
    ((root_neighbor_iff ⟨4, by decide⟩).mpr (by simp)))

private theorem slotCarbonFour_atom :
    spatialRootFrames.actualLigandAtoms slotCarbonFour = SA ⟨4, by decide⟩ :=
  Classical.choose_spec (slot_of_atom ⟨4, by decide⟩
    ((root_neighbor_iff ⟨4, by decide⟩).mpr (by simp)))

private noncomputable def slotHydrogen : Fin 4 :=
  Classical.choose (slot_of_atom ⟨5, by decide⟩
    ((root_neighbor_iff ⟨5, by decide⟩).mpr (by simp)))

private theorem slotHydrogen_atom :
    spatialRootFrames.actualLigandAtoms slotHydrogen = SA ⟨5, by decide⟩ :=
  Classical.choose_spec (slot_of_atom ⟨5, by decide⟩
    ((root_neighbor_iff ⟨5, by decide⟩).mpr (by simp)))

private theorem slots_distinct (left right : Fin 4) (leftIndex rightIndex : Fin 9)
    (leftEq : spatialRootFrames.actualLigandAtoms left = SA leftIndex)
    (rightEq : spatialRootFrames.actualLigandAtoms right = SA rightIndex)
    (different : leftIndex ≠ rightIndex) : left ≠ right := by
  intro same
  apply different
  apply Fin.ext
  have atoms : SA leftIndex = SA rightIndex := by
    rw [← leftEq, ← rightEq, same]
  simpa [SA_val] using congrArg Fin.val atoms

private theorem index_ne_12 : (⟨1, by decide⟩ : Fin 9) ≠ ⟨2, by decide⟩ := by decide
private theorem index_ne_14 : (⟨1, by decide⟩ : Fin 9) ≠ ⟨4, by decide⟩ := by decide
private theorem index_ne_15 : (⟨1, by decide⟩ : Fin 9) ≠ ⟨5, by decide⟩ := by decide
private theorem index_ne_24 : (⟨2, by decide⟩ : Fin 9) ≠ ⟨4, by decide⟩ := by decide
private theorem index_ne_25 : (⟨2, by decide⟩ : Fin 9) ≠ ⟨5, by decide⟩ := by decide
private theorem index_ne_45 : (⟨4, by decide⟩ : Fin 9) ≠ ⟨5, by decide⟩ := by decide

private abbrev priorityOrder : List (Fin 4) :=
  [slotFluorine, slotCarbonTwo, slotCarbonFour, slotHydrogen]

private theorem priorityOrder_nodup : priorityOrder.Nodup := by
  rw [priorityOrder]
  refine List.Nodup.cons ?_ (List.Nodup.cons ?_ (List.Nodup.cons ?_
    (List.Nodup.cons ?_ List.nodup_nil)))
  · intro member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with h | h | h
    · exact slots_distinct slotFluorine slotCarbonTwo _ _ slotFluorine_atom slotCarbonTwo_atom
        index_ne_12 h
    · exact slots_distinct slotFluorine slotCarbonFour _ _ slotFluorine_atom slotCarbonFour_atom
        index_ne_14 h
    · exact slots_distinct slotFluorine slotHydrogen _ _ slotFluorine_atom slotHydrogen_atom
        index_ne_15 h
  · intro member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with h | h
    · exact slots_distinct slotCarbonTwo slotCarbonFour _ _ slotCarbonTwo_atom slotCarbonFour_atom
        index_ne_24 h
    · exact slots_distinct slotCarbonTwo slotHydrogen _ _ slotCarbonTwo_atom slotHydrogen_atom
        index_ne_25 h
  · intro member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    exact slots_distinct slotCarbonFour slotHydrogen _ _ slotCarbonFour_atom slotHydrogen_atom
      index_ne_45 member
  · simp

private theorem priorityOrder_perm : priorityOrder.Perm (List.finRange 4) := by
  apply List.perm_of_nodup_nodup_toFinset_eq priorityOrder_nodup (List.nodup_finRange 4)
  apply Finset.eq_univ_of_card
  rw [List.toFinset_card_of_nodup priorityOrder_nodup]
  simp [Fintype.card_fin, priorityOrder]

private theorem const_fluorine_carbonTwo :
    OfficialRuleMajorKey.compare (spatialRootFrames.stages slotFluorine).a.key.constitutional
      (spatialRootFrames.stages slotCarbonTwo).a.key.constitutional = Ordering.gt :=
  constitutional_gt_of_atomic slotFluorine slotCarbonTwo ⟨1, by decide⟩ ⟨2, by decide⟩ 9 6
    slotFluorine_atom slotCarbonTwo_atom z_fluorine z_arm (by decide)

private theorem const_fluorine_carbonFour :
    OfficialRuleMajorKey.compare (spatialRootFrames.stages slotFluorine).a.key.constitutional
      (spatialRootFrames.stages slotCarbonFour).a.key.constitutional = Ordering.gt :=
  constitutional_gt_of_atomic slotFluorine slotCarbonFour ⟨1, by decide⟩ ⟨4, by decide⟩ 9 6
    slotFluorine_atom slotCarbonFour_atom z_fluorine z_closing (by decide)

private theorem const_fluorine_hydrogen :
    OfficialRuleMajorKey.compare (spatialRootFrames.stages slotFluorine).a.key.constitutional
      (spatialRootFrames.stages slotHydrogen).a.key.constitutional = Ordering.gt :=
  constitutional_gt_of_atomic slotFluorine slotHydrogen ⟨1, by decide⟩ ⟨5, by decide⟩ 9 1
    slotFluorine_atom slotHydrogen_atom z_fluorine z_hydrogenFive (by decide)

private theorem const_carbonTwo_carbonFour :
    OfficialRuleMajorKey.compare (spatialRootFrames.stages slotCarbonTwo).a.key.constitutional
      (spatialRootFrames.stages slotCarbonFour).a.key.constitutional = Ordering.gt :=
  constitutional_carbons slotCarbonTwo slotCarbonFour slotCarbonTwo_atom slotCarbonFour_atom

private theorem const_carbonTwo_hydrogen :
    OfficialRuleMajorKey.compare (spatialRootFrames.stages slotCarbonTwo).a.key.constitutional
      (spatialRootFrames.stages slotHydrogen).a.key.constitutional = Ordering.gt :=
  constitutional_gt_of_atomic slotCarbonTwo slotHydrogen ⟨2, by decide⟩ ⟨5, by decide⟩ 6 1
    slotCarbonTwo_atom slotHydrogen_atom z_arm z_hydrogenFive (by decide)

private theorem const_carbonFour_hydrogen :
    OfficialRuleMajorKey.compare (spatialRootFrames.stages slotCarbonFour).a.key.constitutional
      (spatialRootFrames.stages slotHydrogen).a.key.constitutional = Ordering.gt :=
  constitutional_gt_of_atomic slotCarbonFour slotHydrogen ⟨4, by decide⟩ ⟨5, by decide⟩ 6 1
    slotCarbonFour_atom slotHydrogen_atom z_closing z_hydrogenFive (by decide)

private theorem key_lt_of_gt (left right : Fin 4)
    (compared : compare (spatialRootFrames.retainedKeys left)
      (spatialRootFrames.retainedKeys right) = Ordering.gt) :
    spatialRootFrames.retainedKeys right < spatialRootFrames.retainedKeys left :=
  (completeLigandRule5Key_compare_gt_iff _ _).mp compared

private theorem priorityOrder_pairwise :
    priorityOrder.Pairwise (fun left right =>
      spatialRootFrames.retainedKeys right < spatialRootFrames.retainedKeys left) := by
  apply List.Pairwise.cons
  · intro later member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact key_lt_of_gt slotFluorine slotCarbonTwo
        (retained_gt_of_constitutional _ _ const_fluorine_carbonTwo)
    · exact key_lt_of_gt slotFluorine slotCarbonFour
        (retained_gt_of_constitutional _ _ const_fluorine_carbonFour)
    · exact key_lt_of_gt slotFluorine slotHydrogen
        (retained_gt_of_constitutional _ _ const_fluorine_hydrogen)
  apply List.Pairwise.cons
  · intro later member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl
    · exact key_lt_of_gt slotCarbonTwo slotCarbonFour
        (retained_gt_of_constitutional _ _ const_carbonTwo_carbonFour)
    · exact key_lt_of_gt slotCarbonTwo slotHydrogen
        (retained_gt_of_constitutional _ _ const_carbonTwo_hydrogen)
  apply List.Pairwise.cons
  · intro later member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    subst member
    exact key_lt_of_gt slotCarbonFour slotHydrogen
        (retained_gt_of_constitutional _ _ const_carbonFour_hydrogen)
  apply List.Pairwise.cons
  · intro later member
    simp only [List.mem_nil_iff] at member
  exact List.Pairwise.nil

private theorem prior_ne_of_gt (left right : Fin 4)
    (compared : compare (ofLex (spatialRootFrames.retainedKeys left)).1
      (ofLex (spatialRootFrames.retainedKeys right)).1 = Ordering.gt) :
    (ofLex (spatialRootFrames.retainedKeys left)).1 ≠
      (ofLex (spatialRootFrames.retainedKeys right)).1 := by
  intro equal
  have comparedEq := (completeLigandPriorKey_compare_eq_iff _ _).mpr equal
  rw [compared] at comparedEq
  cases comparedEq

private theorem order_member (index : Fin 4) : index ∈ priorityOrder :=
  priorityOrder_perm.mem_iff.mpr (List.mem_finRange index)

private theorem ranked_prior_ne (left right : Fin 4) (different : left ≠ right) :
    (ofLex (spatialRootFrames.retainedKeys left)).1 ≠
      (ofLex (spatialRootFrames.retainedKeys right)).1 := by
  have leftMember := order_member left
  have rightMember := order_member right
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at leftMember rightMember
  rcases leftMember with rfl | rfl | rfl | rfl <;>
    rcases rightMember with rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl different
        | exact prior_ne_of_gt _ _
            (prior_gt_of_constitutional _ _ const_fluorine_carbonTwo)
        | exact Ne.symm (prior_ne_of_gt _ _
            (prior_gt_of_constitutional _ _ const_fluorine_carbonTwo))
        | exact prior_ne_of_gt _ _
            (prior_gt_of_constitutional _ _ const_fluorine_carbonFour)
        | exact Ne.symm (prior_ne_of_gt _ _
            (prior_gt_of_constitutional _ _ const_fluorine_carbonFour))
        | exact prior_ne_of_gt _ _
            (prior_gt_of_constitutional _ _ const_fluorine_hydrogen)
        | exact Ne.symm (prior_ne_of_gt _ _
            (prior_gt_of_constitutional _ _ const_fluorine_hydrogen))
        | exact prior_ne_of_gt _ _
            (prior_gt_of_constitutional _ _ const_carbonTwo_carbonFour)
        | exact Ne.symm (prior_ne_of_gt _ _
            (prior_gt_of_constitutional _ _ const_carbonTwo_carbonFour))
        | exact prior_ne_of_gt _ _
            (prior_gt_of_constitutional _ _ const_carbonTwo_hydrogen)
        | exact Ne.symm (prior_ne_of_gt _ _
            (prior_gt_of_constitutional _ _ const_carbonTwo_hydrogen))
        | exact prior_ne_of_gt _ _
            (prior_gt_of_constitutional _ _ const_carbonFour_hydrogen)
        | exact Ne.symm (prior_ne_of_gt _ _
            (prior_gt_of_constitutional _ _ const_carbonFour_hydrogen))

private theorem pairCount_zero :
    completeRule5PairCount spatialRootFrames.retainedKeys = 0 := by
  unfold completeRule5PairCount sourceEnantiomorphicPairCount
  have absent : ∀ i j : Fin 4, i ≠ j →
      ¬ CompletePriorPair spatialRootFrames.retainedKeys i j := by
    intro i j different pair
    exact ranked_prior_ne i j different pair.2
  rw [if_neg (absent 0 1 (by decide)), if_neg (absent 0 2 (by decide)),
    if_neg (absent 1 2 (by decide)), if_neg (absent 0 3 (by decide)),
    if_neg (absent 1 3 (by decide)), if_neg (absent 2 3 (by decide))]

private theorem ligand_coordinate (index : Fin 9) (point : CartesianPoint3) (slot : Fin 4)
    (atomEq : spatialRootFrames.actualLigandAtoms slot = SA index)
    (lookup : cyclicSpatialCertified.spatialPointAt? (SA index) = some point) :
    spatialRootFrames.actualCoordinates slot = some point := by
  rw [ContextFrameCompilation.actualCoordinates, atomEq]
  exact lookup

private theorem coordinates_exist (slot : Fin 4) :
    ∃ point : CartesianPoint3, spatialRootFrames.actualCoordinates slot = some point := by
  have member := slot_mem slot
  have member' : (indexOf (spatialRootFrames.actualLigandAtoms slot)).val = 5 ∨
      (indexOf (spatialRootFrames.actualLigandAtoms slot)).val = 1 ∨
      (indexOf (spatialRootFrames.actualLigandAtoms slot)).val = 2 ∨
      (indexOf (spatialRootFrames.actualLigandAtoms slot)).val = 4 := by
    simpa [List.mem_cons, List.mem_nil_iff, or_false] using member
  rcases member' with h | h | h | h
  · have indexEq : indexOf (spatialRootFrames.actualLigandAtoms slot) = ⟨5, by decide⟩ := Fin.ext h
    have atomEq : spatialRootFrames.actualLigandAtoms slot = SA ⟨5, by decide⟩ := by
      rw [indexOf_eq (spatialRootFrames.actualLigandAtoms slot), indexEq]
    exact ⟨P5, ligand_coordinate _ P5 slot atomEq root_written_ligand_coordinates.1⟩
  · have indexEq : indexOf (spatialRootFrames.actualLigandAtoms slot) = ⟨1, by decide⟩ := Fin.ext h
    have atomEq : spatialRootFrames.actualLigandAtoms slot = SA ⟨1, by decide⟩ := by
      rw [indexOf_eq (spatialRootFrames.actualLigandAtoms slot), indexEq]
    exact ⟨P1, ligand_coordinate _ P1 slot atomEq root_written_ligand_coordinates.2.1⟩
  · have indexEq : indexOf (spatialRootFrames.actualLigandAtoms slot) = ⟨2, by decide⟩ := Fin.ext h
    have atomEq : spatialRootFrames.actualLigandAtoms slot = SA ⟨2, by decide⟩ := by
      rw [indexOf_eq (spatialRootFrames.actualLigandAtoms slot), indexEq]
    exact ⟨P2, ligand_coordinate _ P2 slot atomEq root_written_ligand_coordinates.2.2.1⟩
  · have indexEq : indexOf (spatialRootFrames.actualLigandAtoms slot) = ⟨4, by decide⟩ := Fin.ext h
    have atomEq : spatialRootFrames.actualLigandAtoms slot = SA ⟨4, by decide⟩ := by
      rw [indexOf_eq (spatialRootFrames.actualLigandAtoms slot), indexEq]
    exact ⟨P4, ligand_coordinate _ P4 slot atomEq root_written_ligand_coordinates.2.2.2⟩

private noncomputable def priorityPoint (slot : Fin 4) : CartesianPoint3 :=
  Classical.choose (coordinates_exist slot)

private theorem priorityPoint_eq (slot : Fin 4) :
    spatialRootFrames.actualCoordinates slot = some (priorityPoint slot) :=
  Classical.choose_spec (coordinates_exist slot)

private theorem priorityPoint_unique (slot : Fin 4) (point : CartesianPoint3)
    (coord : spatialRootFrames.actualCoordinates slot = some point) :
    priorityPoint slot = point :=
  Option.some.inj ((priorityPoint_eq slot).symm.trans coord)

private theorem fluorine_coord :
    spatialRootFrames.actualCoordinates slotFluorine = some P1 :=
  ligand_coordinate ⟨1, by decide⟩ P1 slotFluorine slotFluorine_atom
    root_written_ligand_coordinates.2.1

private theorem carbonTwo_coord :
    spatialRootFrames.actualCoordinates slotCarbonTwo = some P2 :=
  ligand_coordinate ⟨2, by decide⟩ P2 slotCarbonTwo slotCarbonTwo_atom
    root_written_ligand_coordinates.2.2.1

private theorem carbonFour_coord :
    spatialRootFrames.actualCoordinates slotCarbonFour = some P4 :=
  ligand_coordinate ⟨4, by decide⟩ P4 slotCarbonFour slotCarbonFour_atom
    root_written_ligand_coordinates.2.2.2

private theorem hydrogen_coord :
    spatialRootFrames.actualCoordinates slotHydrogen = some P5 :=
  ligand_coordinate ⟨5, by decide⟩ P5 slotHydrogen slotHydrogen_atom
    root_written_ligand_coordinates.1

private theorem priority_points :
    priorityOrder.map priorityPoint = [P1, P2, P4, P5] := by
  simp [priorityOrder, priorityPoint_unique slotFluorine P1 fluorine_coord,
    priorityPoint_unique slotCarbonTwo P2 carbonTwo_coord,
    priorityPoint_unique slotCarbonFour P4 carbonFour_coord,
    priorityPoint_unique slotHydrogen P5 hydrogen_coord]

private theorem spatial_judgment :
    RetainedContextualDescriptorJudgmentAt cyclicSpatialReference.certified.moleculeGraph
      (descriptorMap cyclicSpatialReference)
      (finalCenterUnit cyclicSpatialReference spatialRootCenter)
      spatialRootFrames.actualArmGraphs spatialRootFrames.W spatialRootFrames.D
      spatialRootFrames.actualCoordinates (.chiral RS.R) := by
  refine ⟨priorityPoint, priorityPoint_eq, ?_⟩
  refine ⟨priorityOrder, RS.R, priorityOrder_perm, priorityOrder_pairwise, ?_, ?_⟩
  · refine ⟨P1, P2, P4, P5, priority_points, ?_⟩
    rw [priority_volume]
    decide
  · have countZero : completeRule5PairCount
        (retainedContextualFrameKeysAt cyclicSpatialReference.certified.moleculeGraph
          (descriptorMap cyclicSpatialReference)
          (finalCenterUnit cyclicSpatialReference spatialRootCenter)
          spatialRootFrames.actualArmGraphs spatialRootFrames.W spatialRootFrames.D) = 0 :=
      pairCount_zero
    unfold classifyTetrahedralRSPseudo
    rw [countZero]
    rfl

/-- At fuel 10 the spatial root's own reference state is chiral `R`.

The retained order is fluorine, the chlorine-bearing carbon, the hydrogen-bearing carbon,
then the root hydrogen. Rule 1a sphere 2 supplies the carbon separation. No prior components
tie, so the pair count is 0, and the ordered points `P1, P2, P4, P5` have oriented volume `-24`. -/
theorem spatialRoot_chiral_R :
    referenceState cyclicSpatialReference spatialRootTarget = some (.chiral RS.R) ∧
      completeRule5PairCount spatialRootFrames.retainedKeys = 0 ∧
      CartesianPoint3.orientedVolume P1 P2 P4 P5 = -24 ∧
      ∃ slotFluorine slotCarbonTwo slotCarbonFour slotHydrogen : Fin 4,
        spatialRootFrames.actualLigandAtoms slotFluorine = SA ⟨1, by decide⟩ ∧
        spatialRootFrames.actualLigandAtoms slotCarbonTwo = SA ⟨2, by decide⟩ ∧
        spatialRootFrames.actualLigandAtoms slotCarbonFour = SA ⟨4, by decide⟩ ∧
        spatialRootFrames.actualLigandAtoms slotHydrogen = SA ⟨5, by decide⟩ ∧
        ([slotFluorine, slotCarbonTwo, slotCarbonFour, slotHydrogen] : List (Fin 4)).Perm
          (List.finRange 4) ∧
        ([slotFluorine, slotCarbonTwo, slotCarbonFour, slotHydrogen] : List (Fin 4)).Pairwise
          (fun left right => spatialRootFrames.retainedKeys right <
            spatialRootFrames.retainedKeys left) ∧
        spatialRootFrames.actualCoordinates slotFluorine = some P1 ∧
        spatialRootFrames.actualCoordinates slotCarbonTwo = some P2 ∧
        spatialRootFrames.actualCoordinates slotCarbonFour = some P4 ∧
        spatialRootFrames.actualCoordinates slotHydrogen = some P5 := by
  refine ⟨(spatialRoot_referenceState_eq_some_iff (.chiral RS.R)).mpr spatial_judgment,
    pairCount_zero, priority_volume, slotFluorine, slotCarbonTwo, slotCarbonFour, slotHydrogen,
    slotFluorine_atom, slotCarbonTwo_atom, slotCarbonFour_atom, slotHydrogen_atom,
    priorityOrder_perm, priorityOrder_pairwise, fluorine_coord, carbonTwo_coord, carbonFour_coord,
    hydrogen_coord⟩

/-- The same root letter is the canonical-cut judgment of the assembled ring endpoint. -/
theorem spatialRoot_canonicalCutJudgment :
    RetainedContextualDescriptorJudgmentAt cyclicSpatialReference.certified.moleculeGraph
      (descriptorMap cyclicSpatialReference)
      (finalCenterUnit cyclicSpatialReference spatialRootCenter)
      (spatialRootFrames.canonicalCutGraphs spatial_simpleBonded)
      spatialRootFrames.W spatialRootFrames.D
      spatialRootFrames.actualCoordinates (.chiral RS.R) :=
  (spatialRootFrames.referenceState_some_iff_canonicalCutJudgment spatial_simpleBonded
    (.chiral RS.R)).mp spatialRoot_chiral_R.1

end

end TetraStereo.OneCenter.LocalizedCyclicSpatialRootLetter

assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialRootLetter.spatialRoot_chiral_R
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialRootLetter.spatialRoot_canonicalCutJudgment
