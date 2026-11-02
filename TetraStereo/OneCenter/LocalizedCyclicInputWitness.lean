import TetraStereo.OneCenter.LocalizedRuleMajorReferencePipeline
import TetraStereo.UniversalProof.NextFrontier.NativeRingRuntimeRoot
import TetraStereo.UniversalProof.NextFrontier.NativeRingParserPublic
import TetraStereo.UniversalProof.NextFrontier.NativeRingRuntimeGraphFacts
import TetraStereo.UniversalProof.NextFrontier.NativeRingPhysicalStructure
import TetraStereo.OneCenter.LocalizedOccurrenceCarrierCoverage
import TetraStereo.OneCenter.LocalizedMonocyclicDoubleBondPerception
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-!
# Certified cyclic single-bond input for localized major-reference nonvacuity

This module exhibits one finite production input, `NativeRingDomain.ringRaw 0` expanded
anticlockwise to nine atoms, inside the actual `LocalizedRuleMajorReference.Input` carrier.
The triangle on semantic atoms `0`, `2`, and `4` is a detected degree-four simple cycle, and
the official occurrence carrier contains real occurrences of all three centers plus a
`ringDuplicate` of atom `0`.

Atoms `2` and `4` are non-root detected centers of this fixture.  No descriptor value and no
whole reference state is computed.
-/

namespace TetraStereo.OneCenter.LocalizedCyclicInputWitness

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.OneCenter.SemanticMolecule
open TetraStereo.OneCenter.SemanticInteraction
open TetraStereo.OneCenter.MoleculeGraph
open TetraStereo.UniversalProof.NativeRingDomain
open TetraStereo.UniversalProof.NativeRingHydrogenFacts
open TetraStereo.UniversalProof.NativeRingParserPublic
open TetraStereo.UniversalProof.NativeRingRuntimeRoot
open TetraStereo.UniversalProof.NativeRingRuntimeGraphFacts
open TetraStereo.UniversalProof.GeneralRingPhysicalAdmission
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery

/-- Explicit-hydrogen expansion of the nine-atom anticlockwise ring fixture. -/
abbrev cyclicExpanded : RawMolecule :=
  expanded 0 TetrahedralInputParity.anticlockwise

/-- Parser-to-source conversion of the expanded ring.  This is the same `getD` converter as
`ownSource`; the source module that names `ringSource` is not imported because its current
import closure rebuilds an unrelated stale module. -/
def cyclicSource : AuthoritativeChemicalInput :=
  cyclicExpanded.toAuthoritativeChemicalInput?.getD
    { molecule := { atoms := [], interactions := [] } }

private theorem expanded_known_elements :
    ∀ spec ∈ cyclicExpanded.atoms, spec.element ≠ .wildcard := by
  intro spec member unknown
  obtain ⟨_mass, known⟩ :=
    expanded_rule2_masses 0 TetrahedralInputParity.anticlockwise spec member
  simp [rule2MassPico?, unknown] at known

theorem source_conversion :
    cyclicExpanded.toAuthoritativeChemicalInput? = some cyclicSource := by
  have present :=
    (RawMolecule.toAuthoritativeChemicalInput?_isSome cyclicExpanded).mpr
      expanded_known_elements
  cases converted : cyclicExpanded.toAuthoritativeChemicalInput? with
  | none => simp [converted] at present
  | some source => simp [cyclicSource, converted]

theorem heavyAtomCount :
    (ringRaw 0 TetrahedralInputParity.anticlockwise).atomCount = 5 :=
  atom_count 0 TetrahedralInputParity.anticlockwise

theorem rawBondsSingle (bond : RawBond)
    (member : bond ∈ (ringRaw 0 TetrahedralInputParity.anticlockwise).bonds) :
    bond.kind = ParsedBondKind.single := by
  rw [ringRaw_bonds] at member
  exact ringBonds_kind_single 0 bond member

theorem parsedRing :
    parseOpenSMILES (ringSyntax 0 TetrahedralInputParity.anticlockwise) =
      .ok (ringRaw 0 TetrahedralInputParity.anticlockwise) :=
  parse_ring 0 TetrahedralInputParity.anticlockwise

theorem certifiedRingFamily :
    parseAndNormalizeOpenSMILESCertified
        (ringSyntax 0 TetrahedralInputParity.anticlockwise) =
      .ok (ringRawCertified 0 TetrahedralInputParity.anticlockwise) :=
  certified_ring 0 TetrahedralInputParity.anticlockwise

theorem runtimeRootLigands :
    cyclicExpanded.ligandsWithLonePair 0 = [5, 1, 2, 4] :=
  actual_root_ligands 0 TetrahedralInputParity.anticlockwise

theorem runtimeRootWidth :
    (physicalRoots 0 TetrahedralInputParity.anticlockwise).length = 4 :=
  physical_roots_length 0 TetrahedralInputParity.anticlockwise

theorem source_structurallyWellFormed : cyclicSource.StructurallyWellFormed :=
  (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff cyclicSource).mp
    (by decide +kernel)

theorem source_graphReady : cyclicSource.molecule.LocalizedCIPGraphReady :=
  (SemanticMolecule.localizedCIPGraphReady?_eq_true_iff cyclicSource.molecule).mp
    (by decide +kernel)

/-- Certified localized input built from the production ring source. -/
def cyclicCertified : CertifiedLocalizedCIPInput where
  certified :=
    { input := cyclicSource
      structurallyWellFormed := source_structurallyWellFormed }
  graphReady := source_graphReady

/-- The same certified input viewed as a major-reference pipeline input. -/
def cyclicReferenceInput : LocalizedRuleMajorReference.Input where
  certified := cyclicCertified

private theorem converted :
    cyclicExpanded.toSemanticMolecule? = some cyclicSource.molecule :=
  cyclicExpanded.toAuthoritativeChemicalInput?_molecule cyclicSource source_conversion

theorem atomCount_eq :
    cyclicCertified.certified.input.molecule.atomCount = 9 := by
  have count :=
    cyclicExpanded.toSemanticMolecule?_atomCount cyclicSource.molecule converted
  have expandedCount : cyclicExpanded.atomCount = 9 := by
    have raw := expanded_atom_count 0 TetrahedralInputParity.anticlockwise
    have arith : 3 * 0 + 9 = 9 := by decide
    rwa [arith] at raw
  rwa [expandedCount] at count

/-- Transport a literal index below nine into the certified atom type. -/
def atom (index : Fin 9) : cyclicCertified.Atom :=
  Fin.cast atomCount_eq.symm index

@[simp] theorem atom_val (index : Fin 9) : (atom index).val = index.val := rfl

def A0 : cyclicCertified.Atom := atom ⟨0, by decide⟩
def A2 : cyclicCertified.Atom := atom ⟨2, by decide⟩
def A4 : cyclicCertified.Atom := atom ⟨4, by decide⟩

private theorem cyclicExpandedWell : cyclicExpanded.WellFormed :=
  (expanded_stereochemical_admissible 0 TetrahedralInputParity.anticlockwise).1.1

private theorem cyclicExpandedUnique : cyclicExpanded.BondRecordsUnique :=
  (expanded_stereochemical_admissible 0 TetrahedralInputParity.anticlockwise).1.2

private theorem covalentRecord_of_single (bond : RawBond)
    (member : bond ∈ cyclicExpanded.bonds) :
    bond.toSemanticInteraction.localizedCovalentRecord? = some (bond.edgeKey, 1) := by
  rw [localizedCovalentRecord?_toSemanticInteraction]
  have single := expanded_bonds_single 0 TetrahedralInputParity.anticlockwise bond member
  simp [single, ParsedBondKind.localizedBondOrder?]

/-- Unordered raw incidence is equality of the semantic endpoint key. -/
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
  rw [cyclicExpanded.toSemanticMolecule?_interactions cyclicSource.molecule converted,
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
    rw [cyclicExpanded.toSemanticMolecule?_interactions cyclicSource.molecule converted,
      List.mem_map] at interactionMember
    obtain ⟨bond, bondMember, bondEq⟩ := interactionMember
    have recorded := covalentRecord_of_single bond bondMember
    rw [← bondEq] at observed
    have pair := Option.some.inj (recorded.symm.trans observed)
    exact ⟨bond, bondMember,
      (connects_semantic bond left right).mpr (Prod.mk.inj pair).1⟩
  · rintro ⟨bond, bondMember, connects⟩
    rw [SemanticMolecule.localizedCovalentRecords,
      cyclicExpanded.toSemanticMolecule?_interactions cyclicSource.molecule converted,
      List.mem_filterMap]
    refine ⟨bond.toSemanticInteraction, List.mem_map.mpr ⟨bond, bondMember, rfl⟩, ?_⟩
    rw [covalentRecord_of_single bond bondMember]
    rw [show bond.edgeKey = semanticEdgeKey bond.source bond.target from rfl]
    rw [(connects_semantic bond left right).mp connects]

private theorem neighbor_mem_iff (center neighbor : cyclicCertified.Atom) :
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

theorem input_simpleBonded :
    cyclicReferenceInput.certified.moleculeGraph.SimpleBonded := by
  intro center neighbor adjacent
  have distinct : center ≠ neighbor := by
    intro equal
    subst neighbor
    simp [MoleculeGraph.Adj,
      cyclicReferenceInput.certified.moleculeGraph.bond_self center] at adjacent
  rcases (cyclicSource.molecule.toLocalizedMoleculeGraph_adj_iff_record
      cyclicCertified.graphReady center neighbor distinct).mp adjacent with
    ⟨order, present, _⟩
  have bondOne := cyclicSource.molecule.toLocalizedMoleculeGraph_bond_eq_of_record
    center neighbor order cyclicCertified.graphReady distinct present
  rw [record_order_one present] at bondOne
  simpa [cyclicReferenceInput, CertifiedLocalizedCIPInput.moleculeGraph] using bondOne

private theorem recordIndex_lt (center : cyclicCertified.Atom) (index : ℕ)
    (member : index ∈ (recordNeighbors cyclicExpanded center.val).toFinset) :
    index < cyclicCertified.certified.input.molecule.atomCount := by
  have rawMember : index ∈ recordNeighbors cyclicExpanded center.val :=
    List.mem_toFinset.mp member
  have rawBound := (recordNeighbor_bounds cyclicExpandedWell rawMember).1
  rw [expanded_atom_count 0 TetrahedralInputParity.anticlockwise] at rawBound
  rw [atomCount_eq]
  exact Nat.lt_of_lt_of_eq rawBound (by decide : 3 * 0 + 9 = 9)

private theorem neighborFinset_eq_records (center : cyclicCertified.Atom) :
    cyclicCertified.moleculeGraph.neighborFinset center =
      ((recordNeighbors cyclicExpanded center.val).toFinset.attachFin
        (recordIndex_lt center)) := by
  ext neighbor
  rw [MoleculeGraph.mem_neighborFinset, neighbor_mem_iff, Finset.mem_attachFin,
    List.mem_toFinset]

private theorem neighborCard_eq_recordLength (center : cyclicCertified.Atom) :
    (cyclicCertified.moleculeGraph.neighborFinset center).card =
      (recordNeighbors cyclicExpanded center.val).length := by
  rw [neighborFinset_eq_records, Finset.card_attachFin,
    List.toFinset_card_of_nodup (recordNeighbors_nodup cyclicExpanded cyclicExpandedUnique
      center.val)]

private theorem degreeA0 : (cyclicCertified.moleculeGraph.neighborFinset A0).card = 4 := by
  rw [neighborCard_eq_recordLength]
  simpa using
    (expanded_root_records 0 TetrahedralInputParity.anticlockwise).length_eq

private theorem degreeA2 : (cyclicCertified.moleculeGraph.neighborFinset A2).card = 4 := by
  rw [neighborCard_eq_recordLength]
  simpa using
    (expanded_left_records 0 TetrahedralInputParity.anticlockwise).length_eq

private theorem degreeA4 : (cyclicCertified.moleculeGraph.neighborFinset A4).card = 4 := by
  rw [neighborCard_eq_recordLength]
  simpa using
    (expanded_right_records 0 TetrahedralInputParity.anticlockwise).length_eq

private theorem detected_iff (center : cyclicCertified.Atom) :
    center ∈ cyclicCertified.tetrahedralCenterSet ↔
      (cyclicCertified.moleculeGraph.neighborFinset center).card = 4 := by
  simp [CertifiedLocalizedCIPInput.tetrahedralCenterSet, MoleculeGraph.mem_tetrahedralCenterSet,
    MoleculeGraph.isTetrahedralCenter_iff_neighborFinset_card]

private theorem detectedA0 : A0 ∈ cyclicCertified.tetrahedralCenterSet :=
  (detected_iff A0).mpr degreeA0

private theorem detectedA2 : A2 ∈ cyclicCertified.tetrahedralCenterSet :=
  (detected_iff A2).mpr degreeA2

private theorem detectedA4 : A4 ∈ cyclicCertified.tetrahedralCenterSet :=
  (detected_iff A4).mpr degreeA4

def rootCenter : cyclicCertified.TetrahedralCenter := ⟨A0, detectedA0⟩
def armCenter : cyclicCertified.TetrahedralCenter := ⟨A2, detectedA2⟩
def closingCenter : cyclicCertified.TetrahedralCenter := ⟨A4, detectedA4⟩

private theorem A0_ne_A2 : A0 ≠ A2 := by
  intro equal
  exact absurd (congrArg Fin.val equal) (by decide : (0 : Nat) ≠ 2)

private theorem A0_ne_A4 : A0 ≠ A4 := by
  intro equal
  exact absurd (congrArg Fin.val equal) (by decide : (0 : Nat) ≠ 4)

private theorem A2_ne_A4 : A2 ≠ A4 := by
  intro equal
  exact absurd (congrArg Fin.val equal) (by decide : (2 : Nat) ≠ 4)

private theorem A2_ne_A0 : A2 ≠ A0 := A0_ne_A2.symm
private theorem A4_ne_A0 : A4 ≠ A0 := A0_ne_A4.symm
private theorem A4_ne_A2 : A4 ≠ A2 := A2_ne_A4.symm

private theorem adj_A0_A2 : cyclicCertified.moleculeGraph.Adj A0 A2 := by
  refine (neighbor_mem_iff A0 A2).mpr ?_
  simpa [A2] using
    (expanded_root_records 0 TetrahedralInputParity.anticlockwise).mem_iff.mpr
      (by decide : (2 : Nat) ∈ [0 + 5, 1, 2, 0 + 4])

private theorem adj_A0_A4 : cyclicCertified.moleculeGraph.Adj A0 A4 := by
  refine (neighbor_mem_iff A0 A4).mpr ?_
  simpa [A4] using
    (expanded_root_records 0 TetrahedralInputParity.anticlockwise).mem_iff.mpr
      (by decide : (4 : Nat) ∈ [0 + 5, 1, 2, 0 + 4])

private theorem adj_A2_A4 : cyclicCertified.moleculeGraph.Adj A2 A4 := by
  refine (neighbor_mem_iff A2 A4).mpr ?_
  simpa [A4] using
    (expanded_left_records 0 TetrahedralInputParity.anticlockwise).mem_iff.mpr
      (by decide : (4 : Nat) ∈ [0, 0 + 6, 3, 4])

private theorem adj_A2_A0 : cyclicCertified.moleculeGraph.Adj A2 A0 :=
  (cyclicCertified.moleculeGraph.adj_symm (u := A0) (v := A2)).mp adj_A0_A2

private theorem adj_A4_A0 : cyclicCertified.moleculeGraph.Adj A4 A0 :=
  (cyclicCertified.moleculeGraph.adj_symm (u := A0) (v := A4)).mp adj_A0_A4

private theorem adj_A4_A2 : cyclicCertified.moleculeGraph.Adj A4 A2 :=
  (cyclicCertified.moleculeGraph.adj_symm (u := A2) (v := A4)).mp adj_A2_A4

/-- Triangle of the three degree-four atoms on the expanded ring. -/
def cycleAtoms : Finset cyclicCertified.Atom := {A0, A2, A4}

private theorem cycleCard : cycleAtoms.card = 3 := by
  have notA2 : A2 ∉ ({A4} : Finset cyclicCertified.Atom) := by
    simpa using A2_ne_A4
  have notA0 : A0 ∉ ({A2, A4} : Finset cyclicCertified.Atom) := by
    intro member
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with equal | equal
    · exact A0_ne_A2 equal
    · exact A0_ne_A4 equal
  rw [cycleAtoms, Finset.card_insert_of_notMem notA0, Finset.card_insert_of_notMem notA2,
    Finset.card_singleton]

private theorem A0_mem_cycle : A0 ∈ cycleAtoms := by
  simp [cycleAtoms]

private theorem A2_mem_cycle : A2 ∈ cycleAtoms := by
  simp [cycleAtoms]

private theorem A4_mem_cycle : A4 ∈ cycleAtoms := by
  simp [cycleAtoms]

private theorem cycleNeighborCard (center n1 n2 : cyclicCertified.Atom)
    (centerMem : center ∈ cycleAtoms) (n1Mem : n1 ∈ cycleAtoms) (n2Mem : n2 ∈ cycleAtoms)
    (distinct : n1 ≠ n2)
    (edge1 : cyclicCertified.moleculeGraph.Adj center n1)
    (edge2 : cyclicCertified.moleculeGraph.Adj center n2) :
    (cyclicCertified.localizedCycleNeighbors cycleAtoms center).card = 2 := by
  have pairSubset :
      ({n1, n2} : Finset cyclicCertified.Atom) ⊆
        cyclicCertified.localizedCycleNeighbors cycleAtoms center := by
    intro atom member
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with equal | equal
    · refine (mem_localizedCycleNeighbors_iff cyclicCertified cycleAtoms center atom).mpr ⟨?_, ?_⟩
      · simpa [equal] using n1Mem
      · simpa [equal] using edge1
    · refine (mem_localizedCycleNeighbors_iff cyclicCertified cycleAtoms center atom).mpr ⟨?_, ?_⟩
      · simpa [equal] using n2Mem
      · simpa [equal] using edge2
  have insideErase :
      cyclicCertified.localizedCycleNeighbors cycleAtoms center ⊆ cycleAtoms.erase center := by
    intro neighbor neighborMem
    have split :=
      (mem_localizedCycleNeighbors_iff cyclicCertified cycleAtoms center neighbor).mp neighborMem
    rw [Finset.mem_erase]
    refine ⟨?_, split.1⟩
    intro equal
    have recordMem := (neighbor_mem_iff center neighbor).mp split.2
    exact (recordNeighbor_bounds cyclicExpandedWell recordMem).2 (congrArg Fin.val equal)
  have eraseCard : (cycleAtoms.erase center).card = 2 := by
    rw [Finset.card_erase_of_mem centerMem, cycleCard]
  have notSingleton : n1 ∉ ({n2} : Finset cyclicCertified.Atom) := by
    simpa using distinct
  have pairCard : ({n1, n2} : Finset cyclicCertified.Atom).card = 2 := by
    rw [Finset.card_insert_of_notMem notSingleton, Finset.card_singleton]
  have upper :
      (cyclicCertified.localizedCycleNeighbors cycleAtoms center).card ≤ 2 := by
    simpa [eraseCard] using Finset.card_le_card insideErase
  have lower :
      2 ≤ (cyclicCertified.localizedCycleNeighbors cycleAtoms center).card := by
    simpa [pairCard] using Finset.card_le_card pairSubset
  exact Nat.le_antisymm upper lower

private theorem inducedAdj {left right : cyclicCertified.Atom}
    (leftMem : left ∈ cycleAtoms) (rightMem : right ∈ cycleAtoms)
    (adjacent : cyclicCertified.moleculeGraph.Adj left right) :
    (cyclicCertified.localizedInducedCycleGraph cycleAtoms).Adj left right := by
  rw [localizedInducedCycleGraph_adj]
  exact ⟨leftMem, rightMem, adjacent⟩

theorem molecularCycle :
    cyclicReferenceInput.certified.DeclarativeLocalizedSimpleCycleVertexSet cycleAtoms := by
  refine ⟨?_, ?_, ?_⟩
  · rw [cycleCard]
  · intro center centerMem
    simp only [cycleAtoms, Finset.mem_insert, Finset.mem_singleton] at centerMem
    rcases centerMem with rfl | rfl | rfl
    · exact cycleNeighborCard A0 A2 A4 A0_mem_cycle A2_mem_cycle A4_mem_cycle A2_ne_A4
        adj_A0_A2 adj_A0_A4
    · exact cycleNeighborCard A2 A0 A4 A2_mem_cycle A0_mem_cycle A4_mem_cycle A0_ne_A4
        adj_A2_A0 adj_A2_A4
    · exact cycleNeighborCard A4 A0 A2 A4_mem_cycle A0_mem_cycle A2_mem_cycle A0_ne_A2
        adj_A4_A0 adj_A4_A2
  · intro left leftMem right rightMem
    simp only [cycleAtoms, Finset.mem_insert, Finset.mem_singleton] at leftMem rightMem
    rcases leftMem with rfl | rfl | rfl <;> rcases rightMem with rfl | rfl | rfl
    · exact SimpleGraph.Reachable.refl _
    · exact SimpleGraph.Adj.reachable (inducedAdj A0_mem_cycle A2_mem_cycle adj_A0_A2)
    · exact SimpleGraph.Adj.reachable (inducedAdj A0_mem_cycle A4_mem_cycle adj_A0_A4)
    · exact SimpleGraph.Adj.reachable (inducedAdj A2_mem_cycle A0_mem_cycle adj_A2_A0)
    · exact SimpleGraph.Reachable.refl _
    · exact SimpleGraph.Adj.reachable (inducedAdj A2_mem_cycle A4_mem_cycle adj_A2_A4)
    · exact SimpleGraph.Adj.reachable (inducedAdj A4_mem_cycle A0_mem_cycle adj_A4_A0)
    · exact SimpleGraph.Adj.reachable (inducedAdj A4_mem_cycle A2_mem_cycle adj_A4_A2)
    · exact SimpleGraph.Reachable.refl _

theorem degreeFourCentersOnCycle :
    (cyclicReferenceInput.certified.moleculeGraph.neighborFinset A0).card = 4 ∧
      (cyclicReferenceInput.certified.moleculeGraph.neighborFinset A2).card = 4 ∧
        (cyclicReferenceInput.certified.moleculeGraph.neighborFinset A4).card = 4 ∧
          A0 ∈ cyclicReferenceInput.certified.tetrahedralCenterSet ∧
            A2 ∈ cyclicReferenceInput.certified.tetrahedralCenterSet ∧
              A4 ∈ cyclicReferenceInput.certified.tetrahedralCenterSet ∧
                A0 ∈ cycleAtoms ∧ A2 ∈ cycleAtoms ∧ A4 ∈ cycleAtoms :=
  ⟨degreeA0, degreeA2, degreeA4, detectedA0, detectedA2, detectedA4,
    A0_mem_cycle, A2_mem_cycle, A4_mem_cycle⟩

private def rootNode : OfficialCIPNode cyclicCertified.Atom := OfficialCIPNode.root A0
private def armNode : OfficialCIPNode cyclicCertified.Atom := rootNode.extend A2 0
private def closingNode : OfficialCIPNode cyclicCertified.Atom := armNode.extend A4 0
private def duplicateNode : OfficialCIPNode cyclicCertified.Atom := closingNode.extend A0 0

private def armAddress : List Nat :=
  [cyclicCertified.executableOfficialChildCopySlot rootNode A2 0]

private def closingAddress : List Nat :=
  armAddress ++ [cyclicCertified.executableOfficialChildCopySlot armNode A4 0]

private def duplicateAddress : List Nat :=
  closingAddress ++ [cyclicCertified.executableOfficialChildCopySlot closingNode A0 0]

private theorem root_history : rootNode.history = [A0] := by
  simp [rootNode, OfficialCIPNode.root]

private theorem arm_history : armNode.history = [A2, A0] := by
  simp [armNode, root_history, OfficialCIPNode.extend_history]

private theorem closing_history : closingNode.history = [A4, A2, A0] := by
  simp [closingNode, arm_history, OfficialCIPNode.extend_history]

private theorem root_current : rootNode.current? = some A0 := by
  simp [rootNode, OfficialCIPNode.root]

private theorem arm_current : armNode.current? = some A2 := by
  simp [armNode, OfficialCIPNode.extend_current?]

private theorem closing_current : closingNode.current? = some A4 := by
  simp [closingNode, OfficialCIPNode.extend_current?]

private theorem duplicate_current_node : duplicateNode.current? = some A0 := by
  simp [duplicateNode, OfficialCIPNode.extend_current?]

private theorem root_parent : rootNode.parent? = none := by
  rw [OfficialCIPNode.parent?, root_history]

private theorem arm_parent : armNode.parent? = some A0 := by
  rw [OfficialCIPNode.parent?, arm_history]

private theorem closing_parent : closingNode.parent? = some A2 := by
  rw [OfficialCIPNode.parent?, closing_history]

private theorem root_notParent : rootNode.parent? ≠ some A2 := by
  rw [root_parent]
  intro equal
  cases equal

private theorem arm_notParent : armNode.parent? ≠ some A4 := by
  rw [arm_parent]
  intro equal
  exact A0_ne_A4 (Option.some.inj equal)

private theorem closing_notParent : closingNode.parent? ≠ some A0 := by
  rw [closing_parent]
  intro equal
  exact A2_ne_A0 (Option.some.inj equal)

private theorem root_fresh : A2 ∉ rootNode.history := by
  rw [root_history]
  intro member
  simp at member
  exact A2_ne_A0 member

private theorem arm_fresh : A4 ∉ armNode.history := by
  rw [arm_history]
  intro member
  simp at member
  rcases member with equal | equal
  · exact A4_ne_A2 equal
  · exact A4_ne_A0 equal

private theorem closing_visited : A0 ∈ closingNode.history := by
  rw [closing_history]
  simp

private theorem pathRoot :
    SimpleOccurrencePath cyclicCertified A0 rootNode [] :=
  SimpleOccurrencePath.root

private theorem pathArm :
    SimpleOccurrencePath cyclicCertified A0 armNode armAddress := by
  simpa [armNode, armAddress, List.nil_append] using
    SimpleOccurrencePath.step pathRoot root_current adj_A0_A2 root_notParent root_fresh

private theorem pathClosing :
    SimpleOccurrencePath cyclicCertified A0 closingNode closingAddress := by
  simpa [closingNode, closingAddress] using
    SimpleOccurrencePath.step pathArm arm_current adj_A2_A4 arm_notParent arm_fresh

private theorem rootLegit : LegitimateOccurrence cyclicCertified A0 rootNode [] :=
  LegitimateOccurrence.simple pathRoot

private theorem armLegit : LegitimateOccurrence cyclicCertified A0 armNode armAddress :=
  LegitimateOccurrence.simple pathArm

private theorem closingLegit :
    LegitimateOccurrence cyclicCertified A0 closingNode closingAddress :=
  LegitimateOccurrence.simple pathClosing

private theorem duplicateLegit :
    LegitimateOccurrence cyclicCertified A0 duplicateNode duplicateAddress := by
  simpa [duplicateNode, duplicateAddress] using
    LegitimateOccurrence.ring pathClosing closing_current adj_A4_A0 closing_notParent
      closing_visited

def rootOccurrence : cyclicCertified.LocalizedCIPOccurrence
    cyclicCertified.certified.input.molecule.atomCount :=
  cyclicCertified.legitimateOccurrenceCarrier rootLegit

def armOccurrence : cyclicCertified.LocalizedCIPOccurrence
    cyclicCertified.certified.input.molecule.atomCount :=
  cyclicCertified.legitimateOccurrenceCarrier armLegit

def closingOccurrence : cyclicCertified.LocalizedCIPOccurrence
    cyclicCertified.certified.input.molecule.atomCount :=
  cyclicCertified.legitimateOccurrenceCarrier closingLegit

def duplicateOccurrence : cyclicCertified.LocalizedCIPOccurrence
    cyclicCertified.certified.input.molecule.atomCount :=
  cyclicCertified.legitimateOccurrenceCarrier duplicateLegit

private theorem rootNode_real :
    cyclicCertified.RealTetrahedralCenterNode rootNode rootCenter :=
  ⟨cyclicCertified.simpleOccurrencePath_provenance pathRoot,
    by simpa [rootCenter] using root_current⟩

private theorem armNode_real :
    cyclicCertified.RealTetrahedralCenterNode armNode armCenter :=
  ⟨cyclicCertified.simpleOccurrencePath_provenance pathArm,
    by simpa [armCenter] using arm_current⟩

private theorem closingNode_real :
    cyclicCertified.RealTetrahedralCenterNode closingNode closingCenter :=
  ⟨cyclicCertified.simpleOccurrencePath_provenance pathClosing,
    by simpa [closingCenter] using closing_current⟩

private theorem armAddress_ne_nil : armAddress ≠ [] := by
  unfold armAddress
  exact List.cons_ne_nil _ _

private theorem closingAddress_ne_nil : closingAddress ≠ [] := by
  unfold closingAddress armAddress
  rw [List.cons_append]
  exact List.cons_ne_nil _ _

private theorem duplicateAddress_ne_nil : duplicateAddress ≠ [] := by
  unfold duplicateAddress closingAddress armAddress
  rw [List.cons_append, List.cons_append]
  exact List.cons_ne_nil _ _

private theorem duplicateDistanceZero : closingNode.duplicateRootDistance A0 = 0 := by
  rw [OfficialCIPNode.duplicateRootDistance, closing_history]
  have reversed : ([A4, A2, A0] : List cyclicCertified.Atom).reverse = [A0, A2, A4] := by
    simp [List.reverse_cons, List.reverse_nil]
  rw [reversed, firstIndexOf?_cons_self]
  rfl

private theorem duplicateNode_provenance :
    duplicateNode.provenance = OfficialCIPNodeProvenance.ringDuplicate 0 := by
  simpa [duplicateNode, duplicateDistanceZero] using
    cyclicCertified.legitimateOccurrence_ring_provenance closing_visited

theorem rootRecognized :
    cyclicReferenceInput.certified.localizedOccurrenceDescriptorCenter? rootOccurrence =
        some rootCenter ∧
      rootCenter.1 = A0 ∧
      rootOccurrence.1.address = [] ∧
      rootOccurrence.1.root = A0 ∧
      rootOccurrence.1 ∈ cyclicReferenceInput.certified.localizedOccurrences
        cyclicReferenceInput.certified.certified.input.molecule.atomCount := by
  refine ⟨?_, rfl, ?_, ?_, rootOccurrence.2⟩
  · rw [localizedOccurrenceDescriptorCenter?_eq_some_iff]
    simpa [cyclicReferenceInput, rootOccurrence, legitimateOccurrenceCarrier_node] using
      rootNode_real
  · simp [rootOccurrence, legitimateOccurrenceCarrier_address]
  · simp [rootOccurrence, legitimateOccurrenceCarrier_root]

theorem armRecognizedNonroot :
    cyclicReferenceInput.certified.localizedOccurrenceDescriptorCenter? armOccurrence =
        some armCenter ∧
      armCenter.1 = A2 ∧
      A2 ≠ A0 ∧
      armOccurrence.1.address ≠ [] ∧
      armOccurrence.1.root = A0 ∧
      armOccurrence.1 ∈ cyclicReferenceInput.certified.localizedOccurrences
        cyclicReferenceInput.certified.certified.input.molecule.atomCount := by
  refine ⟨?_, rfl, A2_ne_A0, ?_, ?_, armOccurrence.2⟩
  · rw [localizedOccurrenceDescriptorCenter?_eq_some_iff]
    simpa [cyclicReferenceInput, armOccurrence, legitimateOccurrenceCarrier_node] using
      armNode_real
  · simpa [armOccurrence, armLegit, legitimateOccurrenceCarrier_address] using
      armAddress_ne_nil
  · simp [armOccurrence, legitimateOccurrenceCarrier_root]

theorem closingRecognizedNonroot :
    cyclicReferenceInput.certified.localizedOccurrenceDescriptorCenter? closingOccurrence =
        some closingCenter ∧
      closingCenter.1 = A4 ∧
      A4 ≠ A0 ∧
      closingOccurrence.1.address ≠ [] ∧
      closingOccurrence.1.root = A0 ∧
      closingOccurrence.1 ∈ cyclicReferenceInput.certified.localizedOccurrences
        cyclicReferenceInput.certified.certified.input.molecule.atomCount := by
  refine ⟨?_, rfl, A4_ne_A0, ?_, ?_, closingOccurrence.2⟩
  · rw [localizedOccurrenceDescriptorCenter?_eq_some_iff]
    simpa [cyclicReferenceInput, closingOccurrence, legitimateOccurrenceCarrier_node] using
      closingNode_real
  · simpa [closingOccurrence, closingLegit, legitimateOccurrenceCarrier_address] using
      closingAddress_ne_nil
  · simp [closingOccurrence, legitimateOccurrenceCarrier_root]

theorem ringDuplicateCarrier :
    duplicateOccurrence.1.node.provenance =
        OfficialCIPNodeProvenance.ringDuplicate 0 ∧
      duplicateOccurrence.1.node.current? = some A0 ∧
      duplicateOccurrence.1.address ≠ [] ∧
      duplicateOccurrence.1.root = A0 ∧
      duplicateOccurrence.1 ∈ cyclicReferenceInput.certified.localizedOccurrences
        cyclicReferenceInput.certified.certified.input.molecule.atomCount := by
  refine ⟨?_, ?_, ?_, ?_, duplicateOccurrence.2⟩
  · simpa [cyclicReferenceInput, duplicateOccurrence, duplicateLegit,
      legitimateOccurrenceCarrier_node] using duplicateNode_provenance
  · simpa [cyclicReferenceInput, duplicateOccurrence, duplicateLegit,
      legitimateOccurrenceCarrier_node] using duplicate_current_node
  · simpa [duplicateOccurrence, duplicateLegit, legitimateOccurrenceCarrier_address] using
      duplicateAddress_ne_nil
  · simp [duplicateOccurrence, legitimateOccurrenceCarrier_root]

end TetraStereo.OneCenter.LocalizedCyclicInputWitness

assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputWitness.heavyAtomCount
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputWitness.rawBondsSingle
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputWitness.parsedRing
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputWitness.certifiedRingFamily
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputWitness.runtimeRootLigands
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputWitness.runtimeRootWidth
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputWitness.source_conversion
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputWitness.source_structurallyWellFormed
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputWitness.source_graphReady
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputWitness.atomCount_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputWitness.input_simpleBonded
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputWitness.molecularCycle
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputWitness.degreeFourCentersOnCycle
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputWitness.rootRecognized
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputWitness.armRecognizedNonroot
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputWitness.closingRecognizedNonroot
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicInputWitness.ringDuplicateCarrier
