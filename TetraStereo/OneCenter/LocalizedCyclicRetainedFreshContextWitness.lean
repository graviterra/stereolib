import TetraStereo.OneCenter.LocalizedCyclicInputWitness
import TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness
import TetraStereo.OneCenter.LocalizedConstitutionalRootSeparation
import TetraStereo.OneCenter.LocalizedParametricCumulativeLabels
import TetraStereo.OneCenter.LocalizedRuleMajorRule4aAgreement
import TetraStereo.OneCenter.LocalizedSimpleBondFourLigandFrames
import TetraStereo.OneCenter.LocalizedOutwardDecoratedSourceFaithfulness
import TetraStereo.OneCenter.LocalizedActualFrameChildClassification
import TetraStereo.OneCenter.LocalizedTetrahedralRootDoubleBondBound
import TetraStereo.OneCenter.LocalizedOccurrenceExecutableRoots
import TetraStereo.OneCenter.LocalizedRetainedRealArmExpansion
import TetraStereo.OneCenter.OfficialRuleMajorKey
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 8192

/-!
# Retained and fresh contexts at atom 4

The retained carrier is the accepted closing occurrence: root `A0`, history
`[A4, A2, A0]`, real, Rule-1b distance 2. Its four-ligand frame keeps the real
parent occurrence at atom 2, history `[A2, A0]`, and the duplicate leaf of atom 0
at stored distance 0. Extending the closing node by `A2` repeats the immediate
parent, so that pair is not an executable child copy.

The fresh carrier is the final root at atom 4. Its atom-2 arm carries chlorine
and its atom-0 arm carries fluorine. Both Rule-4a keys are the successful builds
at fuel `2 * (carrierFuel + 1)`, and each arm is the predecessor cut of that
build. The two comparisons are both `Ordering.gt`. The direct edge from atom 0
to atom 4 has Rule-1b distance 1; that is a different source occurrence.
`referenceState` is not evaluated, and no letter is assigned.
-/

namespace TetraStereo.OneCenter.LocalizedCyclicRetainedFreshContextWitness

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.OneCenter.SemanticMolecule
open TetraStereo.OneCenter.SemanticInteraction
open TetraStereo.OneCenter.MoleculeGraph
open TetraStereo.OneCenter.OfficialRuleMajorKey
open TetraStereo.OneCenter.OfficialCIPNode
open TetraStereo.OneCenter.LocalizedCyclicInputWitness
open TetraStereo.OneCenter.LocalizedCyclicInputRuntimeWitness
open TetraStereo.OneCenter.LocalizedRuleMajorReference
open TetraStereo.OneCenter.DeclarativeCIP
open TetraStereo.OneCenter.DeclarativeCIP.RetainedOccurrenceCarrier
open TetraStereo.OneCenter.ConstitutionalLexAlgebra
open TetraStereo.UniversalProof.NativeRingDomain
open TetraStereo.UniversalProof.NativeRingHydrogenFacts
open TetraStereo.UniversalProof.NativeRingRuntimeGraphFacts
open TetraStereo.UniversalProof.GeneralRingPhysicalAdmission
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery

open scoped Classical

noncomputable section

abbrev graph : MoleculeGraph cyclicCertified.Atom := cyclicCertified.moleculeGraph

def A1 : cyclicCertified.Atom := atom ⟨1, by decide⟩
def A3 : cyclicCertified.Atom := atom ⟨3, by decide⟩
def A5 : cyclicCertified.Atom := atom ⟨5, by decide⟩
def A6 : cyclicCertified.Atom := atom ⟨6, by decide⟩

private theorem expandedCount : cyclicExpanded.atomCount = 9 := by
  have raw := expanded_atom_count 0 TetrahedralInputParity.anticlockwise
  have arith : 3 * 0 + 9 = 9 := by decide
  rwa [arith] at raw

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

private theorem semanticRecord_mpr (left right : ℕ)
    (bond : RawBond) (bondMember : bond ∈ cyclicExpanded.bonds)
    (connects : bond.connects left right = true) :
    (semanticEdgeKey left right, 1) ∈ cyclicSource.molecule.localizedCovalentRecords := by
  rw [SemanticMolecule.localizedCovalentRecords,
    cyclicExpanded.toSemanticMolecule?_interactions cyclicSource.molecule semanticConverted,
    List.mem_filterMap]
  refine ⟨bond.toSemanticInteraction, List.mem_map.mpr ⟨bond, bondMember, rfl⟩, ?_⟩
  rw [covalentRecord_of_single bond bondMember]
  rw [show bond.edgeKey = semanticEdgeKey bond.source bond.target from rfl]
  rw [(connects_semantic bond left right).mp connects]

private theorem adj_of_record (center neighbor : cyclicCertified.Atom)
    (member : neighbor.val ∈ recordNeighbors cyclicExpanded center.val) :
    graph.Adj center neighbor := by
  have distinctVal : center.val ≠ neighbor.val :=
    Ne.symm (recordNeighbor_bounds cyclicExpandedWell member).2
  have distinct : center ≠ neighbor := fun equal => distinctVal (congrArg Fin.val equal)
  obtain ⟨bond, bondMember, connects⟩ :=
    (cyclicExpanded.bondOrder_pos_iff_exists_bond distinctVal).mp
      ((recordNeighbor_positive_iff cyclicExpanded cyclicExpandedWell
        center.val neighbor.val).mp member)
  have present := semanticRecord_mpr center.val neighbor.val bond bondMember connects
  have bondOne := cyclicSource.molecule.toLocalizedMoleculeGraph_bond_eq_of_record
    center neighbor 1 cyclicCertified.graphReady distinct present
  have graphOne : graph.bond center neighbor = 1 := by
    simpa [graph, CertifiedLocalizedCIPInput.moleculeGraph] using bondOne
  rw [MoleculeGraph.Adj, graphOne]
  exact Nat.zero_lt_one

private theorem record_at (center : ℕ) (row : List ℕ)
    (perm : (recordNeighbors cyclicExpanded center).Perm row) (neighbor : ℕ)
    (member : neighbor ∈ row) :
    neighbor ∈ recordNeighbors cyclicExpanded center :=
  perm.mem_iff.mpr member

private theorem adj_A0_A2 : graph.Adj A0 A2 := by
  apply adj_of_record
  simp only [A0, A2, atom_val]
  exact record_at 0 [5, 1, 2, 4]
    (expanded_root_records 0 TetrahedralInputParity.anticlockwise) 2 (by simp)

private theorem adj_A2_A4 : graph.Adj A2 A4 := by
  apply adj_of_record
  simp only [A2, A4, atom_val]
  exact record_at 2 [0, 6, 3, 4]
    (expanded_left_records 0 TetrahedralInputParity.anticlockwise) 4 (by simp)

private theorem adj_A4_A0 : graph.Adj A4 A0 := by
  apply adj_of_record
  simp only [A4, A0, atom_val]
  exact record_at 4 [2, 7, 8, 0]
    (by simpa using expanded_right_records 0 TetrahedralInputParity.anticlockwise) 0 (by simp)

private theorem adj_A2_A0 : graph.Adj A2 A0 := by
  apply adj_of_record
  simp only [A2, A0, atom_val]
  exact record_at 2 [0, 6, 3, 4]
    (expanded_left_records 0 TetrahedralInputParity.anticlockwise) 0 (by simp)

private theorem adj_A2_A3 : graph.Adj A2 A3 := by
  apply adj_of_record
  simp only [A2, A3, atom_val]
  exact record_at 2 [0, 6, 3, 4]
    (expanded_left_records 0 TetrahedralInputParity.anticlockwise) 3 (by simp)

private theorem adj_A2_A6 : graph.Adj A2 A6 := by
  apply adj_of_record
  simp only [A2, A6, atom_val]
  exact record_at 2 [0, 6, 3, 4]
    (expanded_left_records 0 TetrahedralInputParity.anticlockwise) 6 (by simp)

private theorem adj_A0_A1 : graph.Adj A0 A1 := by
  apply adj_of_record
  simp only [A0, A1, atom_val]
  exact record_at 0 [5, 1, 2, 4]
    (expanded_root_records 0 TetrahedralInputParity.anticlockwise) 1 (by simp)

private theorem adj_A0_A5 : graph.Adj A0 A5 := by
  apply adj_of_record
  simp only [A0, A5, atom_val]
  exact record_at 0 [5, 1, 2, 4]
    (expanded_root_records 0 TetrahedralInputParity.anticlockwise) 5 (by simp)

private theorem val_ne {i j : Fin 9} (different : i.val ≠ j.val) : atom i ≠ atom j := by
  intro equal
  exact different (by simpa [atom_val] using congrArg Fin.val equal)

private theorem A0_ne_A2 : A0 ≠ A2 := val_ne (by decide : (0 : ℕ) ≠ 2)
private theorem A0_ne_A4 : A0 ≠ A4 := val_ne (by decide : (0 : ℕ) ≠ 4)
private theorem A2_ne_A4 : A2 ≠ A4 := val_ne (by decide : (2 : ℕ) ≠ 4)
private theorem A4_ne_A2 : A4 ≠ A2 := A2_ne_A4.symm
private theorem A4_ne_A0 : A4 ≠ A0 := A0_ne_A4.symm
private theorem A2_ne_A0 : A2 ≠ A0 := A0_ne_A2.symm
private theorem A3_ne_A2 : A3 ≠ A2 := val_ne (by decide : (3 : ℕ) ≠ 2)
private theorem A3_ne_A4 : A3 ≠ A4 := val_ne (by decide : (3 : ℕ) ≠ 4)
private theorem A6_ne_A2 : A6 ≠ A2 := val_ne (by decide : (6 : ℕ) ≠ 2)
private theorem A6_ne_A4 : A6 ≠ A4 := val_ne (by decide : (6 : ℕ) ≠ 4)
private theorem A1_ne_A0 : A1 ≠ A0 := val_ne (by decide : (1 : ℕ) ≠ 0)
private theorem A1_ne_A4 : A1 ≠ A4 := val_ne (by decide : (1 : ℕ) ≠ 4)
private theorem A5_ne_A0 : A5 ≠ A0 := val_ne (by decide : (5 : ℕ) ≠ 0)
private theorem A5_ne_A4 : A5 ≠ A4 := val_ne (by decide : (5 : ℕ) ≠ 4)
private theorem A2_ne_A1 : A2 ≠ A1 := val_ne (by decide : (2 : ℕ) ≠ 1)
private theorem A2_ne_A5 : A2 ≠ A5 := val_ne (by decide : (2 : ℕ) ≠ 5)

/-! ## Source atomic numbers and the certified graph -/

private theorem atomAt_some (index : Fin 9) :
    ∃ spec, cyclicExpanded.atomAt? index.val = some spec := by
  have bound : index.val < cyclicExpanded.atoms.length := by
    rw [← RawMolecule.atomCount, expandedCount]
    exact index.isLt
  refine ⟨cyclicExpanded.atoms.get ⟨index.val, bound⟩, ?_⟩
  simpa [RawMolecule.atomAt?] using
    (listGet?_eq_some_get cyclicExpanded.atoms ⟨index.val, bound⟩)

private theorem original_atomicNumber (index : ℕ) (spec : AtomSpec) {n : ℕ}
    (raw : (ringRaw 0 TetrahedralInputParity.anticlockwise).atomAt? index = some spec)
    (number : spec.element.atomicNumber = n) :
    ∃ observed, cyclicExpanded.atomAt? index = some observed ∧
      observed.element.atomicNumber = n := by
  refine ⟨materializedAtomSpec spec,
    expanded_original_atom 0 TetrahedralInputParity.anticlockwise index spec raw, ?_⟩
  simp [materializedAtomSpec_element, number]

private theorem root_source_atomicNumber :
    ∃ spec, cyclicExpanded.atomAt? 0 = some spec ∧ spec.element.atomicNumber = 6 :=
  original_atomicNumber 0 (taggedCarbon TetrahedralInputParity.anticlockwise)
    (ringRaw_atomAt_zero 0 TetrahedralInputParity.anticlockwise)
    (by simp [taggedCarbon, carbon, AtomSpec.aliphatic, Element.atomicNumber])

private theorem fluorine_source_atomicNumber :
    ∃ spec, cyclicExpanded.atomAt? 1 = some spec ∧ spec.element.atomicNumber = 9 :=
  original_atomicNumber 1
    { AtomSpec.aliphatic .F with explicitHydrogens? := some 0 }
    (ringRaw_atomAt_one 0 TetrahedralInputParity.anticlockwise)
    (by simp [AtomSpec.aliphatic, Element.atomicNumber])

private theorem arm_source_atomicNumber :
    ∃ spec, cyclicExpanded.atomAt? 2 = some spec ∧ spec.element.atomicNumber = 6 :=
  original_atomicNumber 2 (carbon 1)
    (ringRaw_atomAt_two 0 TetrahedralInputParity.anticlockwise)
    (by simp [carbon, AtomSpec.aliphatic, Element.atomicNumber])

private theorem chlorine_source_atomicNumber :
    ∃ spec, cyclicExpanded.atomAt? 3 = some spec ∧ spec.element.atomicNumber = 17 :=
  original_atomicNumber 3
    { AtomSpec.aliphatic .Cl with explicitHydrogens? := some 0 }
    (ringRaw_atomAt_three 0 TetrahedralInputParity.anticlockwise)
    (by simp [AtomSpec.aliphatic, Element.atomicNumber])

private theorem closing_source_atomicNumber :
    ∃ spec, cyclicExpanded.atomAt? 4 = some spec ∧ spec.element.atomicNumber = 6 :=
  original_atomicNumber 4 (carbon 2)
    (ringRaw_atomAt_chain 0 TetrahedralInputParity.anticlockwise 0 (Nat.le_refl 0))
    (by simp [carbon, AtomSpec.aliphatic, Element.atomicNumber])

private theorem hydrogen_source_atomicNumber (index : Fin 9) (low : 5 ≤ index.val) :
    ∃ spec, cyclicExpanded.atomAt? index.val = some spec ∧ spec.element.atomicNumber = 1 := by
  obtain ⟨spec, lookup⟩ := atomAt_some index
  have fresh := expanded_fresh_atom 0 TetrahedralInputParity.anticlockwise
    index.val spec low lookup
  refine ⟨spec, lookup, ?_⟩
  simp [fresh.1, AtomSpec.aliphatic, Element.atomicNumber]

private theorem graph_atomicNumber (index : Fin 9) (spec : AtomSpec)
    (lookup : cyclicExpanded.atomAt? index.val = some spec) :
    graph.atomZ (atom index) = spec.element.atomicNumber := by
  let rawIndex : Fin cyclicExpanded.atomCount :=
    ⟨index.val, by rw [expandedCount]; exact index.isLt⟩
  obtain ⟨sourceAtom, semanticListed, converted⟩ :=
    cyclicExpanded.toSemanticMolecule?_atomAtFin cyclicSource.molecule semanticConverted rawIndex
  have rawBound : index.val < cyclicExpanded.atoms.length := by
    rw [← RawMolecule.atomCount, expandedCount]
    exact index.isLt
  have rawGet : cyclicExpanded.atoms.get ⟨index.val, rawBound⟩ = spec := by
    apply Option.some.inj
    exact (listGet?_eq_some_get cyclicExpanded.atoms ⟨index.val, rawBound⟩).symm.trans
      (by simpa [RawMolecule.atomAt?] using lookup)
  have convertedSpec : spec.toSemanticAtom? = some sourceAtom := by
    rw [← rawGet]
    simpa [RawMolecule.atomCount, rawIndex] using converted
  have numberEq := (AtomSpec.toSemanticAtom?_exact spec sourceAtom convertedSpec).1
  have semCount := cyclicExpanded.toSemanticMolecule?_atomCount cyclicSource.molecule
    semanticConverted
  have semanticBound : index.val < cyclicSource.molecule.atoms.length := by
    have countBound : index.val < cyclicSource.molecule.atomCount := by
      rw [semCount, expandedCount]
      exact index.isLt
    simpa [SemanticMolecule.atomCount] using countBound
  have semanticGet : cyclicSource.molecule.atoms.get ⟨index.val, semanticBound⟩ = sourceAtom := by
    apply Option.some.inj
    exact (listGet?_eq_some_get cyclicSource.molecule.atoms ⟨index.val, semanticBound⟩).symm.trans
      semanticListed
  have carrierBound : index.val < cyclicSource.molecule.atomCount := by
    rw [semCount, expandedCount]
    exact index.isLt
  have indexEq : atom index = ⟨index.val, carrierBound⟩ := Fin.ext (atom_val index)
  rw [graph, CertifiedLocalizedCIPInput.moleculeGraph, toLocalizedMoleculeGraph_atomZ, indexEq]
  change (cyclicSource.molecule.atoms.get ⟨index.val, carrierBound⟩).element.atomicNumber =
    spec.element.atomicNumber
  have getEq : cyclicSource.molecule.atoms.get ⟨index.val, carrierBound⟩ =
      cyclicSource.molecule.atoms.get ⟨index.val, semanticBound⟩ := by
    congr 1
  rw [getEq, semanticGet]
  exact numberEq

private theorem atomicNumber_at (index : Fin 9) (z : ℕ)
    (fact : ∃ spec, cyclicExpanded.atomAt? index.val = some spec ∧
      spec.element.atomicNumber = z) :
    graph.atomZ (atom index) = z := by
  obtain ⟨spec, lookup, number⟩ := fact
  rw [graph_atomicNumber index spec lookup, number]

private theorem z_root : graph.atomZ A0 = 6 :=
  atomicNumber_at ⟨0, by decide⟩ 6 root_source_atomicNumber

private theorem z_fluorine : graph.atomZ A1 = 9 :=
  atomicNumber_at ⟨1, by decide⟩ 9 fluorine_source_atomicNumber

private theorem z_arm : graph.atomZ A2 = 6 :=
  atomicNumber_at ⟨2, by decide⟩ 6 arm_source_atomicNumber

private theorem z_chlorine : graph.atomZ A3 = 17 :=
  atomicNumber_at ⟨3, by decide⟩ 17 chlorine_source_atomicNumber

private theorem z_closing : graph.atomZ A4 = 6 :=
  atomicNumber_at ⟨4, by decide⟩ 6 closing_source_atomicNumber

private theorem z_rootHydrogen : graph.atomZ A5 = 1 :=
  atomicNumber_at ⟨5, by decide⟩ 1 (hydrogen_source_atomicNumber ⟨5, by decide⟩ (by decide))

private theorem z_armHydrogen : graph.atomZ A6 = 1 :=
  atomicNumber_at ⟨6, by decide⟩ 1 (hydrogen_source_atomicNumber ⟨6, by decide⟩ (by decide))


/-! ## Actual cursors

`standardClosing` is the accepted carrier at atom 4, history `[A4, A2, A0]`.
Its four-ligand frame includes the real parent at atom 2 and the duplicate leaf of atom 0.
Stepping that node back through `A2` repeats the immediate parent, so `simpleBond_childCopy_eq_zero`
excludes it from the executable child copies. The fresh carrier is the final root at atom 4.
Both Rule-4a keys below are the successful builds at fuel `2 * (carrierFuel + 1)`, and each arm
is the predecessor cut of that build. The two comparisons agree. Path length 2 against the
direct edge of length 1 is a different source occurrence. `referenceState` is not evaluated.
-/

private theorem retained_history : standardClosing.1.node.history = [A4, A2, A0] := by
  rfl

private theorem arm_history_std : standardArm.1.node.history = [A2, A0] := by
  rfl

private theorem duplicate_node_std :
    standardDuplicate.1.node = standardClosing.1.node.extend A0 0 := by
  rfl

private theorem retained_parentAtom : standardClosing.1.node.parent? = some A2 := by
  rw [OfficialCIPNode.parent?, retained_history]

private theorem retained_visitedCore : A0 ∈ standardClosing.1.node.history := by
  rw [retained_history]
  simp

private theorem fabricated_parent_history :
    (standardClosing.1.node.extend A2 0).history = [A2, A4, A2, A0] := by
  simp [extend_history, retained_history]

theorem parent_backtrack_not_executable_child :
    standardClosing.1.node.parent? = some A2 ∧
      (A2, 0) ∉ cyclicCertified.executableOfficialChildCopies standardClosing.1.node ∧
      (standardClosing.1.node.extend A2 0).history = [A2, A4, A2, A0] ∧
      (standardClosing.1.node.extend A2 0).history ≠ [A2, A0] := by
  refine ⟨retained_parentAtom, ?_, fabricated_parent_history, ?_⟩
  · intro present
    obtain ⟨_, _, notParent⟩ :=
      cyclicCertified.simpleBond_childCopy_eq_zero input_simpleBonded _ present
    exact notParent retained_parentAtom
  · rw [fabricated_parent_history]
    intro equal
    simp [List.cons.injEq] at equal

theorem evaluationFuel_eq_twentyTwo :
    carrierFuel cyclicReferenceInput = 10 ∧
      2 * (carrierFuel cyclicReferenceInput + 1) = 22 := by
  refine ⟨standardFuel_eq_ten, ?_⟩
  rw [standardFuel_eq_ten]

private theorem fuel_enough :
    cyclicCertified.certified.input.molecule.atomCount ≤ carrierFuel cyclicReferenceInput := by
  rw [carrierFuel_eq]
  exact Nat.le_succ _

def freshTarget :
    cyclicCertified.LocalizedCIPOccurrence (carrierFuel cyclicReferenceInput) :=
  cyclicCertified.localizedFinalOccurrenceExecutable (carrierFuel cyclicReferenceInput)
    closingCenter

private theorem fresh_node : freshTarget.1.node = OfficialCIPNode.root A4 := by
  simp [freshTarget, localizedFinalOccurrenceExecutable_node, closingCenter]

private theorem fresh_address : freshTarget.1.address = [] := by
  simp [freshTarget, localizedFinalOccurrenceExecutable_address]

private theorem fresh_rootAtom : freshTarget.1.root = A4 := by
  simp [freshTarget, localizedFinalOccurrenceExecutable_root, closingCenter]

private theorem fresh_real : freshTarget.1.node.provenance = OfficialCIPNodeProvenance.realAtom := by
  simp [fresh_node, OfficialCIPNode.root]

private theorem fresh_root_history : freshTarget.1.node.history = [A4] := by
  simp [fresh_node, OfficialCIPNode.root]

private theorem fresh_root_distance : freshTarget.1.node.rule1bRootDistance = 0 := by
  rw [OfficialCIPNode.rule1bRootDistance, fresh_real, OfficialCIPNode.depth, fresh_root_history]
  rfl

private theorem adj_A0_A4 : graph.Adj A0 A4 :=
  (graph.adj_symm).1 adj_A4_A0

private theorem adj_A4_A2 : graph.Adj A4 A2 :=
  (graph.adj_symm).1 adj_A2_A4

private theorem direct_simple : SimpleFrom graph A0 [A0, A4] := by
  refine (SimpleFrom.append_iff (SimpleFrom.root_path : SimpleFrom graph A0 [A0])).2 ?_
  refine ⟨⟨A0, by simp, adj_A0_A4⟩, ?_⟩
  intro member
  simp at member
  exact A4_ne_A0 member

theorem source_path_depth_two_versus_one :
    standardClosing.1.root = A0 ∧
      standardClosing.1.node.history = [A4, A2, A0] ∧
      standardClosing.1.node.provenance = OfficialCIPNodeProvenance.realAtom ∧
      standardClosing.1.node.rule1bRootDistance = 2 ∧
      (∃ direct : cyclicCertified.LocalizedCIPOccurrence (carrierFuel cyclicReferenceInput),
        direct.1.root = A0 ∧
          direct.1.node.history = [A4, A0] ∧
          direct.1.node.provenance = OfficialCIPNodeProvenance.realAtom ∧
          direct.1.node.rule1bRootDistance = 1 ∧
          direct.1.node.history ≠ standardClosing.1.node.history) ∧
      freshTarget.1.node = OfficialCIPNode.root A4 ∧
      freshTarget.1.node.history = [A4] ∧
      freshTarget.1.node.rule1bRootDistance = 0 ∧
      freshTarget.1.node.history ≠ standardClosing.1.node.history := by
  refine ⟨standardClosing_source, retained_history, standardClosing_provenance, ?_, ?_,
    fresh_node, fresh_root_history, fresh_root_distance, ?_⟩
  · rw [OfficialCIPNode.rule1bRootDistance, standardClosing_provenance, OfficialCIPNode.depth,
      retained_history]
    rfl
  · obtain ⟨direct, rootEq, reverseEq, real⟩ :=
      cyclicCertified.exists_occurrence_of_simpleFrom direct_simple fuel_enough
    have history : direct.1.node.history = [A4, A0] := by
      rw [← List.reverse_reverse direct.1.node.history, reverseEq]
      simp [List.reverse_cons, List.reverse_nil]
    refine ⟨direct, rootEq, history, real, ?_, ?_⟩
    · rw [OfficialCIPNode.rule1bRootDistance, real, OfficialCIPNode.depth, history]
      rfl
    · rw [history, retained_history]
      intro equal
      have lengths := congrArg List.length equal
      simp at lengths
  · rw [fresh_root_history, retained_history]
    intro equal
    have lengths := congrArg List.length equal
    simp at lengths

/-! ## Neighborhoods used by the second spheres -/

private theorem degree_A0 : (graph.neighborFinset A0).card = 4 := by
  simpa [graph, cyclicReferenceInput] using degreeFourCentersOnCycle.1

private theorem degree_A2 : (graph.neighborFinset A2).card = 4 := by
  simpa [graph, cyclicReferenceInput] using degreeFourCentersOnCycle.2.1

private theorem A0_ne_A3 : A0 ≠ A3 := val_ne (by decide : (0 : ℕ) ≠ 3)
private theorem A0_ne_A6 : A0 ≠ A6 := val_ne (by decide : (0 : ℕ) ≠ 6)
private theorem A3_ne_A6 : A3 ≠ A6 := val_ne (by decide : (3 : ℕ) ≠ 6)
private theorem A5_ne_A1 : A5 ≠ A1 := val_ne (by decide : (5 : ℕ) ≠ 1)
private theorem A5_ne_A2 : A5 ≠ A2 := val_ne (by decide : (5 : ℕ) ≠ 2)

private theorem not_mem_pair {a b c : cyclicCertified.Atom} (hab : a ≠ b) (hac : a ≠ c) :
    a ∉ ({b, c} : Finset cyclicCertified.Atom) := by
  intro mem
  simp only [Finset.mem_insert, Finset.mem_singleton] at mem
  rcases mem with rfl | rfl
  · exact hab rfl
  · exact hac rfl

private theorem not_mem_triple {a b c d : cyclicCertified.Atom}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) :
    a ∉ ({b, c, d} : Finset cyclicCertified.Atom) := by
  intro mem
  simp only [Finset.mem_insert, Finset.mem_singleton] at mem
  rcases mem with rfl | rfl | rfl
  · exact hab rfl
  · exact hac rfl
  · exact had rfl

private theorem card_quartet (a b c d : cyclicCertified.Atom)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ({a, b, c, d} : Finset cyclicCertified.Atom).card = 4 := by
  have singleton : ({d} : Finset cyclicCertified.Atom).card = 1 := Finset.card_singleton d
  have pair : ({c, d} : Finset cyclicCertified.Atom).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hcd), singleton]
  have triple : ({b, c, d} : Finset cyclicCertified.Atom).card = 3 := by
    rw [Finset.card_insert_of_notMem (not_mem_pair hbc hbd), pair]
  rw [Finset.card_insert_of_notMem (not_mem_triple hab hac had), triple]

private theorem neighborFinset_A2 : graph.neighborFinset A2 = {A0, A6, A3, A4} := by
  have subset : ({A0, A6, A3, A4} : Finset cyclicCertified.Atom) ⊆ graph.neighborFinset A2 := by
    intro atom member
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl | rfl
    · simpa [mem_neighborFinset] using adj_A2_A0
    · simpa [mem_neighborFinset] using adj_A2_A6
    · simpa [mem_neighborFinset] using adj_A2_A3
    · simpa [mem_neighborFinset] using adj_A2_A4
  have quartet := card_quartet A0 A6 A3 A4 A0_ne_A6 A0_ne_A3 A0_ne_A4 A3_ne_A6.symm
    A6_ne_A4 A3_ne_A4
  have cards : ({A0, A6, A3, A4} : Finset cyclicCertified.Atom).card =
      (graph.neighborFinset A2).card := by rw [quartet, degree_A2]
  symm
  exact Finset.eq_of_subset_of_card_le subset (le_of_eq cards.symm)

private theorem neighborFinset_A0 : graph.neighborFinset A0 = {A5, A1, A2, A4} := by
  have subset : ({A5, A1, A2, A4} : Finset cyclicCertified.Atom) ⊆ graph.neighborFinset A0 := by
    intro atom member
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl | rfl
    · simpa [mem_neighborFinset] using adj_A0_A5
    · simpa [mem_neighborFinset] using adj_A0_A1
    · simpa [mem_neighborFinset] using adj_A0_A2
    · simpa [mem_neighborFinset] using adj_A0_A4
  have quartet := card_quartet A5 A1 A2 A4 A5_ne_A1 A5_ne_A2 A5_ne_A4 A2_ne_A1.symm
    A1_ne_A4 A2_ne_A4
  have cards : ({A5, A1, A2, A4} : Finset cyclicCertified.Atom).card =
      (graph.neighborFinset A0).card := by rw [quartet, degree_A0]
  symm
  exact Finset.eq_of_subset_of_card_le subset (le_of_eq cards.symm)

private theorem arm_neighbor_bound {w : cyclicCertified.Atom} (adjacent : graph.Adj A2 w) :
    graph.atomZ w ≤ 17 := by
  have member : w ∈ graph.neighborFinset A2 := by simpa [mem_neighborFinset] using adjacent
  rw [neighborFinset_A2] at member
  simp only [Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with rfl | rfl | rfl | rfl
  · rw [z_root]; decide
  · rw [z_armHydrogen]; decide
  · rw [z_chlorine]
  · rw [z_closing]; decide

private theorem root_neighbor_bound {w : cyclicCertified.Atom}
    (adjacent : graph.Adj A0 w) (notClosing : w ≠ A4) : graph.atomZ w ≤ 9 := by
  have member : w ∈ graph.neighborFinset A0 := by simpa [mem_neighborFinset] using adjacent
  rw [neighborFinset_A0] at member
  simp only [Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with rfl | rfl | rfl | rfl
  · rw [z_rootHydrogen]; decide
  · rw [z_fluorine]
  · rw [z_arm]; decide
  · exact absurd rfl notClosing

private theorem retained_core_distance : standardClosing.1.node.duplicateRootDistance A0 = 0 := by
  rw [OfficialCIPNode.duplicateRootDistance, retained_history]
  have reversed : ([A4, A2, A0] : List cyclicCertified.Atom).reverse = [A0, A2, A4] := by
    simp [List.reverse_cons, List.reverse_nil]
  rw [reversed, firstIndexOf?_cons_self]
  rfl

/-! ## Constitutional shape of a successful Rule-4a trace -/

private theorem node_label_atomicNumber (node : OfficialCIPNode cyclicCertified.Atom)
    (atom : cyclicCertified.Atom) (current : node.current? = some atom) :
    (ofLex (graph.officialNodeAtomLabel node)).1 = graph.atomZ atom := by
  cases provenance : node.provenance <;>
    simp [officialNodeAtomLabel, current, provenance, rawCIPAtomLabel, ofLex_toLex]

private theorem declarative_head {fuel : Nat}
    {cursor : cyclicCertified.LocalizedRerootCursor (carrierFuel cyclicReferenceInput)}
    {key : OfficialRuleMajorKey cyclicCertified.Atom}
    (derived : cyclicCertified.DeclarativeLocalizedRerootRuleMajorKey fuel cursor key) :
    key.rule1a.head? = some [([], (ofLex
      (graph.officialNodeAtomLabel cursor.occurrence.1.node)).1)] := by
  cases derived with
  | terminal _ _ => simp [officialRuleMajorRootKey]
  | branch _ _ _ _ _ => simp [assemble, officialRuleMajorRootKey]

private theorem sphere_of_head {key : OfficialRuleMajorKey cyclicCertified.Atom} {z : ℕ}
    (head : key.rule1a.head? = some [([], z)]) : key.rule1a.getD 0 [] = [([], z)] := by
  cases rule : key.rule1a with
  | nil => simp [rule] at head
  | cons first rest =>
      simp [rule] at head
      exact head

private theorem stage_derived
    {target : cyclicCertified.LocalizedCIPOccurrence (carrierFuel cyclicReferenceInput)}
    {unit : DetectedOccurrence cyclicCertified.moleculeGraph}
    {targetUnit : cyclicCertified.molecularFrameUnit target.1 = unit.1}
    (compiled : ContextFrameCompilation cyclicReferenceInput target unit targetUnit)
    (slot : Fin 4) :
    cyclicCertified.DeclarativeLocalizedRerootRuleMajorKey
      (2 * (carrierFuel cyclicReferenceInput + 1)) (compiled.frame.cursorAt slot)
      (compiled.stages slot).a.key.constitutional := by
  have built := (compiled.stages slot).a.built
  rw [cyclicReferenceInput.certified.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized] at built
  exact cyclicReferenceInput.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_declarative
    .rule4a (contextOccurrenceRead cyclicReferenceInput target)
    (2 * (carrierFuel cyclicReferenceInput + 1)) (compiled.frame.cursorAt slot)
    (compiled.stages slot).a.key built

private theorem list_key_of_mem {fuel : Nat}
    {cursors : List (cyclicCertified.LocalizedRerootCursor (carrierFuel cyclicReferenceInput))}
    {keys : List (OfficialRuleMajorKey cyclicCertified.Atom)}
    (derived : cyclicCertified.DeclarativeLocalizedRerootRuleMajorKeyList fuel cursors keys)
    {cursor : cyclicCertified.LocalizedRerootCursor (carrierFuel cyclicReferenceInput)}
    (present : cursor ∈ cursors) :
    ∃ key, key ∈ keys ∧
      cyclicCertified.DeclarativeLocalizedRerootRuleMajorKey fuel cursor key := by
  cases derived with
  | nil _ => simp at present
  | cons head tail =>
      simp at present
      rcases present with rfl | later
      · exact ⟨_, List.mem_cons_self, head⟩
      · obtain ⟨key, mem, derivedKey⟩ := list_key_of_mem tail later
        exact ⟨key, List.mem_cons_of_mem _ mem, derivedKey⟩
termination_by cursors.length

private theorem list_cursor_of_key {fuel : Nat}
    {cursors : List (cyclicCertified.LocalizedRerootCursor (carrierFuel cyclicReferenceInput))}
    {keys : List (OfficialRuleMajorKey cyclicCertified.Atom)}
    (derived : cyclicCertified.DeclarativeLocalizedRerootRuleMajorKeyList fuel cursors keys)
    {key : OfficialRuleMajorKey cyclicCertified.Atom} (present : key ∈ keys) :
    ∃ cursor, cursor ∈ cursors ∧
      cyclicCertified.DeclarativeLocalizedRerootRuleMajorKey fuel cursor key := by
  cases derived with
  | nil _ => simp at present
  | cons head tail =>
      simp at present
      rcases present with rfl | later
      · exact ⟨_, List.mem_cons_self, head⟩
      · obtain ⟨cursor, mem, derivedCursor⟩ := list_cursor_of_key tail later
        exact ⟨cursor, List.mem_cons_of_mem _ mem, derivedCursor⟩
termination_by keys.length

private theorem child_key_head {fuel : Nat}
    {cursor : cyclicCertified.LocalizedRerootCursor (carrierFuel cyclicReferenceInput)}
    {key : OfficialRuleMajorKey cyclicCertified.Atom}
    (derived : cyclicCertified.DeclarativeLocalizedRerootRuleMajorKey fuel cursor key)
    {atom : cyclicCertified.Atom} (current : cursor.occurrence.1.node.current? = some atom) :
    key.rule1a.head? = some [([], graph.atomZ atom)] := by
  rw [declarative_head derived, node_label_atomicNumber _ _ current]

private theorem compare_gt_of_heads
    {left right : OfficialRuleMajorKey cyclicCertified.Atom} {leftZ rightZ : ℕ}
    (leftHead : left.rule1a.head? = some [([], leftZ)])
    (rightHead : right.rule1a.head? = some [([], rightZ)]) (higher : rightZ < leftZ) :
    OfficialRuleMajorKey.compare left right = Ordering.gt := by
  have layers := officialRuleMajorKey_compare_rule1a_gt_of_heads_gt leftHead rightHead higher
  rw [compare_eq_rule1a_of_decisive (by rw [layers]; decide), layers]

private theorem le_foldl_max {β : Type*} (measure : β → ℕ) :
    ∀ (children : List β) (accumulator : ℕ),
      accumulator ≤ children.foldl (fun longest child => max longest (measure child)) accumulator
  | [], _ => Nat.le_refl _
  | head :: tail, accumulator => by
      simp only [List.foldl_cons]
      exact Nat.le_trans (Nat.le_max_left accumulator (measure head))
        (le_foldl_max measure tail (max accumulator (measure head)))

private theorem getD_zero_map_range {γ : Type*} {count : ℕ} (positive : 0 < count)
    (f : ℕ → γ) (fallback : γ) : ((List.range count).map f).getD 0 fallback = f 0 := by
  cases count with
  | zero => exact absurd positive (Nat.lt_irrefl 0)
  | succ _ =>
      rw [List.range_succ_eq_map]
      rfl

private theorem merge_first_head (head : OfficialRuleMajorKey cyclicCertified.Atom)
    (tail : List (OfficialRuleMajorKey cyclicCertified.Atom)) {z : ℕ}
    (sphere : head.rule1a.getD 0 [] = [([], z)]) :
    ((mergeChildren (head :: tail) rule1a).getD 0 []).head? = some ([0], z) := by
  have present : head.rule1a ≠ [] := by
    intro empty
    rw [empty] at sphere
    simp at sphere
  have countPos : 0 < childLayerCount (head :: tail) rule1a := by
    unfold childLayerCount
    simp only [List.foldl_cons, Nat.zero_max]
    exact Nat.lt_of_lt_of_le (List.length_pos_iff.mpr present)
      (le_foldl_max (fun child : OfficialRuleMajorKey cyclicCertified.Atom => child.rule1a.length)
        tail head.rule1a.length)
  unfold mergeChildren
  rw [getD_zero_map_range countPos, List.zipIdx_cons, List.flatMap_cons, sphere]
  simp [prefixLayer, List.head?_cons]

private theorem assemble_second_head (node : OfficialCIPNode cyclicCertified.Atom)
    (sorted : List (OfficialRuleMajorKey cyclicCertified.Atom)) {z : ℕ} (nonempty : sorted ≠ [])
    (sphere : (sorted.head nonempty).rule1a.getD 0 [] = [([], z)]) :
    ((assemble (graph.officialRuleMajorRootKey node false) sorted).rule1a.getD 1 []).head? =
      some ([0], z) := by
  cases sorted with
  | nil => exact (nonempty rfl).elim
  | cons head tail =>
      have sphere' : head.rule1a.getD 0 [] = [([], z)] := by simpa using sphere
      simpa [assemble, officialRuleMajorRootKey, List.singleton_append, List.getD_cons_succ] using
        merge_first_head head tail sphere'

private theorem compareNat_self (z : ℕ) : compareNat z z = Ordering.eq := by
  simp [compareNat]

private theorem singleton_layer_eq (z : ℕ) :
    compareSparseLayer compareNat [([], z)] [([], z)] = Ordering.eq := by
  simp [compareSparseLayer, compareSparseEntry, List.compareLex, compareLex, Ordering.byKey,
    flip, compareNat_self]

private theorem cons_of_getD_zero {α : Type*} {l : List α} {a fallback : α}
    (h : l.getD 0 fallback = a) (ne : a ≠ fallback) : ∃ tail, l = a :: tail := by
  cases l with
  | nil => exact absurd h.symm ne
  | cons head tail =>
      simp at h
      exact ⟨tail, by rw [h]⟩

private theorem entry_gt (a b : ℕ) (higher : b < a) :
    compareSparseEntry compareNat ([0], a) ([0], b) = Ordering.gt := by
  have compared : compareNat a b = Ordering.gt := compare_gt_iff_gt.mpr higher
  unfold compareSparseEntry compareLex Ordering.byKey
  simp only [List.compareLex, flip, compared]
  rw [compareNat_self]
  rfl

private theorem compareLex_cons_nil {α : Type*} (cmp : α → α → Ordering) (head : α)
    (tail : List α) : List.compareLex cmp (head :: tail) [] = Ordering.gt := by
  unfold List.compareLex
  rfl

private theorem rule1a_gt_of_second_sphere
    {left right : OfficialRuleMajorKey cyclicCertified.Atom} {z a b : ℕ}
    (left0 : left.rule1a.getD 0 [] = [([], z)])
    (right0 : right.rule1a.getD 0 [] = [([], z)])
    (left1 : (left.rule1a.getD 1 []).head? = some ([0], a))
    (right1 : (right.rule1a.getD 1 []).head? = some ([0], b)) (higher : b < a) :
    compare left right = Ordering.gt := by
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
  have layerGt : compareSparseLayer compareNat leftLayer rightLayer = Ordering.gt := by
    rw [leftLayerEq, rightLayerEq]
    simp [compareSparseLayer, List.compareLex, entry_gt a b higher]
  have layersGt : compareSparseLayers compareNat left.rule1a right.rule1a = Ordering.gt := by
    rw [leftEq, rightEq, leftTailEq, rightTailEq]
    simp [compareSparseLayers, List.compareLex, singleton_layer_eq z, layerGt]
  rw [compare_eq_rule1a_of_decisive (by rw [layersGt]; decide), layersGt]

private theorem compare_gt_of_extra_sphere
    {left right : OfficialRuleMajorKey cyclicCertified.Atom} {z : ℕ}
    (left0 : left.rule1a.getD 0 [] = [([], z)])
    (rightRule : right.rule1a = [[([], z)]])
    {second : ℕ} (left1 : (left.rule1a.getD 1 []).head? = some ([0], second)) :
    compare left right = Ordering.gt := by
  obtain ⟨leftTail, leftEq⟩ := cons_of_getD_zero left0 (by simp)
  have leftMore : ∃ layer rest, leftTail = layer :: rest := by
    cases leftTail with
    | nil => simp [leftEq] at left1
    | cons layer rest => exact ⟨layer, rest, rfl⟩
  obtain ⟨_layer, _rest, leftTailEq⟩ := leftMore
  have layersGt : compareSparseLayers compareNat left.rule1a right.rule1a = Ordering.gt := by
    rw [leftEq, leftTailEq, rightRule]
    unfold compareSparseLayers
    simp only [List.compareLex, singleton_layer_eq z]
  rw [compare_eq_rule1a_of_decisive (by rw [layersGt]; decide), layersGt]

/-! ## Retained frame: real parent and core duplicate -/

private theorem retained_center_atom : standardClosingCompilation.center.1 = A4 := by
  rw [standardClosing_frame_stage_compound.2.1, closingRecognizedNonroot.2.1]

private theorem retained_realNode :
    cyclicCertified.RealTetrahedralCenterNode standardClosing.1.node
      standardClosingCompilation.center := by
  refine ⟨standardClosing_provenance, ?_⟩
  rw [standardClosing_current, retained_center_atom]

private theorem retained_frame :
    cyclicCertified.localizedOccurrenceFourLigandFrame? standardClosing =
      some standardClosingCompilation.frame := by
  rw [← cyclicCertified.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?
    standardClosing]
  exact standardClosingCompilation.frameComputed

private theorem cursor_present
    {target : cyclicCertified.LocalizedCIPOccurrence (carrierFuel cyclicReferenceInput)}
    {unit : DetectedOccurrence cyclicCertified.moleculeGraph}
    {targetUnit : cyclicCertified.molecularFrameUnit target.1 = unit.1}
    (compiled : ContextFrameCompilation cyclicReferenceInput target unit targetUnit)
    (slot : Fin 4) : compiled.frame.cursorAt slot ∈ compiled.frame.cursors := by
  rw [LocalizedOccurrenceFourLigandFrame.cursorAt]
  exact List.get_mem compiled.frame.cursors
    (Fin.cast compiled.frame.length_eq.symm slot)

def frameLigand
    {target : cyclicCertified.LocalizedCIPOccurrence (carrierFuel cyclicReferenceInput)}
    {unit : DetectedOccurrence cyclicCertified.moleculeGraph}
    {targetUnit : cyclicCertified.molecularFrameUnit target.1 = unit.1}
    (compiled : ContextFrameCompilation cyclicReferenceInput target unit targetUnit)
    (slot : Fin 4) : cyclicCertified.Atom :=
  cyclicCertified.detectedMultiCenterMolecule.ligandAtomAt compiled.center
    (compiled.detectedLigandPermutation slot)

private theorem frame_current
    {target : cyclicCertified.LocalizedCIPOccurrence (carrierFuel cyclicReferenceInput)}
    {unit : DetectedOccurrence cyclicCertified.moleculeGraph}
    {targetUnit : cyclicCertified.molecularFrameUnit target.1 = unit.1}
    (compiled : ContextFrameCompilation cyclicReferenceInput target unit targetUnit)
    (slot : Fin 4) :
    (compiled.frame.cursorAt slot).occurrence.1.node.current? = some (frameLigand compiled slot) := by
  simpa [frameLigand] using compiled.ligandAt slot

private theorem slot_of_ligand
    {target : cyclicCertified.LocalizedCIPOccurrence (carrierFuel cyclicReferenceInput)}
    {unit : DetectedOccurrence cyclicCertified.moleculeGraph}
    {targetUnit : cyclicCertified.molecularFrameUnit target.1 = unit.1}
    (compiled : ContextFrameCompilation cyclicReferenceInput target unit targetUnit)
    {ligand : cyclicCertified.Atom}
    (adjacent : cyclicCertified.detectedMultiCenterMolecule.mol.Adj compiled.center.1 ligand) :
    ∃ slot : Fin 4, frameLigand compiled slot = ligand := by
  obtain ⟨index, atomEq⟩ :=
    cyclicCertified.detectedMultiCenterMolecule.ligandAtomAt_surjective compiled.center ligand
      adjacent
  refine ⟨compiled.detectedLigandPermutation.symm index, ?_⟩
  simp [frameLigand, Equiv.apply_symm_apply, atomEq]

private theorem retained_mol_adj {ligand : cyclicCertified.Atom} (adjacent : graph.Adj A4 ligand) :
    cyclicCertified.detectedMultiCenterMolecule.mol.Adj standardClosingCompilation.center.1
      ligand := by
  have molEq : cyclicCertified.detectedMultiCenterMolecule.mol = graph := rfl
  rw [molEq, retained_center_atom]
  exact adjacent

def retained_slot_cut (slot : Fin 4) :=
  cyclicCertified.executableChild_retainedContextArmFaithful_of_carrierFuel input_simpleBonded
    ⟨standardClosing, none⟩ (standardClosingCompilation.frame.cursorAt slot)
    (standardClosingCompilation.childAt slot) (standardClosingCompilation.stages slot).a

private def classify_retained (slot : Fin 4) :=
  cyclicCertified.simpleBond_fourLigandFrame_cursor_classified input_simpleBonded standardClosing
    standardClosingCompilation.center retained_realNode standardClosingCompilation.frame
    retained_frame (standardClosingCompilation.frame.cursorAt slot)
    (cursor_present standardClosingCompilation slot)

private structure RetainedParent (slot : Fin 4) : Prop where
  current : (standardClosingCompilation.frame.cursorAt slot).occurrence.1.node.current? = some A2
  history : (standardClosingCompilation.frame.cursorAt slot).occurrence.1.node.history = [A2, A0]
  real : (standardClosingCompilation.frame.cursorAt slot).occurrence.1.node.provenance =
    OfficialCIPNodeProvenance.realAtom
  active : (standardClosingCompilation.frame.cursorAt slot).occurrence.1.node.ActiveSimple
  sameArm : (standardClosingCompilation.frame.cursorAt slot).occurrence.1.node.history =
    standardArm.1.node.history
  notFabricated : (standardClosingCompilation.frame.cursorAt slot).occurrence.1.node ≠
    standardClosing.1.node.extend A2 0
  previous : (standardClosingCompilation.frame.cursorAt slot).previous? = some standardClosing

private theorem retained_parent_shape : ∃ slot : Fin 4, RetainedParent slot := by
  obtain ⟨slot, ligandEq⟩ := slot_of_ligand standardClosingCompilation
    (retained_mol_adj adj_A4_A2)
  have current := frame_current standardClosingCompilation slot
  rw [ligandEq] at current
  obtain ⟨w, currentW, _, classified⟩ := classify_retained slot
  have wEq : w = A2 := Option.some.inj (currentW.symm.trans current)
  rcases classified with ⟨certificate, occEq, active, parentEq, _visited⟩ | ⟨_, notParent, _, _⟩
  · have historyEq := certificate.history_eq
    have currentTarget : certificate.current = A4 :=
      Option.some.inj (certificate.current_eq.symm.trans standardClosing_current)
    have parentHistory : certificate.parent.1.node.history = [A2, A0] := by
      rw [retained_history, currentTarget] at historyEq
      simpa [List.cons.injEq] using historyEq.symm
    have nodeHistory :
        (standardClosingCompilation.frame.cursorAt slot).occurrence.1.node.history = [A2, A0] := by
      rw [show (standardClosingCompilation.frame.cursorAt slot).occurrence =
        certificate.parent from occEq]
      exact parentHistory
    have realCursor :
        (standardClosingCompilation.frame.cursorAt slot).occurrence.1.node.provenance =
          OfficialCIPNodeProvenance.realAtom := by
      simpa [occEq] using active.1
    have activeCursor :
        (standardClosingCompilation.frame.cursorAt slot).occurrence.1.node.ActiveSimple := by
      simpa [occEq] using active
    refine ⟨slot, current, nodeHistory, realCursor, activeCursor, ?_, ?_, ?_⟩
    · rw [nodeHistory, arm_history_std]
    · intro equal
      have histories := congrArg OfficialCIPNode.history equal
      rw [nodeHistory, fabricated_parent_history] at histories
      simp at histories
    · simpa [occEq] using
        cyclicCertified.localizedOccurrenceFourLigandFrame_cursor_previous standardClosing
          standardClosingCompilation.frame retained_frame _
          (cursor_present standardClosingCompilation slot)
  · exact False.elim (notParent (by rw [wEq]; exact retained_parentAtom))

private structure RetainedCore (slot : Fin 4) : Prop where
  current : (standardClosingCompilation.frame.cursorAt slot).occurrence.1.node.current? = some A0
  nodeEq : (standardClosingCompilation.frame.cursorAt slot).occurrence.1.node =
    standardClosing.1.node.extend A0 0
  sameDuplicate : (standardClosingCompilation.frame.cursorAt slot).occurrence.1.node =
    standardDuplicate.1.node
  ring : (standardClosingCompilation.frame.cursorAt slot).occurrence.1.node.provenance =
    OfficialCIPNodeProvenance.ringDuplicate 0
  distance : (standardClosingCompilation.frame.cursorAt slot).occurrence.1.node.rule1bRootDistance =
    0
  leaf : (standardClosingCompilation.frame.cursorAt slot).occurrence.1.node.isDuplicateLeaf = true
  noOfficial : cyclicCertified.executableOfficialCIPChildren
    (standardClosingCompilation.frame.cursorAt slot).occurrence.1.node = []
  noReroot : cyclicCertified.executableLocalizedRerootChildren
    (standardClosingCompilation.frame.cursorAt slot) = []

private theorem retained_core_shape : ∃ slot : Fin 4, RetainedCore slot := by
  obtain ⟨slot, ligandEq⟩ := slot_of_ligand standardClosingCompilation
    (retained_mol_adj adj_A4_A0)
  have current := frame_current standardClosingCompilation slot
  rw [ligandEq] at current
  obtain ⟨w, currentW, _, classified⟩ := classify_retained slot
  have wEq : w = A0 := Option.some.inj (currentW.symm.trans current)
  rcases classified with ⟨_, _, _, parentEq, _⟩ | ⟨nodeEq, notParent, visitedFacts, _freshFacts⟩
  · have parentA0 : standardClosing.1.node.parent? = some A0 := by
      rw [← wEq]
      exact parentEq
    exact False.elim (A2_ne_A0 (Option.some.inj (retained_parentAtom.symm.trans parentA0)))
  · have visited := visitedFacts (by rw [wEq]; exact retained_visitedCore)
    have nodeEq' :
        (standardClosingCompilation.frame.cursorAt slot).occurrence.1.node =
          standardClosing.1.node.extend A0 0 := by simpa [wEq] using nodeEq
    have ring : (standardClosingCompilation.frame.cursorAt slot).occurrence.1.node.provenance =
        OfficialCIPNodeProvenance.ringDuplicate 0 := by
      rw [visited.1, wEq, retained_core_distance]
    refine ⟨slot, current, nodeEq', by rw [nodeEq', duplicate_node_std], ring, ?_,
      by simpa [wEq] using visited.2.1, by simpa [wEq] using visited.2.2, ?_⟩
    · simp [OfficialCIPNode.rule1bRootDistance, ring]
    · exact LocalizedRetainedCursorCutCover.ringCursor_executableChildren_eq_nil cyclicCertified
        (standardClosingCompilation.frame.cursorAt slot) ring

private theorem retained_notLeaf (slot : Fin 4) (shape : RetainedParent slot) :
    (standardClosingCompilation.frame.cursorAt slot).occurrence.1.node.isDuplicateLeaf = false :=
  cyclicCertified.isDuplicateLeaf_eq_false_of_provenance_real _ shape.real

private theorem chlorine_intended (slot : Fin 4) (shape : RetainedParent slot) :
    ∃ chlorineFrame, chlorineFrame ∈ cyclicCertified.intendedLocalizedRerootChildFrames
        (standardClosingCompilation.frame.cursorAt slot) ∧
      chlorineFrame.node.current? = some A3 := by
  let cursor := standardClosingCompilation.frame.cursorAt slot
  have notParentA3 : cursor.occurrence.1.node.parent? ≠ some A3 := by
    rw [OfficialCIPNode.parent?, shape.history]
    intro parentEq
    exact A0_ne_A3 (Option.some.inj parentEq)
  obtain ⟨chlorineFrame, _slot, _address, childRoot, current, _node, member, outward⟩ :=
    cyclicCertified.realCenter_outwardChildFrame_of_notParent fuel_enough cursor.occurrence
      shape.current adj_A2_A3 notParentA3 shape.real
  have addressNe : chlorineFrame.address ≠ standardClosing.1.address := by
    intro addressEq
    have childDerived := (cyclicCertified.mem_localizedOccurrences_iff _ chlorineFrame).mp member
    have targetDerived :=
      (cyclicCertified.mem_localizedOccurrences_iff _ standardClosing.1).mp standardClosing.2
    have cursorRoot := cyclicCertified.localizedOccurrenceFourLigandFrame_cursor_root
      standardClosing standardClosingCompilation.frame retained_frame cursor
      (cursor_present standardClosingCompilation slot)
    have sameRoot : chlorineFrame.root = standardClosing.1.root := childRoot.trans cursorRoot
    have frameEq := cyclicCertified.declarativeLocalizedOccurrence_functional_at_root_address
      childDerived targetDerived sameRoot addressEq
    have currents := congrArg
      (fun frame : cyclicCertified.LocalizedCIPOccurrenceFrame => frame.node.current?) frameEq
    exact A3_ne_A4 (Option.some.inj ((current.symm.trans currents).trans standardClosing_current))
  have neighbor : chlorineFrame ∈ cyclicCertified.localizedRerootNeighborFrames
      (fuel := carrierFuel cyclicReferenceInput) cursor.occurrence.1 :=
    List.mem_append_right _ outward
  have intended : chlorineFrame ∈ cyclicCertified.intendedLocalizedRerootChildFrames cursor := by
    unfold intendedLocalizedRerootChildFrames
    have notDup : cursor.occurrence.1.node.isDuplicateLeaf ≠ true := by
      rw [retained_notLeaf slot shape]
      exact Bool.false_ne_true
    rw [if_neg notDup, shape.previous, List.mem_filter, bne_iff_ne]
    exact ⟨neighbor, addressNe⟩
  exact ⟨chlorineFrame, intended, current⟩

private theorem retained_parent_second (slot : Fin 4) (shape : RetainedParent slot) :
    ((standardClosingCompilation.stages slot).a.key.constitutional.rule1a.getD 1 []).head? =
      some ([0], graph.atomZ A3) := by
  let cursor := standardClosingCompilation.frame.cursorAt slot
  have derived := stage_derived standardClosingCompilation slot
  generalize hkey : (standardClosingCompilation.stages slot).a.key.constitutional = key at derived
  obtain ⟨chlorineFrame, chlorineIntended, chlorineCurrent⟩ := chlorine_intended slot shape
  cases derived with
  | terminal childProof empty =>
      exfalso
      have mapEq := childProof.1
      simp [cyclicReferenceInput] at mapEq
      rw [empty, List.map_nil] at mapEq
      rw [← mapEq] at chlorineIntended
      simp at chlorineIntended
  | branch childProof nonempty childDerivations ranking descending =>
      rename_i children childKeys sorted
      have frameEq := childProof.1
      simp [cyclicReferenceInput] at frameEq
      have keyBound : ∀ childKey, childKey ∈ childKeys →
          ∃ z, childKey.rule1a.head? = some [([], z)] ∧ z ≤ 17 := by
        intro childKey childKeyMem
        obtain ⟨child, childMem, childDerived⟩ := list_cursor_of_key childDerivations childKeyMem
        have frameMem : child.occurrence.1 ∈
            cyclicCertified.intendedLocalizedRerootChildFrames cursor := by
          rw [← frameEq]
          exact List.mem_map.mpr ⟨child, childMem, rfl⟩
        have notDup : cursor.occurrence.1.node.isDuplicateLeaf ≠ true := by
          rw [retained_notLeaf slot shape]
          exact Bool.false_ne_true
        have filtered : child.occurrence.1 ∈ cyclicCertified.localizedRerootNeighborFrames
              (fuel := carrierFuel cyclicReferenceInput) cursor.occurrence.1 ∧
            child.occurrence.1.address ≠ standardClosing.1.address := by
          unfold intendedLocalizedRerootChildFrames at frameMem
          rw [if_neg notDup, shape.previous, List.mem_filter, bne_iff_ne] at frameMem
          exact frameMem
        rw [localizedRerootNeighborFrames, List.mem_append] at filtered
        rcases filtered.1 with parentMem | outwardMem
        · have addressNe : cursor.occurrence.1.address ≠ [] := by
            intro nil
            have hlen := cyclicCertified.carrierOccurrence_history_length_eq_address_succ
              cursor.occurrence
            rw [shape.history, nil] at hlen
            simp at hlen
          let cert := cyclicCertified.localizedParentFrameHistory cursor.occurrence addressNe
          have singleton := cert.carrierParentFrames_eq_singleton cyclicCertified
          have frameId : child.occurrence.1 = cert.parent.1 := by
            rw [singleton] at parentMem
            simpa using parentMem
          have parentHist : cert.parent.1.node.history = [A0] := by
            have split := cert.history_eq
            have cur : cert.current = A2 :=
              Option.some.inj (cert.current_eq.symm.trans shape.current)
            rw [shape.history, cur] at split
            simpa [List.cons.injEq] using split.symm
          have derivedParent :=
            (cyclicCertified.mem_localizedOccurrences_iff _ cert.parent.1).mp cert.parent.2
          have headCurrent :=
            cyclicCertified.declarativeLocalizedOccurrence_node_history_head_eq_current
              derivedParent
          have parentCurrent : cert.parent.1.node.current? = some A0 := by
            rw [parentHist] at headCurrent
            simpa using headCurrent.symm
          have currentA0 : child.occurrence.1.node.current? = some A0 := by
            rw [frameId]
            exact parentCurrent
          refine ⟨graph.atomZ A0, child_key_head childDerived currentA0, ?_⟩
          rw [z_root]
          decide
        · obtain ⟨w, _, _, currentW, _, _, _, _, adjW⟩ :=
            cyclicCertified.simpleBond_outwardFrame_extend_zero input_simpleBonded
              cursor.occurrence shape.current shape.real child.occurrence.1 outwardMem
          exact ⟨graph.atomZ w, child_key_head childDerived currentW, arm_neighbor_bound adjW⟩
      have memIntended := chlorineIntended
      rw [← frameEq] at memIntended
      obtain ⟨maxChild, maxChildMem, maxChildEq⟩ := List.mem_map.mp memIntended
      obtain ⟨maxKey, maxKeyMem, maxDerived⟩ := list_key_of_mem childDerivations maxChildMem
      have maxCurrent : maxChild.occurrence.1.node.current? = some A3 := by
        rw [maxChildEq]
        exact chlorineCurrent
      have maxHead := child_key_head maxDerived maxCurrent
      cases sorted with
      | nil => exact absurd (ranking.mem_iff.mpr maxKeyMem) (by simp)
      | cons headKey tail =>
          obtain ⟨z, headHead, zLe⟩ := keyBound headKey (ranking.mem_iff.mp List.mem_cons_self)
          have zEq : z = graph.atomZ A3 := by
            by_contra different
            have zlt : z < graph.atomZ A3 := by
              rw [z_chlorine] at different ⊢
              exact Nat.lt_of_le_of_ne zLe different
            letI : Std.TransCmp (@compare cyclicCertified.Atom) := compare_transCmp
            have childGt := compare_gt_of_heads maxHead headHead zlt
            have headLt : compare headKey maxKey = Ordering.lt := by
              rw [← Std.OrientedCmp.gt_iff_lt]
              exact childGt
            have maxSorted : maxKey ∈ headKey :: tail := ranking.mem_iff.mpr maxKeyMem
            rcases List.mem_cons.mp maxSorted with same | later
            · rw [← same] at headHead
              have heads := headHead.symm.trans maxHead
              injection heads with layerEq
              injection layerEq with entryEq
              injection entryEq with _addrEq zSame
              exact different zSame
            · exact (List.pairwise_cons.mp descending).1 maxKey later headLt
          have sphere : headKey.rule1a.getD 0 [] = [([], graph.atomZ A3)] := by
            rw [sphere_of_head headHead, zEq]
          exact assemble_second_head cursor.occurrence.1.node (headKey :: tail) (by simp)
            (by simpa [List.head_cons] using sphere)

private theorem retained_parent_first (slot : Fin 4) (shape : RetainedParent slot) :
    (standardClosingCompilation.stages slot).a.key.constitutional.rule1a.getD 0 [] =
      [([], graph.atomZ A2)] := by
  have head := declarative_head (stage_derived standardClosingCompilation slot)
  rw [node_label_atomicNumber _ _ shape.current, z_arm] at head
  simpa [z_arm] using sphere_of_head head

private theorem retained_core_rule (slot : Fin 4) (shape : RetainedCore slot) :
    (standardClosingCompilation.stages slot).a.key.constitutional.rule1a = [[([], graph.atomZ A0)]] := by
  have derived := stage_derived standardClosingCompilation slot
  generalize hkey : (standardClosingCompilation.stages slot).a.key.constitutional = key at derived
  cases derived with
  | branch childProof nonempty _ _ _ =>
      exfalso
      have mapEq := childProof.1
      simp [cyclicReferenceInput] at mapEq
      have intendedNil : cyclicCertified.intendedLocalizedRerootChildFrames
          (standardClosingCompilation.frame.cursorAt slot) = [] := by
        simp [intendedLocalizedRerootChildFrames, shape.leaf]
      rw [intendedNil] at mapEq
      exact nonempty (List.map_eq_nil_iff.mp mapEq)
  | terminal _ _ =>
      simp [cyclicReferenceInput, graph]
      rw [node_label_atomicNumber _ _ shape.current, z_root]

private theorem retained_order (parentSlot coreSlot : Fin 4)
    (parentShape : RetainedParent parentSlot) (coreShape : RetainedCore coreSlot) :
    OfficialRuleMajorKey.compare
        (standardClosingCompilation.stages parentSlot).a.key.constitutional
        (standardClosingCompilation.stages coreSlot).a.key.constitutional = Ordering.gt := by
  apply compare_gt_of_extra_sphere
  · simpa [z_arm, z_root] using retained_parent_first parentSlot parentShape
  · simpa [z_root] using retained_core_rule coreSlot coreShape
  · simpa [z_chlorine] using retained_parent_second parentSlot parentShape

structure RetainedLigandKeyFacts (parentSlot coreSlot : Fin 4) : Prop where
  parentCurrent :
    (standardClosingCompilation.frame.cursorAt parentSlot).occurrence.1.node.current? = some A2
  parentHistory :
    (standardClosingCompilation.frame.cursorAt parentSlot).occurrence.1.node.history = [A2, A0]
  parentReal : (standardClosingCompilation.frame.cursorAt parentSlot).occurrence.1.node.provenance =
    OfficialCIPNodeProvenance.realAtom
  parentActive :
    (standardClosingCompilation.frame.cursorAt parentSlot).occurrence.1.node.ActiveSimple
  parentSameArm :
    (standardClosingCompilation.frame.cursorAt parentSlot).occurrence.1.node.history =
      standardArm.1.node.history
  parentNotFabricated :
    (standardClosingCompilation.frame.cursorAt parentSlot).occurrence.1.node ≠
      standardClosing.1.node.extend A2 0
  parentPrevious :
    (standardClosingCompilation.frame.cursorAt parentSlot).previous? = some standardClosing
  coreCurrent :
    (standardClosingCompilation.frame.cursorAt coreSlot).occurrence.1.node.current? = some A0
  coreNode : (standardClosingCompilation.frame.cursorAt coreSlot).occurrence.1.node =
    standardClosing.1.node.extend A0 0
  coreSameDuplicate : (standardClosingCompilation.frame.cursorAt coreSlot).occurrence.1.node =
    standardDuplicate.1.node
  coreRing : (standardClosingCompilation.frame.cursorAt coreSlot).occurrence.1.node.provenance =
    OfficialCIPNodeProvenance.ringDuplicate 0
  coreDistance :
    (standardClosingCompilation.frame.cursorAt coreSlot).occurrence.1.node.rule1bRootDistance = 0
  coreLeaf :
    (standardClosingCompilation.frame.cursorAt coreSlot).occurrence.1.node.isDuplicateLeaf = true
  coreNoOfficial : cyclicCertified.executableOfficialCIPChildren
    (standardClosingCompilation.frame.cursorAt coreSlot).occurrence.1.node = []
  coreNoReroot : cyclicCertified.executableLocalizedRerootChildren
    (standardClosingCompilation.frame.cursorAt coreSlot) = []
  parentSource : (standardClosingCompilation.stages parentSlot).a.tree.source =
    standardClosingCompilation.frame.cursorAt parentSlot
  parentBuilt : cyclicReferenceInput.certified.buildRuleMajorCumulativeWithRead?
    LocalizedCumulativeRule45Stage.rule4a
    (contextOccurrenceRead cyclicReferenceInput standardClosing)
    (2 * (carrierFuel cyclicReferenceInput + 1))
    (standardClosingCompilation.frame.cursorAt parentSlot) =
      some (standardClosingCompilation.stages parentSlot).a.key
  coreSource : (standardClosingCompilation.stages coreSlot).a.tree.source =
    standardClosingCompilation.frame.cursorAt coreSlot
  coreBuilt : cyclicReferenceInput.certified.buildRuleMajorCumulativeWithRead?
    LocalizedCumulativeRule45Stage.rule4a
    (contextOccurrenceRead cyclicReferenceInput standardClosing)
    (2 * (carrierFuel cyclicReferenceInput + 1))
    (standardClosingCompilation.frame.cursorAt coreSlot) =
      some (standardClosingCompilation.stages coreSlot).a.key
  chlorineBond : graph.Adj A2 A3
  parentAtomic : graph.atomZ A2 = 6
  coreAtomic : graph.atomZ A0 = 6
  chlorineAtomic : graph.atomZ A3 = 17
  parentFirst :
    (standardClosingCompilation.stages parentSlot).a.key.constitutional.rule1a.getD 0 [] = [([], 6)]
  parentSecond :
    ((standardClosingCompilation.stages parentSlot).a.key.constitutional.rule1a.getD 1 []).head? =
      some ([0], 17)
  coreRule :
    (standardClosingCompilation.stages coreSlot).a.key.constitutional.rule1a = [[([], 6)]]
  comparison : OfficialRuleMajorKey.compare
    (standardClosingCompilation.stages parentSlot).a.key.constitutional
    (standardClosingCompilation.stages coreSlot).a.key.constitutional = Ordering.gt

theorem retained_ligand_keys_rank_parent_above_core :
    ∃ parentSlot coreSlot : Fin 4, RetainedLigandKeyFacts parentSlot coreSlot := by
  obtain ⟨parentSlot, parentShape⟩ := retained_parent_shape
  obtain ⟨coreSlot, coreShape⟩ := retained_core_shape
  exact ⟨parentSlot, coreSlot, {
    parentCurrent := parentShape.current
    parentHistory := parentShape.history
    parentReal := parentShape.real
    parentActive := parentShape.active
    parentSameArm := parentShape.sameArm
    parentNotFabricated := parentShape.notFabricated
    parentPrevious := parentShape.previous
    coreCurrent := coreShape.current
    coreNode := coreShape.nodeEq
    coreSameDuplicate := coreShape.sameDuplicate
    coreRing := coreShape.ring
    coreDistance := coreShape.distance
    coreLeaf := coreShape.leaf
    coreNoOfficial := coreShape.noOfficial
    coreNoReroot := coreShape.noReroot
    parentSource := (standardClosingCompilation.stages parentSlot).a.sourceEq
    parentBuilt := (standardClosingCompilation.stages parentSlot).a.built
    coreSource := (standardClosingCompilation.stages coreSlot).a.sourceEq
    coreBuilt := (standardClosingCompilation.stages coreSlot).a.built
    chlorineBond := adj_A2_A3
    parentAtomic := z_arm
    coreAtomic := z_root
    chlorineAtomic := z_chlorine
    parentFirst := by simpa [z_arm] using retained_parent_first parentSlot parentShape
    parentSecond := by simpa [z_chlorine] using retained_parent_second parentSlot parentShape
    coreRule := by simpa [z_root] using retained_core_rule coreSlot coreShape
    comparison := retained_order parentSlot coreSlot parentShape coreShape
  }⟩

/-! ## Fresh own-root at atom 4 -/

private theorem fresh_head : freshTarget.1.node.history.head? = some A4 := by
  simp [fresh_root_history]

private theorem fresh_last : freshTarget.1.node.history.getLast? = some freshTarget.1.root := by
  simp [fresh_root_history, fresh_rootAtom]

private theorem fresh_unit_atom : (cyclicCertified.molecularFrameUnit freshTarget.1).atom = A4 :=
  cyclicCertified.molecularFrameUnit_atom_eq_current freshTarget.1 fresh_head fresh_last

theorem fresh_detected : IsDetectedCenter graph
    (cyclicCertified.molecularFrameUnit freshTarget.1).atom := by
  rw [fresh_unit_atom, IsDetectedCenter]
  simpa [graph, cyclicReferenceInput] using degreeFourCentersOnCycle.2.2.1

def freshDetectedUnit : DetectedOccurrence graph :=
  ⟨cyclicCertified.molecularFrameUnit freshTarget.1, fresh_detected⟩

theorem fresh_unit_target :
    cyclicCertified.molecularFrameUnit freshTarget.1 = freshDetectedUnit.1 :=
  rfl

def freshCompilation : ContextFrameCompilation cyclicReferenceInput freshTarget
    freshDetectedUnit fresh_unit_target :=
  cyclicContextFrameCompilation cyclicReferenceInput input_simpleBonded freshTarget fresh_real
    freshDetectedUnit fresh_unit_target

private theorem fresh_center_atom : freshCompilation.center.1 = A4 := by
  rw [freshCompilation.centerEq, freshDetectedUnit]
  exact fresh_unit_atom

private theorem fresh_frame :
    cyclicCertified.localizedOccurrenceFourLigandFrame? freshTarget = some freshCompilation.frame := by
  rw [← cyclicCertified.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?
    freshTarget]
  exact freshCompilation.frameComputed

def fresh_slot_cut (slot : Fin 4) :=
  cyclicCertified.executableChild_retainedContextArmFaithful_of_carrierFuel input_simpleBonded
    ⟨freshTarget, none⟩ (freshCompilation.frame.cursorAt slot)
    (freshCompilation.childAt slot) (freshCompilation.stages slot).a

private structure FreshSlot (slot : Fin 4) : Prop where
  nodeEq : (freshCompilation.frame.cursorAt slot).occurrence.1.node =
    (OfficialCIPNode.root A4).extend (frameLigand freshCompilation slot) 0
  history : (freshCompilation.frame.cursorAt slot).occurrence.1.node.history =
    [frameLigand freshCompilation slot, A4]
  parent : (freshCompilation.frame.cursorAt slot).occurrence.1.node.parent? = some A4
  real : (freshCompilation.frame.cursorAt slot).occurrence.1.node.provenance =
    OfficialCIPNodeProvenance.realAtom
  distance : (freshCompilation.frame.cursorAt slot).occurrence.1.node.rule1bRootDistance = 1
  duplicateFree : (freshCompilation.frame.cursorAt slot).occurrence.1.node.isDuplicateLeaf = false
  previous : (freshCompilation.frame.cursorAt slot).previous? = some freshTarget
  sameRoot : freshTarget.1.root =
    (freshCompilation.frame.cursorAt slot).occurrence.1.root
  addressDrop : freshTarget.1.address =
    (freshCompilation.frame.cursorAt slot).occurrence.1.address.dropLast
  addressStep : freshTarget.1.address.length + 1 =
    (freshCompilation.frame.cursorAt slot).occurrence.1.address.length

private theorem freshSlotShape (slot : Fin 4) : FreshSlot slot := by
  have previous := cyclicCertified.localizedOccurrenceFourLigandFrame_cursor_previous
    freshTarget freshCompilation.frame fresh_frame _ (cursor_present freshCompilation slot)
  have sameRoot := cyclicCertified.localizedOccurrenceFourLigandFrame_cursor_root
    freshTarget freshCompilation.frame fresh_frame _ (cursor_present freshCompilation slot)
  have neighborMem := cyclicCertified.localizedOccurrenceFourLigandFrame_cursor_mem_neighborFrames
    freshTarget freshCompilation.frame fresh_frame _ (cursor_present freshCompilation slot)
  have outwardEq := cyclicCertified.localizedRerootNeighborFrames_eq_outwardChildFrames_of_address_nil
    freshTarget fresh_address
  have outwardMem : (freshCompilation.frame.cursorAt slot).occurrence.1 ∈
      cyclicCertified.localizedCarrierOutwardChildFrames
        (fuel := carrierFuel cyclicReferenceInput) freshTarget.1 := by
    rw [← outwardEq]
    exact neighborMem
  have currentRoot : freshTarget.1.node.current? = some A4 := by
    simp [fresh_node, OfficialCIPNode.root]
  obtain ⟨w, childSlot, nodeEq, current, _rootEq, addressEq, _zip, _notParent, graphAdjacent⟩ :=
    cyclicCertified.simpleBond_outwardFrame_extend_zero input_simpleBonded freshTarget
      currentRoot fresh_real _ outwardMem
  have wEq : w = frameLigand freshCompilation slot :=
    Option.some.inj (current.symm.trans (frame_current freshCompilation slot))
  have nodeEq' : (freshCompilation.frame.cursorAt slot).occurrence.1.node =
      (OfficialCIPNode.root A4).extend w 0 := by
    rw [nodeEq, fresh_node]
  have parent : (freshCompilation.frame.cursorAt slot).occurrence.1.node.parent? = some A4 := by
    rw [nodeEq']
    simp [OfficialCIPNode.extend, OfficialCIPNode.root, OfficialCIPNode.parent?]
  have notHistory : w ∉ (OfficialCIPNode.root A4).history := by
    simp only [OfficialCIPNode.root, List.mem_singleton]
    intro equal
    have loop : graph.Adj w w := by simpa [equal] using graphAdjacent
    simp [MoleculeGraph.Adj, graph.bond_self] at loop
  have real : (freshCompilation.frame.cursorAt slot).occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom := by
    rw [nodeEq', OfficialCIPNode.extend, OfficialCIPNode.childProvenance]
    simp only [if_neg notHistory, if_true]
  have history : (freshCompilation.frame.cursorAt slot).occurrence.1.node.history = [w, A4] := by
    rw [nodeEq']
    simp [extend_history, OfficialCIPNode.root]
  have addressNil : (freshCompilation.frame.cursorAt slot).occurrence.1.address = [childSlot] := by
    simpa [fresh_address] using addressEq
  refine {
    nodeEq := by rw [← wEq]; exact nodeEq'
    history := by rw [← wEq]; exact history
    parent := parent
    real := real
    distance := by
      rw [OfficialCIPNode.rule1bRootDistance, real, OfficialCIPNode.depth, history]
      rfl
    duplicateFree := cyclicCertified.isDuplicateLeaf_eq_false_of_provenance_real _ real
    previous := previous
    sameRoot := sameRoot.symm
    addressDrop := by simp [addressNil, fresh_address]
    addressStep := by simp [addressNil, fresh_address] }

private theorem fresh_outward_perm (slot : Fin 4) (shape : FreshSlot slot) :
    (cyclicCertified.intendedLocalizedRerootChildFrames
      (freshCompilation.frame.cursorAt slot)).Perm
      (cyclicCertified.localizedCarrierOutwardChildFrames
        (fuel := carrierFuel cyclicReferenceInput)
        (freshCompilation.frame.cursorAt slot).occurrence.1) :=
  cyclicCertified.intendedLocalizedRerootChildFrames_perm_outward
    (freshCompilation.frame.cursorAt slot) freshTarget shape.previous shape.sameRoot
    shape.addressDrop shape.addressStep shape.duplicateFree

private theorem fresh_mol_adj {ligand : cyclicCertified.Atom} (adjacent : graph.Adj A4 ligand) :
    cyclicCertified.detectedMultiCenterMolecule.mol.Adj freshCompilation.center.1 ligand := by
  have molEq : cyclicCertified.detectedMultiCenterMolecule.mol = graph := rfl
  rw [molEq, fresh_center_atom]
  exact adjacent

private theorem fresh_second (slot : Fin 4) (ligand maxAtom : cyclicCertified.Atom) (maxZ : ℕ)
    (ligandEq : frameLigand freshCompilation slot = ligand)
    (adjacent : graph.Adj ligand maxAtom) (maxNe : maxAtom ≠ A4)
    (maxAtomic : graph.atomZ maxAtom = maxZ)
    (bounded : ∀ w, graph.Adj ligand w → w ≠ A4 → graph.atomZ w ≤ maxZ) :
    ((freshCompilation.stages slot).a.key.constitutional.rule1a.getD 1 []).head? =
      some ([0], maxZ) := by
  let shape := freshSlotShape slot
  let cursor := freshCompilation.frame.cursorAt slot
  have currentLigand : cursor.occurrence.1.node.current? = some ligand := by
    rw [← ligandEq]
    exact frame_current freshCompilation slot
  have notParent : cursor.occurrence.1.node.parent? ≠ some maxAtom := by
    rw [shape.parent]
    intro same
    exact maxNe (Option.some.inj same.symm)
  obtain ⟨maxFrame, _, _, _, currentMax, _, _, memOut⟩ :=
    cyclicCertified.realCenter_outwardChildFrame_of_notParent fuel_enough cursor.occurrence
      currentLigand adjacent notParent shape.real
  have perm := fresh_outward_perm slot shape
  have derived := stage_derived freshCompilation slot
  generalize hkey : (freshCompilation.stages slot).a.key.constitutional = key at derived
  cases derived with
  | terminal childProof empty =>
      exfalso
      have mapEq := childProof.1
      simp [cyclicReferenceInput] at mapEq
      rw [empty, List.map_nil] at mapEq
      have outwardPerm : ([] : List cyclicCertified.LocalizedCIPOccurrenceFrame).Perm
          (cyclicCertified.localizedCarrierOutwardChildFrames
            (fuel := carrierFuel cyclicReferenceInput) cursor.occurrence.1) := by
        simpa [← mapEq] using perm
      have outwardNil := List.Perm.nil_eq outwardPerm
      rw [← outwardNil] at memOut
      simp at memOut
  | branch childProof nonempty childDerivations ranking descending =>
      rename_i children childKeys sorted
      have frameEq := childProof.1
      simp [cyclicReferenceInput] at frameEq
      have keyBound : ∀ childKey, childKey ∈ childKeys →
          ∃ z, childKey.rule1a.head? = some [([], z)] ∧ z ≤ maxZ := by
        intro childKey childKeyMem
        obtain ⟨child, childMem, childDerived⟩ := list_cursor_of_key childDerivations childKeyMem
        have frameMem : child.occurrence.1 ∈
            cyclicCertified.intendedLocalizedRerootChildFrames cursor := by
          rw [← frameEq]
          exact List.mem_map.mpr ⟨child, childMem, rfl⟩
        have outwardFrame := perm.mem_iff.mp frameMem
        obtain ⟨w, _, _, currentW, _, _, _, notParentW, adjW⟩ :=
          cyclicCertified.simpleBond_outwardFrame_extend_zero input_simpleBonded
            cursor.occurrence currentLigand shape.real child.occurrence.1 outwardFrame
        have wNe : w ≠ A4 := by
          intro equal
          exact notParentW (by rw [equal]; exact shape.parent)
        exact ⟨graph.atomZ w, child_key_head childDerived currentW, bounded w adjW wNe⟩
      have memIntended : maxFrame ∈ cyclicCertified.intendedLocalizedRerootChildFrames cursor :=
        perm.mem_iff.mpr memOut
      rw [← frameEq] at memIntended
      obtain ⟨maxChild, maxChildMem, maxChildEq⟩ := List.mem_map.mp memIntended
      obtain ⟨maxKey, maxKeyMem, maxDerived⟩ := list_key_of_mem childDerivations maxChildMem
      have maxCurrent : maxChild.occurrence.1.node.current? = some maxAtom := by
        rw [maxChildEq]
        exact currentMax
      have maxHead := child_key_head maxDerived maxCurrent
      rw [maxAtomic] at maxHead
      cases sorted with
      | nil => exact absurd (ranking.mem_iff.mpr maxKeyMem) (by simp)
      | cons headKey tail =>
          obtain ⟨z, headHead, zLe⟩ := keyBound headKey (ranking.mem_iff.mp List.mem_cons_self)
          have zEq : z = maxZ := by
            by_contra different
            have zlt : z < maxZ := Nat.lt_of_le_of_ne zLe different
            letI : Std.TransCmp (@compare cyclicCertified.Atom) := compare_transCmp
            have childGt := compare_gt_of_heads maxHead headHead zlt
            have headLt : compare headKey maxKey = Ordering.lt := by
              rw [← Std.OrientedCmp.gt_iff_lt]
              exact childGt
            have maxSorted : maxKey ∈ headKey :: tail := ranking.mem_iff.mpr maxKeyMem
            rcases List.mem_cons.mp maxSorted with same | later
            · rw [← same] at headHead
              have heads := headHead.symm.trans maxHead
              injection heads with layerEq
              injection layerEq with entryEq
              injection entryEq with _addrEq zSame
              exact different zSame
            · exact (List.pairwise_cons.mp descending).1 maxKey later headLt
          have sphere : headKey.rule1a.getD 0 [] = [([], maxZ)] := by
            rw [sphere_of_head headHead, zEq]
          exact assemble_second_head cursor.occurrence.1.node (headKey :: tail) (by simp)
            (by simpa [List.head_cons] using sphere)

private theorem fresh_first (slot : Fin 4) :
    (freshCompilation.stages slot).a.key.constitutional.rule1a.getD 0 [] =
      [([], graph.atomZ (frameLigand freshCompilation slot))] := by
  have head := declarative_head (stage_derived freshCompilation slot)
  rw [node_label_atomicNumber _ _ (frame_current freshCompilation slot)] at head
  exact sphere_of_head head

private theorem fresh_order (armSlot outerSlot : Fin 4)
    (armEq : frameLigand freshCompilation armSlot = A2)
    (outerEq : frameLigand freshCompilation outerSlot = A0) :
    OfficialRuleMajorKey.compare (freshCompilation.stages armSlot).a.key.constitutional
      (freshCompilation.stages outerSlot).a.key.constitutional = Ordering.gt := by
  have secondArm := fresh_second armSlot A2 A3 17 armEq adj_A2_A3 A3_ne_A4 z_chlorine
    (fun w adj _ne => arm_neighbor_bound adj)
  have secondOuter := fresh_second outerSlot A0 A1 9 outerEq adj_A0_A1 A1_ne_A4 z_fluorine
    (fun w adj ne => root_neighbor_bound adj ne)
  apply rule1a_gt_of_second_sphere
  · simpa [armEq, z_arm] using fresh_first armSlot
  · simpa [outerEq, z_root] using fresh_first outerSlot
  · exact secondArm
  · exact secondOuter
  · decide

structure FreshLigandKeyFacts (armSlot outerSlot : Fin 4) : Prop where
  armLigand : frameLigand freshCompilation armSlot = A2
  outerLigand : frameLigand freshCompilation outerSlot = A0
  armHistory : (freshCompilation.frame.cursorAt armSlot).occurrence.1.node.history = [A2, A4]
  outerHistory : (freshCompilation.frame.cursorAt outerSlot).occurrence.1.node.history = [A0, A4]
  armReal : (freshCompilation.frame.cursorAt armSlot).occurrence.1.node.provenance =
    OfficialCIPNodeProvenance.realAtom
  outerReal : (freshCompilation.frame.cursorAt outerSlot).occurrence.1.node.provenance =
    OfficialCIPNodeProvenance.realAtom
  armDistance : (freshCompilation.frame.cursorAt armSlot).occurrence.1.node.rule1bRootDistance = 1
  outerDistance : (freshCompilation.frame.cursorAt outerSlot).occurrence.1.node.rule1bRootDistance = 1
  armSource : (freshCompilation.stages armSlot).a.tree.source =
    freshCompilation.frame.cursorAt armSlot
  armBuilt : cyclicReferenceInput.certified.buildRuleMajorCumulativeWithRead?
    LocalizedCumulativeRule45Stage.rule4a
    (contextOccurrenceRead cyclicReferenceInput freshTarget)
    (2 * (carrierFuel cyclicReferenceInput + 1))
    (freshCompilation.frame.cursorAt armSlot) =
      some (freshCompilation.stages armSlot).a.key
  outerSource : (freshCompilation.stages outerSlot).a.tree.source =
    freshCompilation.frame.cursorAt outerSlot
  outerBuilt : cyclicReferenceInput.certified.buildRuleMajorCumulativeWithRead?
    LocalizedCumulativeRule45Stage.rule4a
    (contextOccurrenceRead cyclicReferenceInput freshTarget)
    (2 * (carrierFuel cyclicReferenceInput + 1))
    (freshCompilation.frame.cursorAt outerSlot) =
      some (freshCompilation.stages outerSlot).a.key
  chlorineBond : graph.Adj A2 A3
  fluorineBond : graph.Adj A0 A1
  chlorineAtomic : graph.atomZ A3 = 17
  fluorineAtomic : graph.atomZ A1 = 9
  armSecond :
    ((freshCompilation.stages armSlot).a.key.constitutional.rule1a.getD 1 []).head? = some ([0], 17)
  outerSecond :
    ((freshCompilation.stages outerSlot).a.key.constitutional.rule1a.getD 1 []).head? = some ([0], 9)
  comparison : OfficialRuleMajorKey.compare (freshCompilation.stages armSlot).a.key.constitutional
    (freshCompilation.stages outerSlot).a.key.constitutional = Ordering.gt

theorem fresh_ligand_keys_rank_arm_above_outer :
    ∃ armSlot outerSlot : Fin 4, FreshLigandKeyFacts armSlot outerSlot := by
  obtain ⟨armSlot, armEq⟩ := slot_of_ligand freshCompilation (fresh_mol_adj adj_A4_A2)
  obtain ⟨outerSlot, outerEq⟩ := slot_of_ligand freshCompilation (fresh_mol_adj adj_A4_A0)
  have armShape := freshSlotShape armSlot
  have outerShape := freshSlotShape outerSlot
  exact ⟨armSlot, outerSlot, {
    armLigand := armEq
    outerLigand := outerEq
    armHistory := by
      simpa [armEq] using armShape.history
    outerHistory := by
      simpa [outerEq] using outerShape.history
    armReal := armShape.real
    outerReal := outerShape.real
    armDistance := armShape.distance
    outerDistance := outerShape.distance
    armSource := (freshCompilation.stages armSlot).a.sourceEq
    armBuilt := (freshCompilation.stages armSlot).a.built
    outerSource := (freshCompilation.stages outerSlot).a.sourceEq
    outerBuilt := (freshCompilation.stages outerSlot).a.built
    chlorineBond := adj_A2_A3
    fluorineBond := adj_A0_A1
    chlorineAtomic := z_chlorine
    fluorineAtomic := z_fluorine
    armSecond := by
      simpa [z_chlorine] using fresh_second armSlot A2 A3 17 armEq adj_A2_A3 A3_ne_A4 z_chlorine
        (fun w adj hne => arm_neighbor_bound adj)
    outerSecond := by
      simpa [z_fluorine] using fresh_second outerSlot A0 A1 9 outerEq adj_A0_A1 A1_ne_A4 z_fluorine
        (fun w adj ne => root_neighbor_bound adj ne)
    comparison := fresh_order armSlot outerSlot armEq outerEq
  }⟩

theorem retained_and_fresh_carbon_orders_agree :
    ∃ parentSlot coreSlot armSlot outerSlot : Fin 4,
      OfficialRuleMajorKey.compare
          (standardClosingCompilation.stages parentSlot).a.key.constitutional
          (standardClosingCompilation.stages coreSlot).a.key.constitutional = Ordering.gt ∧
      OfficialRuleMajorKey.compare
          (freshCompilation.stages armSlot).a.key.constitutional
          (freshCompilation.stages outerSlot).a.key.constitutional = Ordering.gt ∧
      OfficialRuleMajorKey.compare
          (standardClosingCompilation.stages parentSlot).a.key.constitutional
          (standardClosingCompilation.stages coreSlot).a.key.constitutional =
        OfficialRuleMajorKey.compare
          (freshCompilation.stages armSlot).a.key.constitutional
          (freshCompilation.stages outerSlot).a.key.constitutional := by
  obtain ⟨parentSlot, parentShape⟩ := retained_parent_shape
  obtain ⟨coreSlot, coreShape⟩ := retained_core_shape
  obtain ⟨armSlot, armEq⟩ := slot_of_ligand freshCompilation (fresh_mol_adj adj_A4_A2)
  obtain ⟨outerSlot, outerEq⟩ := slot_of_ligand freshCompilation (fresh_mol_adj adj_A4_A0)
  have retainedGt := retained_order parentSlot coreSlot parentShape coreShape
  have freshGt := fresh_order armSlot outerSlot armEq outerEq
  exact ⟨parentSlot, coreSlot, armSlot, outerSlot, retainedGt, freshGt, by
    rw [retainedGt, freshGt]⟩

end

end TetraStereo.OneCenter.LocalizedCyclicRetainedFreshContextWitness

assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRetainedFreshContextWitness.evaluationFuel_eq_twentyTwo
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRetainedFreshContextWitness.parent_backtrack_not_executable_child
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRetainedFreshContextWitness.source_path_depth_two_versus_one
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRetainedFreshContextWitness.retained_slot_cut
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRetainedFreshContextWitness.fresh_slot_cut
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRetainedFreshContextWitness.retained_ligand_keys_rank_parent_above_core
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRetainedFreshContextWitness.fresh_ligand_keys_rank_arm_above_outer
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRetainedFreshContextWitness.retained_and_fresh_carbon_orders_agree
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRetainedFreshContextWitness.fresh_detected
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRetainedFreshContextWitness.fresh_unit_target
