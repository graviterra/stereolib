import TetraStereo.UniversalProof.SecondSphereFamilyPhysicalInstantiation
import TetraStereo.UniversalProof.SecondSphereNativeBlockParser
import TetraStereo.UniversalProof.NativeFamilyReportRawHelpers

set_option autoImplicit false

namespace TetraStereo.UniversalProof.SecondSphereFamilyValenceInstantiation

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.ChronologicalRawAdmissionRecoveryProofs.ChronologicalRawAdmissionRecovery
open TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords
open TetraStereo.UniversalProof.SecondSphereFamilyPhysicalInstantiation
open TetraStereo.UniversalProof.GeneralParserStateBridge (FamilyAtom atomSpec)





/-- The actual block fold followed by its one final hydrogen append. -/
def finishedBlocks (ps : List TetrahedralInputParity) (mol : RawMolecule)
    (parent : Fin mol.atomCount) : RawMolecule :=
  appendFreshChild (blocksResult543 ps mol parent)
    ⟨blocksParent543 ps mol parent, blocksParent543_bounded ps mol parent⟩ hydrogenSpec

/-- Finishing a suffix preserves any previously completed non-parent row. -/
theorem finishedBlocks_records_old (ps : List TetrahedralInputParity) (mol : RawMolecule)
    (parent : Fin mol.atomCount) (center : Nat) (older : center < mol.atomCount)
    (different : parent.val ≠ center) :
    recordNeighbors (finishedBlocks ps mol parent) center = recordNeighbors mol center := by
  have count := blocksResult543_atomCount ps mol parent
  have finalDifferent : blocksParent543 ps mol parent ≠ center := by
    cases ps with
    | nil => exact different
    | cons p rest =>
        have beyond := blocksParent_ge_count (p :: rest) mol parent (by simp)
        omega
  unfold finishedBlocks
  rw [appendFreshChild_records_old _ _ _ center (by omega) finalDifferent,
    blocksResult_records_old ps mol parent center older different]

/-- One complete block adds exactly the new backbone to its old continuation parent's row. -/
theorem blockAppend_records_parent (mol : RawMolecule) (base : Nat)
    (count : mol.atomCount = base) (parent : Fin mol.atomCount)
    (parity : TetrahedralInputParity) :
    recordNeighbors (blockAppend mol base count parent parity) parent.val =
      recordNeighbors mol parent.val ++ [base] := by
  have parentBound : parent.val < base := by simpa only [count] using parent.isLt
  have tail : (twelveBonds parent.val base).filterMap (recordNeighbor? parent.val) = [base] := by
    have baseDifferent : base ≠ parent.val := by omega
    have newer (offset : Nat) : base + offset ≠ parent.val := by omega
    simp only [twelveBonds, List.filterMap_cons, List.filterMap_nil]
    simp [recordNeighbor?, baseDifferent, newer]
  change ((blockAppend mol base count parent parity).bonds.filterMap (recordNeighbor? parent.val)) = _
  rw [blockAppend_bonds_exact, List.filterMap_append, tail]
  rfl

/-- A current backbone receives exactly one next atom: the next backbone, or the final cap. -/
theorem finishedBlocks_records_parent (ps : List TetrahedralInputParity) (mol : RawMolecule)
    (parent : Fin mol.atomCount) :
    recordNeighbors (finishedBlocks ps mol parent) parent.val =
      recordNeighbors mol parent.val ++ [mol.atomCount] := by
  cases ps with
  | nil =>
      change recordNeighbors (appendFreshChild mol parent hydrogenSpec) parent.val = _
      rw [appendFreshChild_records_at_old mol parent hydrogenSpec parent.val parent.isLt,
        if_pos rfl]
  | cons parity rest =>
      let next := blockAppend mol mol.atomCount rfl parent parity
      let nextParent : Fin next.atomCount := ⟨mol.atomCount, by rw [blockAppend_atomCount]; omega⟩
      have nextCount : next.atomCount = mol.atomCount + 12 := blockAppend_atomCount _ _ _ _ _
      have oldBound := parent.isLt
      change recordNeighbors (finishedBlocks rest next nextParent) parent.val = _
      rw [finishedBlocks_records_old rest next nextParent parent.val (by omega)
        (by change mol.atomCount ≠ parent.val; omega)]
      exact blockAppend_records_parent mol mol.atomCount rfl parent parity

/-- Incoming atom of a block, read solely from chronological allocation indices. -/
def incomingIndex (parent base index : Nat) : Nat :=
  if index = 0 then parent else base + 12 * (index - 1)

theorem incomingIndex_shift (parent base index : Nat) :
    incomingIndex base (base + 12) index = incomingIndex parent base (index + 1) := by
  cases index with
  | zero => simp [incomingIndex]
  | succ index =>
      simp only [incomingIndex, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
      omega

/-- A just-created backbone has its introduction parent and its H and bridge-C branches. -/
theorem blockAppend_records_backbone (mol : RawMolecule) (well : mol.WellFormed)
    (parent : Fin mol.atomCount) (parity : TetrahedralInputParity) :
    recordNeighbors (blockAppend mol mol.atomCount rfl parent parity) mol.atomCount =
      [parent.val, mol.atomCount + 1, mol.atomCount + 2] := by
  have old := recordNeighbors_of_ge_atomCount mol well mol.atomCount (Nat.le_refl _)
  have parentBound := parent.isLt
  have tail : (twelveBonds parent.val mol.atomCount).filterMap (recordNeighbor? mol.atomCount) =
      [parent.val, mol.atomCount + 1, mol.atomCount + 2] := by
    have parentDifferent : parent.val ≠ mol.atomCount := by omega
    simp only [twelveBonds, List.filterMap_cons, List.filterMap_nil]
    simp [recordNeighbor?, parentDifferent]
  change ((blockAppend mol mol.atomCount rfl parent parity).bonds.filterMap
    (recordNeighbor? mol.atomCount)) = _
  rw [blockAppend_bonds_exact, List.filterMap_append]
  change recordNeighbors mol mol.atomCount ++ _ = _
  rw [old, List.nil_append, tail]

/-- Every backbone's next neighbor has the same index whether it is carbon or the terminal cap. -/
theorem finishedBlocks_records_backbone (ps : List TetrahedralInputParity) (mol : RawMolecule)
    (well : mol.WellFormed) (parent : Fin mol.atomCount) (i : Nat) (indexBound : i < ps.length) :
    recordNeighbors (finishedBlocks ps mol parent) (mol.atomCount + 12 * i) =
      [incomingIndex parent.val mol.atomCount i, mol.atomCount + 12 * i + 1,
        mol.atomCount + 12 * i + 2, mol.atomCount + 12 * i + 12] := by
  induction ps generalizing mol parent i with
  | nil => simp at indexBound
  | cons parity rest ih =>
      let next := blockAppend mol mol.atomCount rfl parent parity
      let nextParent : Fin next.atomCount := ⟨mol.atomCount, by rw [blockAppend_atomCount]; omega⟩
      have nextCount : next.atomCount = mol.atomCount + 12 := blockAppend_atomCount _ _ _ _ _
      change recordNeighbors (finishedBlocks rest next nextParent) (mol.atomCount + 12 * i) = _
      cases i with
      | zero =>
          have parentRow := finishedBlocks_records_parent rest next nextParent
          change recordNeighbors (finishedBlocks rest next nextParent) mol.atomCount =
            recordNeighbors next mol.atomCount ++ [next.atomCount] at parentRow
          simp only [Nat.mul_zero, Nat.add_zero]
          rw [parentRow, blockAppend_records_backbone mol well parent parity, nextCount]
          rfl
      | succ i =>
          have restBound : i < rest.length := by
            simpa only [List.length_cons, Nat.succ_lt_succ_iff] using indexBound
          have nextWell : next.WellFormed := by
            unfold next blockAppend
            dsimp only
            repeat (first | apply appendFreshChild_wellFormed)
            exact well
          have selected := ih next nextWell nextParent i restBound
          have baseEqual : next.atomCount + 12 * i = mol.atomCount + 12 * (i + 1) := by omega
          have previousEqual : incomingIndex nextParent.val next.atomCount i =
              incomingIndex parent.val mol.atomCount (i + 1) := by
            change incomingIndex mol.atomCount next.atomCount i = _
            rw [nextCount]
            exact incomingIndex_shift _ _ _
          simpa only [baseEqual, previousEqual] using selected

theorem familyRaw_backbone_records (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    recordNeighbors (familyRaw ps) (1 + 12 * i.val) =
      [if i.val = 0 then 0 else 1 + 12 * (i.val - 1),
        1 + 12 * i.val + 1, 1 + 12 * i.val + 2, 1 + 12 * i.val + 12] := by
  exact finishedBlocks_records_backbone ps family543Base family543Base_blockGood.1
    baseFin i.val i.isLt

theorem familyRaw_left_cap_records (ps : List TetrahedralInputParity) :
    recordNeighbors (familyRaw ps) 0 = [1] := by
  have parentRow := finishedBlocks_records_parent ps family543Base baseFin
  exact parentRow

theorem familyRaw_final_cap_records (ps : List TetrahedralInputParity) :
    recordNeighbors (familyRaw ps) (12 * ps.length + 1) =
      [blocksParent543 ps family543Base baseFin] := by
  have count : (blocksResult543 ps family543Base baseFin).atomCount = 12 * ps.length + 1 := by
    rw [blocksResult543_atomCount]
    change 1 + 12 * ps.length = _
    omega
  have well := (blocksResult543_blockGood ps family543Base baseFin family543Base_blockGood).1
  have row := appendFreshChild_records_at_fresh
    (blocksResult543 ps family543Base baseFin) well
    ⟨blocksParent543 ps family543Base baseFin, blocksParent543_bounded ps family543Base baseFin⟩
    hydrogenSpec
  change recordNeighbors (familyRaw ps) (blocksResult543 ps family543Base baseFin).atomCount =
    [blocksParent543 ps family543Base baseFin] at row
  simpa only [count] using row

theorem familyRaw_backbone_demand (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (familyRaw ps).incidentBondOrderSum (1 + 12 * i.val) = 4 := by
  simp [familyRaw_incident_sum, familyRaw_backbone_records]

theorem familyRaw_caps_demand (ps : List TetrahedralInputParity) :
    (familyRaw ps).incidentBondOrderSum 0 = 1 ∧
      (familyRaw ps).incidentBondOrderSum (12 * ps.length + 1) = 1 := by
  simp [familyRaw_incident_sum, familyRaw_left_cap_records, familyRaw_final_cap_records]



/-- Role type covers both caps and every actual block atom, including the continuation backbone. -/
inductive AtomRole (ps : List TetrahedralInputParity) where
  | leftCap
  | rightCap
  | block (index : Fin ps.length) (offset : Fin 12)

def atomRoleIndex {ps : List TetrahedralInputParity} : AtomRole ps → Nat
  | .leftCap => 0
  | .rightCap => 12 * ps.length + 1
  | .block i offset => 1 + 12 * i.val + offset.val

def atomRoleSpec {ps : List TetrahedralInputParity} : AtomRole ps → AtomSpec
  | .leftCap | .rightCap => hydrogenSpec
  | .block i offset => roleAtom (ps.get i) (roleOfOffset offset.val)

def atomRoleDemand {ps : List TetrahedralInputParity} : AtomRole ps → Nat
  | .leftCap | .rightCap => 1
  | .block _ offset => if offset.val = 0 ∨ offset.val = 2 ∨ offset.val = 5 ∨ offset.val = 8 then 4 else 1

theorem familyRaw_cap_atoms (ps : List TetrahedralInputParity) :
    (familyRaw ps).atomAt? 0 = some hydrogenSpec ∧
    (familyRaw ps).atomAt? (12 * ps.length + 1) = some hydrogenSpec := by
  constructor
  · change listGet? (familyRaw ps).atoms 0 = _
    rw [familyRaw_atoms]
    rfl
  · change listGet? (familyRaw ps).atoms (12 * ps.length + 1) = _
    rw [familyRaw_atoms]
    have position : 12 * ps.length + 1 = [hydrogenSpec].length + 12 * ps.length := by
      change 12 * ps.length + 1 = 1 + 12 * ps.length
      omega
    rw [position, listGet?_append_right,
      listGet?_flatMap_blocks_high ps (12 * ps.length) (Nat.le_refl _), if_pos rfl]

theorem familyRaw_atomRole_lookup (ps : List TetrahedralInputParity) (role : AtomRole ps) :
    (familyRaw ps).atomAt? (atomRoleIndex role) = some (atomRoleSpec role) := by
  cases role with
  | leftCap => exact (familyRaw_cap_atoms ps).1
  | rightCap => exact (familyRaw_cap_atoms ps).2
  | block i offset => exact familyRaw_role_atom ps i offset.val offset.isLt

/-- Actual lookup, not an assumed census: all stored atoms are caps or twelve-append roles. -/
theorem familyRaw_atomRole_of_lookup (ps : List TetrahedralInputParity) (index : Nat)
    (spec : AtomSpec) (lookup : (familyRaw ps).atomAt? index = some spec) :
    ∃ role : AtomRole ps, index = atomRoleIndex role ∧ spec = atomRoleSpec role := by
  have bounded := listGet?_eq_some_implies_lt (familyRaw ps).atoms index spec lookup
  change index < (familyRaw ps).atomCount at bounded
  rw [familyRaw_atomCount] at bounded
  by_cases leading : index = 0
  · subst index
    have matching := (familyRaw_cap_atoms ps).1
    rw [lookup] at matching
    exact ⟨.leftCap, rfl, Option.some.inj matching⟩
  · by_cases trailing : index = 12 * ps.length + 1
    · subst index
      have matching := (familyRaw_cap_atoms ps).2
      rw [lookup] at matching
      exact ⟨.rightCap, rfl, Option.some.inj matching⟩
    · let m := index - 1
      have positive : 0 < index := by omega
      have internal : m < 12 * ps.length := by dsimp [m]; omega
      have remainder : m % 12 < 12 := Nat.mod_lt _ (by decide)
      have division := Nat.div_add_mod m 12
      have quotient : m / 12 < ps.length := by omega
      let i : Fin ps.length := ⟨m / 12, quotient⟩
      let offset : Fin 12 := ⟨m % 12, remainder⟩
      have position : index = atomRoleIndex (.block i offset) := by
        change index = 1 + 12 * (m / 12) + m % 12
        dsimp [m] at division ⊢
        omega
      have matching := familyRaw_atomRole_lookup ps (.block i offset)
      rw [← position, lookup] at matching
      exact ⟨.block i offset, position, Option.some.inj matching⟩

theorem atomRoleSpec_zero_explicit {ps : List TetrahedralInputParity} (role : AtomRole ps) :
    (atomRoleSpec role).explicitHydrogens = 0 := by
  cases role with
  | leftCap | rightCap => rfl
  | block i offset =>
      change (roleAtom (ps.get i) (roleOfOffset offset.val)).explicitHydrogens = 0
      cases roleOfOffset offset.val <;> rfl

theorem atomRoleDemand_allowed {ps : List TetrahedralInputParity} (role : AtomRole ps) :
    atomRoleDemand role ∈ (atomRoleSpec role).allowedValences := by
  cases role with
  | leftCap | rightCap =>
      change 1 ∈ ([1] : List Nat)
      exact List.mem_cons_self
  | block i offset =>
      obtain ⟨offset, bound⟩ := offset
      interval_cases offset <;>
        simp [atomRoleDemand, atomRoleSpec, roleOfOffset, roleAtom, carbonSpec, hydrogenSpec,
          fluorineSpec, atomSpec, AtomSpec.allowedValences, Element.allowedValences]

/-- Every actual atom has exact saturation demand, including both H caps and all backbones. -/
theorem familyRaw_atomRole_incident_demand (ps : List TetrahedralInputParity) (role : AtomRole ps) :
    (familyRaw ps).incidentBondOrderSum (atomRoleIndex role) = atomRoleDemand role := by
  cases role with
  | leftCap => exact (familyRaw_caps_demand ps).1
  | rightCap => exact (familyRaw_caps_demand ps).2
  | block i offset =>
      by_cases backbone : offset.val = 0
      · have row := familyRaw_backbone_demand ps i
        simpa [atomRoleIndex, atomRoleDemand, backbone] using row
      · have positive : 0 < offset.val := by omega
        have row := familyRaw_local_demand ps i offset.val positive offset.isLt
        simpa [atomRoleIndex, atomRoleDemand, backbone] using row

theorem familyRaw_atomRole_used_demand (ps : List TetrahedralInputParity) (role : AtomRole ps) :
    (familyRaw ps).usedValenceAt (atomRoleIndex role) = atomRoleDemand role := by
  unfold usedValenceAt
  rw [familyRaw_atomRole_lookup]
  change (atomRoleSpec role).explicitHydrogens + _ = _
  rw [atomRoleSpec_zero_explicit, Nat.zero_add, familyRaw_atomRole_incident_demand]

/-- Whole family encoded valence, including n0 H-H, with no admitted outcome as premise. -/
theorem familyRaw_valenceOK (ps : List TetrahedralInputParity) : (familyRaw ps).ValenceOK := by
  intro index spec lookup
  obtain ⟨role, indexEq, specEq⟩ := familyRaw_atomRole_of_lookup ps index spec lookup
  rw [indexEq, specEq]
  exact ⟨atomRoleDemand role, atomRoleDemand_allowed role,
    le_of_eq (familyRaw_atomRole_used_demand ps role)⟩

theorem familyRaw_stereochemical_admissible (ps : List TetrahedralInputParity) :
    (familyRaw ps).StereochemicalAdmissible :=
  ⟨⟨familyRaw_wellFormed ps, familyRaw_bondRecordsUnique ps⟩, familyRaw_writtenNeighborExact ps⟩

/-- Production normalization is genuinely identity on this actual all-single constructor. -/
theorem familyRaw_normalized_parsed (ps : List TetrahedralInputParity) :
    (normalizeRawMolecule (familyRaw ps)).parsed = familyRaw ps :=
  ActualFamilyReportBridgeProofs.ActualFamilyReportBridge.normalize_single_identity (familyRaw ps) (familyRaw_all_single ps)

/-- Independent repeated-C tag shape; this is saturation and written metadata, not a rank. -/
def SaturatedTagSites (raw : RawMolecule) : Prop :=
  ∀ index spec parity, raw.atomAt? index = some spec → spec.tetrahedral? = some parity →
    spec.element = .C ∧ raw.usedValenceAt index = 4 ∧
    (raw.writtenNeighbors index).length = 4 ∧
    (raw.writtenNeighbors index).map raw.atomZAt = [6, 1, 9, 6]

/-- Every observed tag, not a supplied tag list, has actual saturated C/H/F/C physical metadata. -/
theorem familyRaw_saturatedTagSites (ps : List TetrahedralInputParity) :
    SaturatedTagSites (familyRaw ps) := by
  intro index spec parity lookup annotation
  have observed : observedTag (familyRaw ps) index = some parity := by
    unfold observedTag
    rw [lookup]
    exact annotation
  obtain ⟨i, indexEq, _⟩ := (familyRaw_observedTag_iff ps index parity).mp observed
  have position : index = 1 + 12 * i.val + 5 := by
    rw [indexEq]
    unfold tagIndex
    omega
  rw [position] at lookup ⊢
  have actual := familyRaw_role_atom ps i 5 (by decide)
  rw [lookup] at actual
  have specEq := Option.some.inj actual
  rw [specEq]
  refine ⟨rfl, familyRaw_atomRole_used_demand ps (.block i ⟨5, by decide⟩), ?_, ?_⟩
  · simp [familyRaw_tag_written]
  · rw [familyRaw_tag_written]
    have atoms := familyRaw_interior_carbon_Z ps i
    have terminals := familyRaw_terminal_Z ps i
    simp only [List.map_cons, List.map_nil, atoms.2.1, terminals.2.2.2.1,
      terminals.2.2.2.2.1, atoms.2.2.2]

theorem normalizedSaturatedTagSites (ps : List TetrahedralInputParity) :
    SaturatedTagSites (normalizeRawMolecule (familyRaw ps)).parsed := by
  rw [familyRaw_normalized_parsed]
  exact familyRaw_saturatedTagSites ps

/-- The independent raw family retains its checked source-introduction history. The native
record invariant is transported through exact constructor equality; parser execution is not a
premise of this result. -/
theorem familyRaw_introduction_valid (ps : List TetrahedralInputParity) :
    (familyRaw ps).introductionPredecessorsValid? = true := by
  have valid := SecondSphereNativeBlockParser.native_family_introduction_valid ps
  simp only [RawMolecule.parserIntroductionValid?, Bool.and_eq_true] at valid
  exact valid.2

/-- This certified object is constructed from proved intake facts, not supplied by a caller. -/
def certifiedFamily (ps : List TetrahedralInputParity) : CertifiedChemistryNormalizationResult where
  result := normalizeRawMolecule (familyRaw ps)
  admissible := by
    rw [familyRaw_normalized_parsed]
    exact (familyRaw_stereochemical_admissible ps).1
  writtenNeighborExact := by
    rw [familyRaw_normalized_parsed]
    exact familyRaw_writtenNeighborExact ps
  valenceOK := by
    rw [familyRaw_normalized_parsed]
    exact familyRaw_valenceOK ps
  rule2MassesKnown := by
    rw [familyRaw_normalized_parsed]
    exact familyRaw_masses_known ps

/-- Actual executable certify? returns the internally built family certificate for every parity list. -/
theorem familyRaw_actual_certified_intake (ps : List TetrahedralInputParity) :
    normalizeRawMoleculeCertified? (familyRaw ps) = some (certifiedFamily ps) := by
  have introduction :
      (normalizeRawMolecule (familyRaw ps)).parsed.introductionPredecessorsValid? = true := by
    rw [familyRaw_normalized_parsed]
    exact familyRaw_introduction_valid ps
  have admission : (normalizeRawMolecule (familyRaw ps)).parsed.admissible? = true := by
    apply (RawMolecule.admissible?_eq_true_iff _).mpr
    rw [familyRaw_normalized_parsed]
    exact (familyRaw_stereochemical_admissible ps).1
  have written : (normalizeRawMolecule (familyRaw ps)).parsed.writtenNeighborExact? = true := by
    apply (RawMolecule.writtenNeighborExact?_eq_true_iff _).mpr
    rw [familyRaw_normalized_parsed]
    exact familyRaw_writtenNeighborExact ps
  have valence : (normalizeRawMolecule (familyRaw ps)).parsed.valenceOK? = true := by
    apply (RawMolecule.valenceOK?_eq_true_iff _).mpr
    rw [familyRaw_normalized_parsed]
    exact familyRaw_valenceOK ps
  have masses : (normalizeRawMolecule (familyRaw ps)).parsed.rule2MassesKnown? = true := by
    apply (RawMolecule.rule2MassesKnown?_eq_true_iff _).mpr
    rw [familyRaw_normalized_parsed]
    exact familyRaw_masses_known ps
  unfold normalizeRawMoleculeCertified? ChemistryNormalizationResult.certify? certifiedFamily
  rw [if_pos introduction, dif_pos admission, dif_pos written, dif_pos valence, dif_pos masses]

theorem certifiedFamily_parsed (ps : List TetrahedralInputParity) :
    (certifiedFamily ps).result.parsed = familyRaw ps := familyRaw_normalized_parsed ps

/-- Whole positive-or-zero family intake, independent of parser and discovery execution outcomes. -/
theorem whole_family_certified_intake (ps : List TetrahedralInputParity) :
    ∃ certified : CertifiedChemistryNormalizationResult,
      normalizeRawMoleculeCertified? (familyRaw ps) = some certified ∧
      certified.result.parsed = familyRaw ps ∧
      SaturatedTagSites certified.result.parsed := by
  exact ⟨certifiedFamily ps, familyRaw_actual_certified_intake ps,
    certifiedFamily_parsed ps, normalizedSaturatedTagSites ps⟩

end TetraStereo.UniversalProof.SecondSphereFamilyValenceInstantiation
