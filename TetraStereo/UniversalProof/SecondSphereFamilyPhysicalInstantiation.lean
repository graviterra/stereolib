import TetraStereo.OneCenter.BranchSphereKey
import TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords
import TetraStereo.UniversalProof.NativeSingleBondRawSupport

set_option autoImplicit false

namespace TetraStereo.UniversalProof.SecondSphereFamilyPhysicalInstantiation

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.ChronologicalRawAdmissionRecoveryProofs.ChronologicalRawAdmissionRecovery
open TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords
open TetraStereo.UniversalProof.GeneralParserStateBridge (FamilyAtom atomSpec)





/-- All twelve bonds written by the actual raw block constructor, in chronological order. -/
def twelveBonds (parent base : Nat) : List RawBond :=
  [⟨parent, base, .single⟩, ⟨base, base + 1, .single⟩,
   ⟨base, base + 2, .single⟩, ⟨base + 2, base + 3, .single⟩,
   ⟨base + 2, base + 4, .single⟩, ⟨base + 2, base + 5, .single⟩,
   ⟨base + 5, base + 6, .single⟩, ⟨base + 5, base + 7, .single⟩,
   ⟨base + 5, base + 8, .single⟩, ⟨base + 8, base + 9, .single⟩,
   ⟨base + 8, base + 10, .single⟩, ⟨base + 8, base + 11, .single⟩]

theorem blockAppend_bonds_exact (mol : RawMolecule) (base : Nat)
    (count : mol.atomCount = base) (parent : Fin mol.atomCount)
    (parity : TetrahedralInputParity) :
    (blockAppend mol base count parent parity).bonds = mol.bonds ++ twelveBonds parent.val base := by
  unfold blockAppend
  dsimp only
  simp only [appendFreshChild_bonds, freshBond, appendFreshChild_atomCount,
    List.append_assoc, List.cons_append, List.nil_append]
  simp only [count, twelveBonds]

/-- Exact independent role table for the completed non-backbone rows of one block. -/
def closedLocalRow (base offset : Nat) : List Nat :=
  match offset with
  | 1 => [base]
  | 2 => [base, base + 3, base + 4, base + 5]
  | 3 | 4 => [base + 2]
  | 5 => [base + 2, base + 6, base + 7, base + 8]
  | 6 | 7 => [base + 5]
  | 8 => [base + 5, base + 9, base + 10, base + 11]
  | 9 | 10 | 11 => [base + 8]
  | _ => []

private theorem recordNeighbor_none (bond : RawBond) (center : Nat)
    (source : bond.source ≠ center) (target : bond.target ≠ center) :
    recordNeighbor? center bond = none := by
  simp [recordNeighbor?, source, target]

/-- Existing well-formed records cannot mention an as-yet-unallocated role. -/
theorem recordNeighbors_of_ge_atomCount (mol : RawMolecule) (well : mol.WellFormed)
    (center : Nat) (outside : mol.atomCount ≤ center) : recordNeighbors mol center = [] := by
  unfold recordNeighbors
  apply List.filterMap_eq_nil_iff.mpr
  intro bond member
  obtain ⟨sourceBound, targetBound, _⟩ := well bond member
  apply recordNeighbor_none
  · omega
  · omega

/-- A new block cannot touch an old completed role unless it is the explicit continuation parent. -/
theorem twelveBonds_avoid_old (parent base center : Nat) (older : center < base)
    (different : parent ≠ center) :
    (twelveBonds parent base).filterMap (recordNeighbor? center) = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro bond member
  simp only [twelveBonds, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals apply recordNeighbor_none <;> dsimp only <;> omega

/-- Every local offset1..11 has its closed record row directly from the actual twelve edge list. -/
theorem twelveBonds_local_rows (parent base offset : Nat) (parentBound : parent < base)
    (positive : 0 < offset) (bound : offset < 12) :
    (twelveBonds parent base).filterMap (recordNeighbor? (base + offset)) =
      closedLocalRow base offset := by
  have parentDifferent : parent ≠ base + offset := by omega
  interval_cases offset <;>
    simp [twelveBonds, closedLocalRow, recordNeighbor?, parentDifferent]

/-- The actual block preserves all old rows except its explicit continuation parent's row. -/
theorem blockAppend_records_old (mol : RawMolecule) (base : Nat)
    (count : mol.atomCount = base) (parent : Fin mol.atomCount)
    (parity : TetrahedralInputParity) (center : Nat)
    (older : center < base) (different : parent.val ≠ center) :
    recordNeighbors (blockAppend mol base count parent parity) center = recordNeighbors mol center := by
  change ((blockAppend mol base count parent parity).bonds.filterMap (recordNeighbor? center)) = _
  rw [blockAppend_bonds_exact, List.filterMap_append,
    twelveBonds_avoid_old parent.val base center older different, List.append_nil]
  rfl

/-- New local records are derived without supplying any physical-row result. -/
theorem blockAppend_records_local (mol : RawMolecule) (well : mol.WellFormed) (base : Nat)
    (count : mol.atomCount = base) (parent : Fin mol.atomCount)
    (parity : TetrahedralInputParity) (offset : Nat)
    (positive : 0 < offset) (bound : offset < 12) :
    recordNeighbors (blockAppend mol base count parent parity) (base + offset) =
      closedLocalRow base offset := by
  have parentBound : parent.val < base := by simpa only [count] using parent.isLt
  have old : recordNeighbors mol (base + offset) = [] :=
    recordNeighbors_of_ge_atomCount mol well _ (by omega)
  change ((blockAppend mol base count parent parity).bonds.filterMap
    (recordNeighbor? (base + offset))) = _
  rw [blockAppend_bonds_exact, List.filterMap_append]
  change recordNeighbors mol (base + offset) ++ _ = _
  rw [old, List.nil_append, twelveBonds_local_rows parent.val base offset parentBound positive bound]

/-- Every suffix of blocks preserves a completed old non-continuation role. -/
theorem blocksResult_records_old (ps : List TetrahedralInputParity) (mol : RawMolecule)
    (parent : Fin mol.atomCount) (center : Nat)
    (older : center < mol.atomCount) (different : parent.val ≠ center) :
    recordNeighbors (blocksResult543 ps mol parent) center = recordNeighbors mol center := by
  induction ps generalizing mol parent with
  | nil => rfl
  | cons parity rest ih =>
      let next := blockAppend mol mol.atomCount rfl parent parity
      let nextParent : Fin next.atomCount := ⟨mol.atomCount, by rw [blockAppend_atomCount]; omega⟩
      have nextCount : next.atomCount = mol.atomCount + 12 := blockAppend_atomCount _ _ _ _ _
      have retained := ih next nextParent (by omega) (by change mol.atomCount ≠ center; omega)
      change recordNeighbors (blocksResult543 rest next nextParent) center = _
      rw [retained]
      exact blockAppend_records_old mol mol.atomCount rfl parent parity center older different

/-- The selected block's local closed role remains unchanged through all later blocks. -/
theorem blocksResult_records_local (ps : List TetrahedralInputParity) (mol : RawMolecule)
    (well : mol.WellFormed) (parent : Fin mol.atomCount)
    (i offset : Nat) (indexBound : i < ps.length) (positive : 0 < offset) (bound : offset < 12) :
    recordNeighbors (blocksResult543 ps mol parent) (mol.atomCount + 12 * i + offset) =
      closedLocalRow (mol.atomCount + 12 * i) offset := by
  induction ps generalizing mol parent i with
  | nil => simp at indexBound
  | cons parity rest ih =>
      let next := blockAppend mol mol.atomCount rfl parent parity
      let nextParent : Fin next.atomCount := ⟨mol.atomCount, by rw [blockAppend_atomCount]; omega⟩
      have nextCount : next.atomCount = mol.atomCount + 12 := blockAppend_atomCount _ _ _ _ _
      change recordNeighbors (blocksResult543 rest next nextParent) (mol.atomCount + 12 * i + offset) = _
      cases i with
      | zero =>
          have retained := blocksResult_records_old rest next nextParent (mol.atomCount + offset)
            (by omega) (by change mol.atomCount ≠ mol.atomCount + offset; omega)
          simpa only [Nat.mul_zero, Nat.add_zero] using
            retained.trans (blockAppend_records_local mol well mol.atomCount rfl parent parity offset positive bound)
      | succ i =>
          have restBound : i < rest.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using indexBound
          have nextWell : next.WellFormed := by
            unfold next blockAppend
            dsimp only
            repeat (first | apply appendFreshChild_wellFormed)
            exact well
          have selected := ih next nextWell nextParent i restBound
          have baseEqual : next.atomCount + 12 * i = mol.atomCount + 12 * (i + 1) := by omega
          simpa only [baseEqual] using selected

/-- Future continuation parents never move backwards. -/
theorem blocksParent_ge_parent (ps : List TetrahedralInputParity) (mol : RawMolecule)
    (parent : Fin mol.atomCount) : parent.val ≤ blocksParent543 ps mol parent := by
  induction ps generalizing mol parent with
  | nil => exact Nat.le_refl _
  | cons parity rest ih =>
      change parent.val ≤ blocksParent543 rest (blockAppend mol mol.atomCount rfl parent parity)
        ⟨mol.atomCount, by rw [blockAppend_atomCount]; omega⟩
      have later := ih (blockAppend mol mol.atomCount rfl parent parity)
        ⟨mol.atomCount, by rw [blockAppend_atomCount]; omega⟩
      have bounded := parent.isLt
      change mol.atomCount ≤ _ at later
      omega

/-- A nonempty suffix returns a backbone at or beyond its original allocation boundary. -/
theorem blocksParent_ge_count (ps : List TetrahedralInputParity) (mol : RawMolecule)
    (parent : Fin mol.atomCount) (nonempty : ps ≠ []) :
    mol.atomCount ≤ blocksParent543 ps mol parent := by
  cases ps with
  | nil => exact False.elim (nonempty rfl)
  | cons parity rest =>
      exact blocksParent_ge_parent rest (blockAppend mol mol.atomCount rfl parent parity)
        ⟨mol.atomCount, by rw [blockAppend_atomCount]; omega⟩

/-- The final cap's backbone parent is distinct from every completed offset1..11. -/
theorem blocksParent_avoids_local (ps : List TetrahedralInputParity) (mol : RawMolecule)
    (parent : Fin mol.atomCount) (i offset : Nat)
    (indexBound : i < ps.length) (positive : 0 < offset) (bound : offset < 12) :
    blocksParent543 ps mol parent ≠ mol.atomCount + 12 * i + offset := by
  induction ps generalizing mol parent i with
  | nil => simp at indexBound
  | cons parity rest ih =>
      let next := blockAppend mol mol.atomCount rfl parent parity
      let nextParent : Fin next.atomCount := ⟨mol.atomCount, by rw [blockAppend_atomCount]; omega⟩
      have nextCount : next.atomCount = mol.atomCount + 12 := blockAppend_atomCount _ _ _ _ _
      change blocksParent543 rest next nextParent ≠ _
      cases i with
      | zero =>
          cases rest with
          | nil => change mol.atomCount ≠ mol.atomCount + 12 * 0 + offset; omega
          | cons p remaining =>
              have later := blocksParent_ge_count (p :: remaining) next nextParent (by simp)
              omega
      | succ i =>
          have restBound : i < rest.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using indexBound
          have selected := ih next nextParent i restBound
          have baseEqual : next.atomCount + 12 * i = mol.atomCount + 12 * (i + 1) := by omega
          simpa only [baseEqual] using selected

/-- One last fresh cap also preserves any older non-parent physical row. -/
theorem appendFreshChild_records_old (mol : RawMolecule) (parent : Fin mol.atomCount)
    (child : AtomSpec) (center : Nat) (older : center < mol.atomCount)
    (different : parent.val ≠ center) :
    recordNeighbors (appendFreshChild mol parent child) center = recordNeighbors mol center := by
  have targetDifferent : mol.atomCount ≠ center := by omega
  change ((appendFreshChild mol parent child).bonds.filterMap (recordNeighbor? center)) = _
  rw [appendFreshChild_bonds, List.filterMap_append]
  have extra : ([freshBond mol parent] : List RawBond).filterMap (recordNeighbor? center) = [] := by
    rw [List.filterMap_cons]
    have none := recordNeighbor_none (freshBond mol parent) center different targetDifferent
    rw [none]
    rfl
  rw [extra, List.append_nil]
  rfl

/-- Headline: every actual family local offset1..11 has its derived closed physical record row. -/
theorem familyRaw_local_records (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (offset : Nat) (positive : 0 < offset) (bound : offset < 12) :
    recordNeighbors (familyRaw ps) (1 + 12 * i.val + offset) =
      closedLocalRow (1 + 12 * i.val) offset := by
  have indexBound := i.isLt
  have baseCount : family543Base.atomCount = 1 := rfl
  have outsideCap : 1 + 12 * i.val + offset < (blocksResult543 ps family543Base baseFin).atomCount := by
    rw [blocksResult543_atomCount, baseCount]
    omega
  have parentDifferent := blocksParent_avoids_local ps family543Base baseFin i.val offset indexBound positive bound
  have original := blocksResult_records_local ps family543Base family543Base_blockGood.1
    baseFin i.val offset indexBound positive bound
  unfold familyRaw
  dsimp only
  rw [appendFreshChild_records_old _ _ _ _ outsideCap (by simpa only [baseCount] using parentDifferent)]
  simpa only [baseCount] using original



/-- Exact bridge records of every block, including arbitrary later blocks and the final cap. -/
theorem familyRaw_bridge_records (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    recordNeighbors (familyRaw ps) (1 + 12 * i.val + 2) =
      [1 + 12 * i.val, 1 + 12 * i.val + 3, 1 + 12 * i.val + 4, 1 + 12 * i.val + 5] :=
  familyRaw_local_records ps i 2 (by decide) (by decide)

theorem familyRaw_tag_records (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    recordNeighbors (familyRaw ps) (1 + 12 * i.val + 5) =
      [1 + 12 * i.val + 2, 1 + 12 * i.val + 6, 1 + 12 * i.val + 7, 1 + 12 * i.val + 8] :=
  familyRaw_local_records ps i 5 (by decide) (by decide)

theorem familyRaw_methyl_records (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    recordNeighbors (familyRaw ps) (1 + 12 * i.val + 8) =
      [1 + 12 * i.val + 5, 1 + 12 * i.val + 9, 1 + 12 * i.val + 10, 1 + 12 * i.val + 11] :=
  familyRaw_local_records ps i 8 (by decide) (by decide)

/-- The five bridge/methyl hydrogens have exactly their sole carbon parent. -/
theorem familyRaw_comparison_leaf_records (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    recordNeighbors (familyRaw ps) (1 + 12 * i.val + 3) = [1 + 12 * i.val + 2] ∧
    recordNeighbors (familyRaw ps) (1 + 12 * i.val + 4) = [1 + 12 * i.val + 2] ∧
    recordNeighbors (familyRaw ps) (1 + 12 * i.val + 9) = [1 + 12 * i.val + 8] ∧
    recordNeighbors (familyRaw ps) (1 + 12 * i.val + 10) = [1 + 12 * i.val + 8] ∧
    recordNeighbors (familyRaw ps) (1 + 12 * i.val + 11) = [1 + 12 * i.val + 8] := by
  exact ⟨familyRaw_local_records ps i 3 (by decide) (by decide),
    familyRaw_local_records ps i 4 (by decide) (by decide),
    familyRaw_local_records ps i 9 (by decide) (by decide),
    familyRaw_local_records ps i 10 (by decide) (by decide),
    familyRaw_local_records ps i 11 (by decide) (by decide)⟩

theorem familyRaw_tag_leaf_records (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    recordNeighbors (familyRaw ps) (1 + 12 * i.val + 6) = [1 + 12 * i.val + 5] ∧
    recordNeighbors (familyRaw ps) (1 + 12 * i.val + 7) = [1 + 12 * i.val + 5] := by
  exact ⟨familyRaw_local_records ps i 6 (by decide) (by decide),
    familyRaw_local_records ps i 7 (by decide) (by decide)⟩

/-- Fresh raw construction always writes a single edge. -/
theorem appendFreshChild_all_single (mol : RawMolecule) (parent : Fin mol.atomCount)
    (child : AtomSpec) (single : ∀ bond ∈ mol.bonds, bond.kind = .single) :
    ∀ bond ∈ (appendFreshChild mol parent child).bonds, bond.kind = .single := by
  intro bond member
  rw [appendFreshChild_bonds] at member
  rcases List.mem_append.mp member with old | fresh
  · exact single bond old
  · have equal := List.mem_singleton.mp fresh
    subst bond
    rfl

theorem blockAppend_all_single (mol : RawMolecule) (base : Nat)
    (count : mol.atomCount = base) (parent : Fin mol.atomCount)
    (parity : TetrahedralInputParity) (single : ∀ bond ∈ mol.bonds, bond.kind = .single) :
    ∀ bond ∈ (blockAppend mol base count parent parity).bonds, bond.kind = .single := by
  unfold blockAppend
  dsimp only
  repeat (first | apply appendFreshChild_all_single)
  exact single

theorem blocksResult_all_single (ps : List TetrahedralInputParity) (mol : RawMolecule)
    (parent : Fin mol.atomCount) (single : ∀ bond ∈ mol.bonds, bond.kind = .single) :
    ∀ bond ∈ (blocksResult543 ps mol parent).bonds, bond.kind = .single := by
  induction ps generalizing mol parent with
  | nil => exact single
  | cons parity rest ih =>
      exact ih (blockAppend mol mol.atomCount rfl parent parity)
        ⟨mol.atomCount, by rw [blockAppend_atomCount]; omega⟩
        (blockAppend_all_single mol mol.atomCount rfl parent parity single)

theorem familyRaw_all_single (ps : List TetrahedralInputParity) :
    ∀ bond ∈ (familyRaw ps).bonds, bond.kind = .single := by
  unfold familyRaw
  dsimp only
  apply appendFreshChild_all_single
  apply blocksResult_all_single
  intro bond member
  simp [family543Base] at member

/-- Any physical neighbor in the actual family has unit bond order, for arbitrary center indices. -/
theorem familyRaw_incident_order (ps : List TetrahedralInputParity) (center other : Nat)
    (member : other ∈ recordNeighbors (familyRaw ps) center) :
    (familyRaw ps).bondOrder center other = 1 :=
  ChronologicalFamilyPhysicalBridge.all_single_incident_order (familyRaw ps)
    (familyRaw_wellFormed ps) (familyRaw_all_single ps) center other member

/-- Actual bond-valence demand equals the derived record degree. -/
theorem familyRaw_incident_sum (ps : List TetrahedralInputParity) (center : Nat) :
    (familyRaw ps).incidentBondOrderSum center = (recordNeighbors (familyRaw ps) center).length :=
  ChronologicalFamilyPhysicalBridge.all_single_incident_sum (familyRaw ps)
    (familyRaw_all_single ps) center

/-- Direct role lookup in the independent twelve-atom table, with no parser or cursor premise. -/
theorem listGet?_role_blocks (ps : List TetrahedralInputParity) (i offset : Nat)
    (indexBound : i < ps.length) (bound : offset < 12) :
    listGet? (ps.flatMap blockAtoms) (12 * i + offset) =
      some (roleAtom (ps.get ⟨i, indexBound⟩) (roleOfOffset offset)) := by
  induction ps generalizing i with
  | nil => simp at indexBound
  | cons parity rest ih =>
      cases i with
      | zero =>
          simp only [List.flatMap_cons, Nat.mul_zero, Nat.zero_add]
          rw [listGet?_append_left (blockAtoms parity) (rest.flatMap blockAtoms) offset
            (by simpa only [blockAtoms_length] using bound)]
          exact blockAtoms_get parity offset bound
      | succ i =>
          have restBound : i < rest.length := by
            simpa only [List.length_cons, Nat.succ_lt_succ_iff] using indexBound
          have position : 12 * (i + 1) + offset = (blockAtoms parity).length + (12 * i + offset) := by
            rw [blockAtoms_length]
            omega
          rw [List.flatMap_cons, position, listGet?_append_right]
          exact ih i restBound

theorem familyRaw_role_atom (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (offset : Nat) (bound : offset < 12) :
    (familyRaw ps).atomAt? (1 + 12 * i.val + offset) =
      some (roleAtom (ps.get i) (roleOfOffset offset)) := by
  change listGet? (familyRaw ps).atoms (1 + 12 * i.val + offset) = _
  rw [show 1 + 12 * i.val + offset = 1 + (12 * i.val + offset) from Nat.add_assoc _ _ _,
    familyRaw_atoms]
  change listGet? ([hydrogenSpec] ++ (ps.flatMap blockAtoms ++ [hydrogenSpec]))
    ([hydrogenSpec].length + (12 * i.val + offset)) = _
  rw [listGet?_append_right]
  have inside : 12 * i.val + offset < (ps.flatMap blockAtoms).length := by
    rw [flatMap_blockAtoms_length]
    have indexBound := i.isLt
    omega
  rw [listGet?_append_left (ps.flatMap blockAtoms) [hydrogenSpec] _ inside]
  exact listGet?_role_blocks ps i.val offset i.isLt bound

/-- All actual family atoms have ordinary explicit-zero-hydrogen spellings. -/
theorem familyRaw_atom_origin (ps : List TetrahedralInputParity) (atom : AtomSpec)
    (member : atom ∈ (familyRaw ps).atoms) :
    ∃ kind : FamilyAtom, atom = atomSpec kind := by
  rw [familyRaw_atoms] at member
  rcases List.mem_append.mp member with leading | remaining
  · exact ⟨.hydrogen, List.mem_singleton.mp leading⟩
  · rcases List.mem_append.mp remaining with blocks | trailing
    · obtain ⟨parity, _, selected⟩ := List.mem_flatMap.mp blocks
      obtain ⟨role, _, equal⟩ := List.mem_map.mp selected
      subst atom
      cases role <;> first
        | exact ⟨.carbon, rfl⟩
        | exact ⟨.hydrogen, rfl⟩
        | exact ⟨.taggedCarbon parity, rfl⟩
        | exact ⟨.fluorine, rfl⟩
    · exact ⟨.hydrogen, List.mem_singleton.mp trailing⟩

theorem familyRaw_zero_explicit_hydrogens (ps : List TetrahedralInputParity) :
    ∀ atom ∈ (familyRaw ps).atoms, atom.explicitHydrogens? = some 0 := by
  intro atom member
  obtain ⟨kind, rfl⟩ := familyRaw_atom_origin ps atom member
  cases kind <;> rfl

theorem familyRaw_known_elements (ps : List TetrahedralInputParity) :
    ∀ atom ∈ (familyRaw ps).atoms, atom.element ≠ .wildcard := by
  intro atom member
  obtain ⟨kind, rfl⟩ := familyRaw_atom_origin ps atom member
  exact ChronologicalFamilyRuntimeSourceBridge.atomSpec_known_element kind

theorem familyRaw_masses_known (ps : List TetrahedralInputParity) :
    (familyRaw ps).Rule2MassesKnown := by
  intro atom member
  obtain ⟨kind, rfl⟩ := familyRaw_atom_origin ps atom member
  exact ChronologicalFamilyRuntimeSourceBridge.atomSpec_mass_known kind

/-- Element lookup for all twelve actual block roles, not only the selected tagged carbon. -/
theorem familyRaw_role_Z (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (offset : Nat) (bound : offset < 12) :
    (familyRaw ps).atomZAt (1 + 12 * i.val + offset) =
      (roleAtom (ps.get i) (roleOfOffset offset)).element.atomicNumber := by
  unfold atomZAt
  rw [familyRaw_role_atom ps i offset bound]

/-- Carbon roles needed by the interior comparison/cursor domains. -/
theorem familyRaw_interior_carbon_Z (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (familyRaw ps).atomZAt (1 + 12 * i.val) = 6 ∧
    (familyRaw ps).atomZAt (1 + 12 * i.val + 2) = 6 ∧
    (familyRaw ps).atomZAt (1 + 12 * i.val + 5) = 6 ∧
    (familyRaw ps).atomZAt (1 + 12 * i.val + 8) = 6 := by
  exact ⟨familyRaw_role_Z ps i 0 (by decide), familyRaw_role_Z ps i 2 (by decide),
    familyRaw_role_Z ps i 5 (by decide), familyRaw_role_Z ps i 8 (by decide)⟩

/-- The seven hydrogen roles and fluorine role carry the actual low-Z keys. -/
theorem familyRaw_terminal_Z (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (familyRaw ps).atomZAt (1 + 12 * i.val + 1) = 1 ∧
    (familyRaw ps).atomZAt (1 + 12 * i.val + 3) = 1 ∧
    (familyRaw ps).atomZAt (1 + 12 * i.val + 4) = 1 ∧
    (familyRaw ps).atomZAt (1 + 12 * i.val + 6) = 1 ∧
    (familyRaw ps).atomZAt (1 + 12 * i.val + 7) = 9 ∧
    (familyRaw ps).atomZAt (1 + 12 * i.val + 9) = 1 ∧
    (familyRaw ps).atomZAt (1 + 12 * i.val + 10) = 1 ∧
    (familyRaw ps).atomZAt (1 + 12 * i.val + 11) = 1 := by
  exact ⟨familyRaw_role_Z ps i 1 (by decide), familyRaw_role_Z ps i 3 (by decide),
    familyRaw_role_Z ps i 4 (by decide), familyRaw_role_Z ps i 6 (by decide),
    familyRaw_role_Z ps i 7 (by decide), familyRaw_role_Z ps i 9 (by decide),
    familyRaw_role_Z ps i 10 (by decide), familyRaw_role_Z ps i 11 (by decide)⟩

/-- Physical saturation at the three closed carbon sites is derived from records and unit edges. -/
theorem familyRaw_closed_carbon_demand (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (familyRaw ps).incidentBondOrderSum (1 + 12 * i.val + 2) = 4 ∧
    (familyRaw ps).incidentBondOrderSum (1 + 12 * i.val + 5) = 4 ∧
    (familyRaw ps).incidentBondOrderSum (1 + 12 * i.val + 8) = 4 := by
  simp [familyRaw_incident_sum, familyRaw_bridge_records, familyRaw_tag_records,
    familyRaw_methyl_records, List.length_cons, List.length_nil]

/-- Closed four-neighbor rows have no repeated role indices. -/
theorem familyRaw_closed_rows_nodup (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (recordNeighbors (familyRaw ps) (1 + 12 * i.val + 2)).Nodup ∧
    (recordNeighbors (familyRaw ps) (1 + 12 * i.val + 5)).Nodup ∧
    (recordNeighbors (familyRaw ps) (1 + 12 * i.val + 8)).Nodup := by
  rw [familyRaw_bridge_records, familyRaw_tag_records, familyRaw_methyl_records]
  simp (disch := omega)



/-- Exact local bond demand, including all seven hydrogen/fluorine terminals. -/
theorem familyRaw_local_demand (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (offset : Nat) (positive : 0 < offset) (bound : offset < 12) :
    (familyRaw ps).incidentBondOrderSum (1 + 12 * i.val + offset) =
      if offset = 2 ∨ offset = 5 ∨ offset = 8 then 4 else 1 := by
  rw [familyRaw_incident_sum, familyRaw_local_records ps i offset positive bound]
  interval_cases offset <;> rfl

/-- All indices used by the generic interior physical roles are actual bounded family atoms. -/
theorem familyRaw_role_bound (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (offset : Nat) (bound : offset < 12) :
    1 + 12 * i.val + offset < (familyRaw ps).atomCount := by
  rw [familyRaw_atomCount]
  have indexBound := i.isLt
  omega

/-- Pointwise alignment of stored written order with chronological physical record order. -/
def RecordOrderAligned (mol : RawMolecule) : Prop :=
  ∀ center, center < mol.atomCount → mol.writtenNeighbors center = recordNeighbors mol center

/-- Actual raw append's old record row, with its conditional last child made explicit. -/
theorem appendFreshChild_records_at_old (mol : RawMolecule) (parent : Fin mol.atomCount)
    (child : AtomSpec) (center : Nat) (older : center < mol.atomCount) :
    recordNeighbors (appendFreshChild mol parent child) center =
      recordNeighbors mol center ++ (if center = parent.val then [mol.atomCount] else []) := by
  have targetDifferent : mol.atomCount ≠ center := by omega
  change ((appendFreshChild mol parent child).bonds.filterMap (recordNeighbor? center)) = _
  rw [appendFreshChild_bonds, List.filterMap_append]
  by_cases same : center = parent.val
  · subst center
    simp [freshBond, recordNeighbor?]
    rfl
  · have parentDifferent : parent.val ≠ center := Ne.symm same
    simp [freshBond, recordNeighbor?, targetDifferent, parentDifferent, same]
    rfl

/-- The actual fresh row contains exactly its introduction parent. -/
theorem appendFreshChild_records_at_fresh (mol : RawMolecule) (well : mol.WellFormed)
    (parent : Fin mol.atomCount) (child : AtomSpec) :
    recordNeighbors (appendFreshChild mol parent child) mol.atomCount = [parent.val] := by
  have old := recordNeighbors_of_ge_atomCount mol well mol.atomCount (Nat.le_refl _)
  have parentDifferent : parent.val ≠ mol.atomCount := by have bounded := parent.isLt; omega
  change ((appendFreshChild mol parent child).bonds.filterMap (recordNeighbor? mol.atomCount)) = _
  rw [appendFreshChild_bonds, List.filterMap_append]
  change recordNeighbors mol mol.atomCount ++ _ = _
  rw [old]
  simp [freshBond, recordNeighbor?, parentDifferent]

/-- Append derives written order equality from the old independent order invariant. -/
theorem appendFreshChild_record_order (mol : RawMolecule) (well : mol.WellFormed)
    (parent : Fin mol.atomCount) (child : AtomSpec) (aligned : RecordOrderAligned mol) :
    RecordOrderAligned (appendFreshChild mol parent child) := by
  intro center bounded
  have newBound : center < mol.atomCount + 1 := by
    simpa only [appendFreshChild_atomCount] using bounded
  rw [appendFreshChild_writtenNeighbors mol parent child center newBound]
  by_cases older : center < mol.atomCount
  · rw [appendedRow_old mol parent older, appendFreshChild_records_at_old mol parent child center older,
      aligned center older]
  · have fresh : center = mol.atomCount := by omega
    subst center
    rw [appendedRow_fresh mol parent (Nat.lt_irrefl _),
      appendFreshChild_records_at_fresh mol well parent child]

/-- Every one of the twelve actual appends preserves the independent written/record invariant. -/
theorem blockAppend_record_order (mol : RawMolecule) (well : mol.WellFormed)
    (base : Nat) (count : mol.atomCount = base) (parent : Fin mol.atomCount)
    (parity : TetrahedralInputParity) (aligned : RecordOrderAligned mol) :
    RecordOrderAligned (blockAppend mol base count parent parity) := by
  unfold blockAppend
  dsimp only
  repeat' (first | exact well | exact aligned | apply appendFreshChild_record_order |
    apply appendFreshChild_wellFormed)

/-- The entire chronological block fold preserves actual written order. -/
theorem blocksResult_record_order (ps : List TetrahedralInputParity) (mol : RawMolecule)
    (well : mol.WellFormed) (parent : Fin mol.atomCount) (aligned : RecordOrderAligned mol) :
    RecordOrderAligned (blocksResult543 ps mol parent) := by
  induction ps generalizing mol parent with
  | nil => exact aligned
  | cons parity rest ih =>
      let next := blockAppend mol mol.atomCount rfl parent parity
      let nextParent : Fin next.atomCount := ⟨mol.atomCount, by rw [blockAppend_atomCount]; omega⟩
      have nextWell : next.WellFormed := by
        unfold next blockAppend
        dsimp only
        repeat (first | apply appendFreshChild_wellFormed)
        exact well
      have nextAligned := blockAppend_record_order mol well mol.atomCount rfl parent parity aligned
      exact ih next nextWell nextParent nextAligned

/-- Headline: actual stored written rows equal physical record rows for the whole raw family. -/
theorem familyRaw_record_order (ps : List TetrahedralInputParity) :
    RecordOrderAligned (familyRaw ps) := by
  have initial : RecordOrderAligned family543Base := by
    intro center bound
    have zero : center = 0 := by change center < 1 at bound; omega
    subst center
    rfl
  have constructedWell : (blocksResult543 ps family543Base baseFin).WellFormed :=
    (blocksResult543_blockGood ps family543Base baseFin family543Base_blockGood).1
  unfold familyRaw
  dsimp only
  apply appendFreshChild_record_order _ constructedWell
  exact blocksResult_record_order ps family543Base family543Base_blockGood.1 baseFin initial

/-- Actual tag parity's source-order row is preserved in the stored written table. -/
theorem familyRaw_tag_written (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (familyRaw ps).writtenNeighbors (1 + 12 * i.val + 5) =
      [1 + 12 * i.val + 2, 1 + 12 * i.val + 6, 1 + 12 * i.val + 7, 1 + 12 * i.val + 8] := by
  rw [familyRaw_record_order ps _ (familyRaw_role_bound ps i 5 (by decide))]
  exact familyRaw_tag_records ps i

/-- Isotopes are genuinely unspecified in all constructed roles; explicit H=0 is retained. -/
theorem familyRaw_zero_isotope (ps : List TetrahedralInputParity) :
    ∀ atom ∈ (familyRaw ps).atoms, atom.isotope? = none := by
  intro atom member
  obtain ⟨kind, rfl⟩ := familyRaw_atom_origin ps atom member
  cases kind <;> rfl

end TetraStereo.UniversalProof.SecondSphereFamilyPhysicalInstantiation
