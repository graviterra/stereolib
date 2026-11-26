import TetraStereo.Engine.RingBondAdmission

/-! Structural admission invariance when only raw bond-record order changes.
Malformed endpoints, duplicate records and invalid stored neighbor orders are included. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingBondRecordAdmission
open OneCenter

variable {m n : RawMolecule}

theorem writtenNeighbors_perm (bonds : m.bonds.Perm n.bonds)
    (orders : m.neighborOrder = n.neighborOrder) (center : Nat) :
    (m.writtenNeighbors center).Perm (n.writtenNeighbors center) := by
  unfold RawMolecule.writtenNeighbors
  rw [orders]
  cases n.neighborOrder[center]? with
  | some row => exact List.Perm.refl row
  | none => exact bonds.filterMap _

theorem stereochemical_admissible (atoms : m.atoms = n.atoms)
    (bonds : m.bonds.Perm n.bonds) (orders : m.neighborOrder = n.neighborOrder) :
    m.StereochemicalAdmissible ↔ n.StereochemicalAdmissible := by
  have counts : m.atomCount = n.atomCount := congrArg List.length atoms
  have endpoints : m.WellFormed ↔ n.WellFormed := by
    simp only [RawMolecule.WellFormed,RawMolecule.BondEndpointsOK,counts,bonds.mem_iff]
  have unique : m.BondRecordsUnique ↔ n.BondRecordsUnique :=
    (bonds.map RawBond.edgeKey).nodup_iff
  have rows := writtenNeighbors_perm bonds orders
  have nodup : ∀ c, (m.writtenNeighbors c).Nodup ↔ (n.writtenNeighbors c).Nodup :=
    fun c => (rows c).nodup_iff
  have member : ∀ c x, x ∈ m.writtenNeighbors c ↔ x ∈ n.writtenNeighbors c :=
    fun c _ => (rows c).mem_iff
  have exactRows : m.WrittenNeighborExact ↔ n.WrittenNeighborExact := by
    simp only [RawMolecule.WrittenNeighborExact,RawMolecule.writtenNeighborExact?,
      List.all_eq_true,Bool.and_eq_true,decide_eq_true_eq,counts,nodup,member,
      RingBondRecordOrder.bondOrder bonds]
  simp only [RawMolecule.StereochemicalAdmissible,RawMolecule.Admissible,
    endpoints,unique,exactRows]

/-- No validity assumptions are required: both successful admission and structural
rejection are preserved by changing only the order of raw bond records. -/
theorem public_admission (atoms : m.atoms = n.atoms)
    (bonds : m.bonds.Perm n.bonds) (orders : m.neighborOrder = n.neighborOrder)
    (g : SpatialConfiguration) :
    (LocalizedChemicalRing.admitRawSpatial? m g).isSome =
      (LocalizedChemicalRing.admitRawSpatial? n g).isSome := by
  have valid := stereochemical_admissible atoms bonds orders
  by_cases first : m.StereochemicalAdmissible
  · apply Bool.eq_iff_iff.mpr
    exact RingBondAdmission.public_admission atoms bonds first (valid.mp first) g
  · have second : ¬ n.StereochemicalAdmissible := fun h => first (valid.mpr h)
    have badM : m.stereochemicalAdmissible? = false := by
      cases h : m.stereochemicalAdmissible? with
      | false => rfl
      | true => exact (first (m.stereochemicalAdmissible?_eq_true_iff.mp h)).elim
    have badN : n.stereochemicalAdmissible? = false := by
      cases h : n.stereochemicalAdmissible? with
      | false => rfl
      | true => exact (second (n.stereochemicalAdmissible?_eq_true_iff.mp h)).elim
    simp [LocalizedChemicalRing.admitRawSpatial?,badM,badN]

end TetraStereo.Engine.RingBondRecordAdmission
assert_kernel_only TetraStereo.Engine.RingBondRecordAdmission.writtenNeighbors_perm
assert_kernel_only TetraStereo.Engine.RingBondRecordAdmission.stereochemical_admissible
assert_kernel_only TetraStereo.Engine.RingBondRecordAdmission.public_admission
