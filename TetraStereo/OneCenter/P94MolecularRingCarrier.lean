import TetraStereo.OneCenter.CIPP94ConformationCompletePipeline

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Exact molecular carriers for P-94 cyclic conformations

The P-94 plane-side predicates describe geometry, but saturation and unsaturation are facts about
the molecular graph.  This module gives the cyclic atom traversal an exact closing edge, maps that
edge list to the actual `RawMolecule.bondOrder` values, and reflects the resulting finite checks.
In particular, neither crown saturation nor the number of double bonds in a half-chair can be
manufactured by a caller-supplied geometry record.
-/

namespace P94ConformationUnit

/-- Every directed adjacent pair in a closed cyclic traversal.  The last atom is paired with the
first atom.  Degenerate lists are represented literally; the molecular-cycle admission check
below rejects traversals with fewer than three atoms. -/
def cyclicAdjacentPairs (atoms : List ℕ) : List (ℕ × ℕ) :=
  atoms.zip (cyclicSuccessors atoms)

/-- The exact directed edge enumeration belonging to a P-94 physical carrier. -/
def cycleEdges (unit : P94ConformationUnit) : List (ℕ × ℕ) :=
  cyclicAdjacentPairs unit.atoms

@[simp] theorem cyclicAdjacentPairs_nil : cyclicAdjacentPairs [] = [] :=
  rfl

@[simp] theorem cyclicAdjacentPairs_cons (first : ℕ) (rest : List ℕ) :
    cyclicAdjacentPairs (first :: rest) =
      (first :: rest).zip (rest ++ [first]) := by
  simp [cyclicAdjacentPairs, cyclicSuccessors]

/-- Closing a traversal neither drops nor duplicates an edge position. -/
@[simp] theorem cyclicSuccessors_length (atoms : List ℕ) :
    (cyclicSuccessors atoms).length = atoms.length := by
  cases atoms <;> simp [cyclicSuccessors]

@[simp] theorem cyclicAdjacentPairs_length (atoms : List ℕ) :
    (cyclicAdjacentPairs atoms).length = atoms.length := by
  simp [cyclicAdjacentPairs]

@[simp] theorem cycleEdges_length (unit : P94ConformationUnit) :
    unit.cycleEdges.length = unit.atoms.length := by
  simp [cycleEdges]

private theorem zipWith_eq_map_zip {Alpha Beta Gamma : Type*}
    (combine : Alpha → Beta → Gamma) :
    ∀ (left : List Alpha) (right : List Beta),
      List.zipWith combine left right =
        (left.zip right).map (fun pair => combine pair.1 pair.2)
  | [], _ => by simp
  | _ :: _, [] => by simp
  | left :: lefts, right :: rights => by
      simp [zipWith_eq_map_zip combine lefts rights]

/-- The production bond-order ledger is exactly the image of the closed edge enumeration under
the molecule's symmetric bond-order function. -/
theorem cycleBondOrders_eq_map_cycleEdges
    (unit : P94ConformationUnit) (molecule : RawMolecule) :
    unit.cycleBondOrders molecule =
      unit.cycleEdges.map (fun edge => molecule.bondOrder edge.1 edge.2) := by
  unfold cycleBondOrders cycleEdges cyclicAdjacentPairs
  exact zipWith_eq_map_zip molecule.bondOrder unit.atoms (cyclicSuccessors unit.atoms)

/-- There is one actual bond-order entry per atom position, including the closing bond. -/
@[simp] theorem cycleBondOrders_length
    (unit : P94ConformationUnit) (molecule : RawMolecule) :
    (unit.cycleBondOrders molecule).length = unit.atoms.length := by
  rw [cycleBondOrders_eq_map_cycleEdges, List.length_map, cycleEdges_length]

/-- The orientation-independent multiplicity carrier associated with the ordered bond ledger. -/
def cycleBondOrderMultiset
    (unit : P94ConformationUnit) (molecule : RawMolecule) : Multiset BondOrder :=
  Multiset.ofList (unit.cycleBondOrders molecule)

@[simp] theorem cycleBondOrderMultiset_card
    (unit : P94ConformationUnit) (molecule : RawMolecule) :
    (unit.cycleBondOrderMultiset molecule).card = unit.atoms.length := by
  simp [cycleBondOrderMultiset]

/-- Counting double bonds in the multiset is exactly the molecule-derived ring count. -/
@[simp] theorem cycleBondOrderMultiset_count_two
    (unit : P94ConformationUnit) (molecule : RawMolecule) :
    (unit.cycleBondOrderMultiset molecule).count 2 =
      unit.CycleDoubleBondCount molecule := by
  simp [cycleBondOrderMultiset, CycleDoubleBondCount]

theorem cycleDoubleBondCount_eq_count
    (unit : P94ConformationUnit) (molecule : RawMolecule) :
    unit.CycleDoubleBondCount molecule =
      (unit.cycleBondOrders molecule).count 2 :=
  rfl

theorem cycleDoubleBondCount_eq_one_iff
    (unit : P94ConformationUnit) (molecule : RawMolecule) :
    unit.CycleDoubleBondCount molecule = 1 ↔
      (unit.cycleBondOrders molecule).count 2 = 1 :=
  Iff.rfl

/-- Exact graph-relative meaning of molecular saturation, expressed over the ordered ledger. -/
theorem saturatedCyclic_iff_all_cycleBondOrders_single
    (unit : P94ConformationUnit) (molecule : RawMolecule) :
    unit.SaturatedCyclic molecule ↔
      (∀ order ∈ unit.cycleBondOrders molecule, order = 1) ∧
        unit.SaturatedCycleBondKinds molecule :=
  Iff.rfl

/-- Equivalent edge-level form of molecular saturation. -/
theorem saturatedCyclic_iff_all_cycleEdges_single
    (unit : P94ConformationUnit) (molecule : RawMolecule) :
    unit.SaturatedCyclic molecule ↔
      (∀ edge ∈ unit.cycleEdges, molecule.bondOrder edge.1 edge.2 = 1) ∧
        unit.SaturatedCycleBondKinds molecule := by
  constructor
  · intro saturated
    refine ⟨?_, saturated.2⟩
    intro edge edgeMember
    apply saturated.1 (molecule.bondOrder edge.1 edge.2)
    rw [cycleBondOrders_eq_map_cycleEdges]
    exact List.mem_map.mpr ⟨edge, edgeMember, rfl⟩
  · rintro ⟨everyEdge, kinds⟩
    refine ⟨?_, kinds⟩
    intro order orderMember
    rw [cycleBondOrders_eq_map_cycleEdges] at orderMember
    rcases List.mem_map.mp orderMember with ⟨edge, edgeMember, edgeOrder⟩
    subst order
    exact everyEdge edge edgeMember

/-- Executable reflection of the saturated single-bond spelling predicate. -/
def saturatedSingleBondKind? : ParsedBondKind → Bool
  | .single | .up | .down => true
  | .unspecified | .double | .triple | .aromatic => false

@[simp] theorem saturatedSingleBondKind?_eq_true_iff (kind : ParsedBondKind) :
    saturatedSingleBondKind? kind = true ↔ SaturatedSingleBondKind kind := by
  cases kind <;> simp [saturatedSingleBondKind?, SaturatedSingleBondKind]

/-- Executable check retaining the raw bond-kind information erased by `BondOrder`. -/
def saturatedCycleBondKinds? (unit : P94ConformationUnit) (molecule : RawMolecule) : Bool :=
  unit.cycleEdges.all fun edge =>
    molecule.bonds.all fun bond =>
      (!bond.connects edge.1 edge.2) || saturatedSingleBondKind? bond.kind

@[simp] theorem saturatedCycleBondKinds?_eq_true_iff
    (unit : P94ConformationUnit) (molecule : RawMolecule) :
    unit.saturatedCycleBondKinds? molecule = true ↔
      unit.SaturatedCycleBondKinds molecule := by
  constructor
  · intro accepted edge edgeMember bond bondMember connected
    rw [saturatedCycleBondKinds?, List.all_eq_true] at accepted
    have allBonds := accepted edge edgeMember
    rw [List.all_eq_true] at allBonds
    have allowed := allBonds bond bondMember
    rw [Bool.or_eq_true] at allowed
    rcases allowed with disconnected | saturated
    · rw [connected] at disconnected
      simp at disconnected
    · exact (saturatedSingleBondKind?_eq_true_iff bond.kind).mp saturated
  · intro saturated
    rw [saturatedCycleBondKinds?, List.all_eq_true]
    intro edge edgeMember
    rw [List.all_eq_true]
    intro bond bondMember
    rw [Bool.or_eq_true]
    by_cases connected : bond.connects edge.1 edge.2 = true
    · exact .inr ((saturatedSingleBondKind?_eq_true_iff bond.kind).mpr
        (saturated edge edgeMember bond bondMember connected))
    · have disconnected : bond.connects edge.1 edge.2 = false :=
        Bool.eq_false_of_not_eq_true connected
      exact .inl (by simp [disconnected])

/-- Executable reflection of the exact molecular saturation predicate. -/
def saturatedCyclic? (unit : P94ConformationUnit) (molecule : RawMolecule) : Bool :=
  ((unit.cycleBondOrders molecule).all fun order => decide (order = 1)) &&
    unit.saturatedCycleBondKinds? molecule

@[simp] theorem saturatedCyclic?_eq_true_iff
    (unit : P94ConformationUnit) (molecule : RawMolecule) :
    unit.saturatedCyclic? molecule = true ↔ unit.SaturatedCyclic molecule := by
  simp [saturatedCyclic?, SaturatedCyclic]

/-- Executable reflection of the bond kinds admitted in a monounsaturated ring. -/
def monounsaturatedCycleBondKind? : ParsedBondKind → Bool
  | .single | .up | .down | .double => true
  | .unspecified | .triple | .aromatic => false

@[simp] theorem monounsaturatedCycleBondKind?_eq_true_iff (kind : ParsedBondKind) :
    monounsaturatedCycleBondKind? kind = true ↔
      MonounsaturatedCycleBondKind kind := by
  cases kind <;>
    simp [monounsaturatedCycleBondKind?, MonounsaturatedCycleBondKind]

def monounsaturatedCycleBondKinds?
    (unit : P94ConformationUnit) (molecule : RawMolecule) : Bool :=
  unit.cycleEdges.all fun edge =>
    molecule.bonds.all fun bond =>
      (!bond.connects edge.1 edge.2) || monounsaturatedCycleBondKind? bond.kind

@[simp] theorem monounsaturatedCycleBondKinds?_eq_true_iff
    (unit : P94ConformationUnit) (molecule : RawMolecule) :
    unit.monounsaturatedCycleBondKinds? molecule = true ↔
      unit.MonounsaturatedCycleBondKinds molecule := by
  constructor
  · intro accepted edge edgeMember bond bondMember connected
    rw [monounsaturatedCycleBondKinds?, List.all_eq_true] at accepted
    have allBonds := accepted edge edgeMember
    rw [List.all_eq_true] at allBonds
    have allowed := allBonds bond bondMember
    rw [Bool.or_eq_true] at allowed
    rcases allowed with disconnected | admitted
    · rw [connected] at disconnected
      simp at disconnected
    · exact (monounsaturatedCycleBondKind?_eq_true_iff bond.kind).mp admitted
  · intro admitted
    rw [monounsaturatedCycleBondKinds?, List.all_eq_true]
    intro edge edgeMember
    rw [List.all_eq_true]
    intro bond bondMember
    rw [Bool.or_eq_true]
    by_cases connected : bond.connects edge.1 edge.2 = true
    · exact .inr ((monounsaturatedCycleBondKind?_eq_true_iff bond.kind).mpr
        (admitted edge edgeMember bond bondMember connected))
    · have disconnected : bond.connects edge.1 edge.2 = false :=
        Bool.eq_false_of_not_eq_true connected
      exact .inl (by simp [disconnected])

/-- Executable exact check that a cyclic carrier contains precisely one double bond and no other
unsaturated or unresolved cyclic bond kind. -/
def monounsaturatedCyclic?
    (unit : P94ConformationUnit) (molecule : RawMolecule) : Bool :=
  decide (unit.CycleDoubleBondCount molecule = 1) &&
    unit.monounsaturatedCycleBondKinds? molecule

@[simp] theorem monounsaturatedCyclic?_eq_true_iff
    (unit : P94ConformationUnit) (molecule : RawMolecule) :
    unit.monounsaturatedCyclic? molecule = true ↔
      unit.MonounsaturatedCyclic molecule := by
  simp [monounsaturatedCyclic?, MonounsaturatedCyclic]

/-- Independent finite molecular-cycle admission.  It validates the atom ledger and every
enumerated closing/consecutive edge directly against positive molecular bond order. -/
def CycleCarrier (unit : P94ConformationUnit) (molecule : RawMolecule) : Prop :=
  3 ≤ unit.atoms.length ∧
  unit.atoms.Nodup ∧
  (∀ atom ∈ unit.atoms, atom < molecule.atomCount) ∧
  ∀ edge ∈ unit.cycleEdges, 0 < molecule.bondOrder edge.1 edge.2

/-- Executable finite check of `CycleCarrier`. -/
def cycleCarrier? (unit : P94ConformationUnit) (molecule : RawMolecule) : Bool :=
  decide (3 ≤ unit.atoms.length) &&
  decide unit.atoms.Nodup &&
  unit.atoms.all (fun atom => decide (atom < molecule.atomCount)) &&
  unit.cycleEdges.all (fun edge => decide (0 < molecule.bondOrder edge.1 edge.2))

@[simp] theorem cycleCarrier?_eq_true_iff
    (unit : P94ConformationUnit) (molecule : RawMolecule) :
    unit.cycleCarrier? molecule = true ↔ unit.CycleCarrier molecule := by
  simp only [cycleCarrier?, CycleCarrier, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true]
  tauto

/-- Validate a molecular cycle and, on success, return exactly its actual bond-order ledger. -/
def validatedCycleBondOrders?
    (unit : P94ConformationUnit) (molecule : RawMolecule) : Option (List BondOrder) :=
  if unit.cycleCarrier? molecule = true then
    some (unit.cycleBondOrders molecule)
  else
    none

theorem validatedCycleBondOrders?_eq_some_iff
    (unit : P94ConformationUnit) (molecule : RawMolecule) (orders : List BondOrder) :
    unit.validatedCycleBondOrders? molecule = some orders ↔
      unit.CycleCarrier molecule ∧ unit.cycleBondOrders molecule = orders := by
  simp [validatedCycleBondOrders?, cycleCarrier?_eq_true_iff]

theorem validatedCycleBondOrders?_eq_none_iff
    (unit : P94ConformationUnit) (molecule : RawMolecule) :
    unit.validatedCycleBondOrders? molecule = none ↔
      ¬unit.CycleCarrier molecule := by
  simp [validatedCycleBondOrders?, cycleCarrier?_eq_true_iff]

/-- A successful validation returns one entry per cyclic atom position. -/
theorem validatedCycleBondOrders?_length
    (unit : P94ConformationUnit) (molecule : RawMolecule) (orders : List BondOrder)
    (computed : unit.validatedCycleBondOrders? molecule = some orders) :
    orders.length = unit.atoms.length := by
  have exactOrders :=
    (unit.validatedCycleBondOrders?_eq_some_iff molecule orders).mp computed
  rw [← exactOrders.2]
  exact unit.cycleBondOrders_length molecule

end P94ConformationUnit

end TetraStereo.OneCenter
