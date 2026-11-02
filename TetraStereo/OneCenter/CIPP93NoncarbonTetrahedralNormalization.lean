import TetraStereo.OneCenter.P93NoncarbonTetrahedra
import TetraStereo.OneCenter.CIPStereogenicPerceptionConformance
import TetraStereo.OneCenter.ProductionCIPRule1aGraphRealization
import TetraStereo.OneCenter.RawSourceHydrogenValence

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace TetraStereo.OneCenter
namespace BlueBookP93.NoncarbonTetrahedra.Production

/-!
# P-93.2 effective molecular graph

P-93.2 contains a genuine exception to ordinary multiple-bond expansion.  At a tetrahedral amine
or phosphane oxide the oxygen is the fourth atom and its bonding formalism is irrelevant.  In
phosphates, phosphonates, sulfates, sulfonates, and the stated selenium/tellurium analogues, a
conventionally written oxo double bond is treated as one single ligand edge and formal-charge
placement is ignored when configuration is determined.

This module turns that prose into a representation quotient before the ordinary P-92 digraph is
built.  The transformation is finite and executable.  It is deliberately restricted to a
four-physical-neighbour N/P/S/Se/Te center (written neighbours plus stored inline hydrogens) and an
oxygen edge; three-coordinate sulfoxides and other P-93.3 units therefore do not enter this rule.

The production entry point `normalizeRawMoleculeP93` first freezes each atom's exact *source*
hydrogen count (`RawMolecule.freezeSourceHydrogenCounts`), then applies the quotient, then runs the
ordinary chemistry normalizer.  Freezing must precede the quotient: lowering an effective oxo
multiple bond changes the hydrogen inventory implied by the written bond orders.  On the frozen
input the effective oxo-center gate counts `writtenNeighbors.length + spec.explicitHydrogens?.getD
0`, so a tetrahedral phosphane oxide written `P(=O)(C)(N)` is admitted via its one source hydrogen
rather than rejected for having only three written neighbours.  The inserted packet below records
the resulting hydrogen-aware representation theory; the whole-pipeline analyzer theorems carry
explicit-hydrogen-domain premises, because an unbracketed center can be effective under the written
hydrogen policy yet not under its filled source count.
-/

/-- Elements for which P-93.2.3--.5 give the oxo-edge representation rule. -/
def oxoCenterElement : Element → Bool
  | .N | .P | .S | .Se | .Te => true
  | _ => false

/-- Concrete production elements denoted by every P-93.2.2 onium family. -/
def onicElement : OnicCenter → Element
  | .azanium => .N
  | .phosphanium => .P
  | .arsanium => .As
  | .stibanium => .Sb
  | .bismuthanium => .Bi

def oxideElement : OxideCenter → Element
  | .amineOxide => .N
  | .phosphaneOxide => .P

def chalcogenOxoElement : ChalcogenOxoFamily → Element
  | .sulfate | .sulfonate => .S
  | .selenate | .selenonate => .Se
  | .tellurate | .telluronate => .Te
  | .related => .S

def noncarbonGroup14Element : NoncarbonGroup14Center → Element
  | .silicon => .Si
  | .germanium => .Ge
  | .tin => .Sn
  | .lead => .Pb

@[simp] theorem onicElement_supported (family : OnicCenter) :
    RawMolecule.centreElementSupported (onicElement family) = true := by
  cases family <;> rfl

@[simp] theorem oxideElement_supported (family : OxideCenter) :
    RawMolecule.centreElementSupported (oxideElement family) = true := by
  cases family <;> rfl

@[simp] theorem oxideElement_effective (family : OxideCenter) :
    oxoCenterElement (oxideElement family) = true := by
  cases family <;> rfl

@[simp] theorem chalcogenOxoElement_supported (family : ChalcogenOxoFamily) :
    RawMolecule.centreElementSupported (chalcogenOxoElement family) = true := by
  cases family <;> rfl

@[simp] theorem chalcogenOxoElement_effective (family : ChalcogenOxoFamily) :
    oxoCenterElement (chalcogenOxoElement family) = true := by
  cases family <;> rfl

@[simp] theorem noncarbonGroup14Element_supported (family : NoncarbonGroup14Center) :
    RawMolecule.centreElementSupported (noncarbonGroup14Element family) = true := by
  cases family <;> rfl

/-- Exact production element inventory named by P-93.2. -/
def p93NoncarbonElements : List Element :=
  [.N, .P, .As, .Sb, .Bi, .S, .Se, .Te, .Si, .Ge, .Sn, .Pb]

theorem p93NoncarbonElements_nodup : p93NoncarbonElements.Nodup := by
  decide

theorem p93NoncarbonElements_all_supported :
    p93NoncarbonElements.all RawMolecule.centreElementSupported = true := by
  decide

theorem p93NoncarbonElements_all_have_rule2_mass :
    p93NoncarbonElements.all
      (fun element => (RawMolecule.rule2MassPico? element none).isSome) = true := by
  decide

/-- Executable oxygen lookup at one raw atom index. -/
def oxygenAt? (mol : RawMolecule) (atom : Nat) : Bool :=
  (mol.atomAt? atom).any fun spec => spec.element == .O

/-- The structural P-93.2 oxo-center boundary used by normalization.

The four-physical-neighbour test counts the written neighbours plus the stored inline hydrogen
count.  On the source-hydrogen-frozen input produced by `normalizeRawMoleculeP93` that stored count
is exactly the written source hydrogen count, so `P(=O)(C)(N)` (three written neighbours, one
source hydrogen) is admitted while a three-coordinate sulfoxide (three written neighbours, no source
hydrogen) is not.  Authority-facing admission subsequently requires `WrittenNeighborExact`, so
malformed hand-written neighbour rows cannot create a certified center. -/
def effectiveOxoCenter? (mol : RawMolecule) (center : Nat) : Bool :=
  (mol.atomAt? center).any fun spec =>
    oxoCenterElement spec.element &&
      ((mol.writtenNeighbors center).length + spec.explicitHydrogens?.getD 0 == 4)

/-- Independent proposition denoted by `effectiveOxoCenter?`. -/
def EffectiveOxoCenter (mol : RawMolecule) (center : Nat) : Prop :=
  ∃ spec, mol.atomAt? center = some spec ∧
    oxoCenterElement spec.element = true ∧
    (mol.writtenNeighbors center).length + spec.explicitHydrogens?.getD 0 = 4

@[simp] theorem effectiveOxoCenter?_eq_true_iff
    (mol : RawMolecule) (center : Nat) :
    effectiveOxoCenter? mol center = true ↔ EffectiveOxoCenter mol center := by
  cases observed : mol.atomAt? center with
  | none => simp [effectiveOxoCenter?, EffectiveOxoCenter, observed]
  | some spec =>
      simp [effectiveOxoCenter?, EffectiveOxoCenter, observed]

/-- An edge to which the P-93.2 single-ligand oxo convention applies. -/
def effectiveOxoBond? (mol : RawMolecule) (bond : RawBond) : Bool :=
  (effectiveOxoCenter? mol bond.source && oxygenAt? mol bond.target) ||
    (effectiveOxoCenter? mol bond.target && oxygenAt? mol bond.source)

/-- Independent, orientation-free meaning of an effective P-93.2 oxo edge. -/
def EffectiveOxoBond (mol : RawMolecule) (bond : RawBond) : Prop :=
  (EffectiveOxoCenter mol bond.source ∧
      ∃ oxygen, mol.atomAt? bond.target = some oxygen ∧ oxygen.element = .O) ∨
    (EffectiveOxoCenter mol bond.target ∧
      ∃ oxygen, mol.atomAt? bond.source = some oxygen ∧ oxygen.element = .O)

@[simp] theorem oxygenAt?_eq_true_iff (mol : RawMolecule) (atom : Nat) :
    oxygenAt? mol atom = true ↔
      ∃ oxygen, mol.atomAt? atom = some oxygen ∧ oxygen.element = .O := by
  cases observed : mol.atomAt? atom with
  | none => simp [oxygenAt?, observed]
  | some oxygen =>
      simp [oxygenAt?, observed]

@[simp] theorem effectiveOxoBond?_eq_true_iff (mol : RawMolecule) (bond : RawBond) :
    effectiveOxoBond? mol bond = true ↔ EffectiveOxoBond mol bond := by
  simp [effectiveOxoBond?, EffectiveOxoBond, Bool.and_eq_true, Bool.or_eq_true]

/-- Atoms whose formal charge is a representational choice ignored by P-93.2: the effective oxo
center and the oxygen endpoint of each of its effective oxo edges. -/
def chargeInsensitiveAtom? (mol : RawMolecule) (atom : Nat) : Bool :=
  mol.bonds.any fun bond =>
    effectiveOxoBond? mol bond && (bond.source == atom || bond.target == atom)

/-- Elements which can occupy an endpoint of an effective oxo edge.  Including this local type
check in the atom map ensures that an invalid index/atom pairing can never erase the charge of an
unrelated element such as boron. -/
def chargeNormalizedElement : Element → Bool
  | .N | .O | .P | .S | .Se | .Te => true
  | _ => false

/-- Canonical atom view for P-93.2 configuration. -/
def normalizeAtom (mol : RawMolecule) (index : Nat) (atom : AtomSpec) : AtomSpec :=
  if chargeInsensitiveAtom? mol index && chargeNormalizedElement atom.element then
    { atom with charge := 0 }
  else atom

/-- Index-aware finite atom-map. -/
def normalizeAtomsAux (mol : RawMolecule) : Nat → List AtomSpec → List AtomSpec
  | _, [] => []
  | index, atom :: rest =>
      normalizeAtom mol index atom :: normalizeAtomsAux mol (index + 1) rest

def normalizeAtoms (mol : RawMolecule) : List AtomSpec :=
  normalizeAtomsAux mol 0 mol.atoms

/-- Canonical edge view for P-93.2 configuration.  Every written bonding formalism on an effective
oxo edge has one single-bond representative. -/
def normalizeBond (mol : RawMolecule) (bond : RawBond) : RawBond :=
  if effectiveOxoBond? mol bond then { bond with kind := .single } else bond

/-- The effective raw molecule consumed by the ordinary P-92 digraph and descriptor pipeline. -/
def normalize (mol : RawMolecule) : RawMolecule where
  atoms := normalizeAtoms mol
  bonds := mol.bonds.map (normalizeBond mol)
  neighborOrder := mol.neighborOrder
  introductionPredecessors := mol.introductionPredecessors

@[simp] theorem normalizeAtom_element (mol : RawMolecule) (index : Nat) (atom : AtomSpec) :
    (normalizeAtom mol index atom).element = atom.element := by
  by_cases insensitive : chargeInsensitiveAtom? mol index = true <;>
    by_cases eligible : chargeNormalizedElement atom.element = true <;>
      simp [normalizeAtom, insensitive, eligible]

@[simp] theorem normalizeAtom_isotope (mol : RawMolecule) (index : Nat) (atom : AtomSpec) :
    (normalizeAtom mol index atom).isotope? = atom.isotope? := by
  by_cases insensitive : chargeInsensitiveAtom? mol index = true <;>
    by_cases eligible : chargeNormalizedElement atom.element = true <;>
      simp [normalizeAtom, insensitive, eligible]

@[simp] theorem normalizeAtom_tetrahedral (mol : RawMolecule) (index : Nat) (atom : AtomSpec) :
    (normalizeAtom mol index atom).tetrahedral? = atom.tetrahedral? := by
  by_cases insensitive : chargeInsensitiveAtom? mol index = true <;>
    by_cases eligible : chargeNormalizedElement atom.element = true <;>
      simp [normalizeAtom, insensitive, eligible]

@[simp] theorem normalizeAtom_explicitHydrogens
    (mol : RawMolecule) (index : Nat) (atom : AtomSpec) :
    (normalizeAtom mol index atom).explicitHydrogens = atom.explicitHydrogens := by
  by_cases insensitive : chargeInsensitiveAtom? mol index = true <;>
    by_cases eligible : chargeNormalizedElement atom.element = true <;>
      simp [normalizeAtom, insensitive, eligible, AtomSpec.explicitHydrogens]

theorem normalizeAtomsAux_length (mol : RawMolecule) (index : Nat) (atoms : List AtomSpec) :
    (normalizeAtomsAux mol index atoms).length = atoms.length := by
  induction atoms generalizing index with
  | nil => rfl
  | cons atom rest ih => simp [normalizeAtomsAux, ih]

@[simp] theorem normalize_atoms_length (mol : RawMolecule) :
    (normalize mol).atoms.length = mol.atoms.length := by
  exact normalizeAtomsAux_length mol 0 mol.atoms

@[simp] theorem normalize_atomCount (mol : RawMolecule) :
    (normalize mol).atomCount = mol.atomCount := by
  exact normalize_atoms_length mol

theorem listGet?_normalizeAtomsAux (mol : RawMolecule) (offset : Nat)
    (atoms : List AtomSpec) (index : Nat) :
    listGet? (normalizeAtomsAux mol offset atoms) index =
      (listGet? atoms index).map (normalizeAtom mol (offset + index)) := by
  induction atoms generalizing offset index with
  | nil => simp [normalizeAtomsAux, listGet?]
  | cons atom rest ih =>
      cases index with
      | zero => simp [normalizeAtomsAux, listGet?]
      | succ index =>
          simpa [normalizeAtomsAux, listGet?, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using ih (offset + 1) index

@[simp] theorem normalize_atomAt? (mol : RawMolecule) (index : Nat) :
    (normalize mol).atomAt? index =
      (mol.atomAt? index).map (normalizeAtom mol index) := by
  simp [RawMolecule.atomAt?, normalize, normalizeAtoms,
    listGet?_normalizeAtomsAux]

@[simp] theorem normalizeAtomsAux_rule2MassCheck (mol : RawMolecule)
    (offset : Nat) (atoms : List AtomSpec) :
    (normalizeAtomsAux mol offset atoms).all
        (fun atom => (RawMolecule.rule2MassPico? atom.element atom.isotope?).isSome) =
      atoms.all
        (fun atom => (RawMolecule.rule2MassPico? atom.element atom.isotope?).isSome) := by
  induction atoms generalizing offset with
  | nil => rfl
  | cons atom rest ih =>
      simp [normalizeAtomsAux, ih]

@[simp] theorem normalize_rule2MassesKnown? (mol : RawMolecule) :
    (normalize mol).rule2MassesKnown? = mol.rule2MassesKnown? := by
  simp [RawMolecule.rule2MassesKnown?, normalize, normalizeAtoms]

@[simp] theorem normalize_rule2MassesKnown (mol : RawMolecule) :
    (normalize mol).Rule2MassesKnown ↔ mol.Rule2MassesKnown := by
  rw [← (normalize mol).rule2MassesKnown?_eq_true_iff,
    ← mol.rule2MassesKnown?_eq_true_iff, normalize_rule2MassesKnown?]

@[simp] theorem normalizeBond_source (mol : RawMolecule) (bond : RawBond) :
    (normalizeBond mol bond).source = bond.source := by
  by_cases effective : effectiveOxoBond? mol bond = true <;>
    simp [normalizeBond, effective]

@[simp] theorem normalizeBond_target (mol : RawMolecule) (bond : RawBond) :
    (normalizeBond mol bond).target = bond.target := by
  by_cases effective : effectiveOxoBond? mol bond = true <;>
    simp [normalizeBond, effective]

@[simp] theorem normalizeBond_edgeKey (mol : RawMolecule) (bond : RawBond) :
    (normalizeBond mol bond).edgeKey = bond.edgeKey := by
  simp [RawBond.edgeKey]

@[simp] theorem normalizeBond_connects (mol : RawMolecule) (bond : RawBond)
    (left right : Nat) :
    (normalizeBond mol bond).connects left right = bond.connects left right := by
  simp [RawBond.connects]

/-- The source's single-ligand instruction is realized literally. -/
theorem normalizeBond_kind_eq_single_of_effective
    (mol : RawMolecule) (bond : RawBond) (effective : EffectiveOxoBond mol bond) :
    (normalizeBond mol bond).kind = .single := by
  simp [normalizeBond, (effectiveOxoBond?_eq_true_iff mol bond).2 effective]

/-- Bond spelling is irrelevant on an effective oxo edge: every possible parsed bonding
formalism has the same canonical single-edge view. -/
theorem effective_oxo_bond_formalism_irrelevant
    (mol : RawMolecule) (bond : RawBond) (effective : EffectiveOxoBond mol bond)
    (first second : ParsedBondKind) :
    normalizeBond mol { bond with kind := first } =
      normalizeBond mol { bond with kind := second } := by
  have firstEffective : EffectiveOxoBond mol { bond with kind := first } := by
    simpa [EffectiveOxoBond] using effective
  have secondEffective : EffectiveOxoBond mol { bond with kind := second } := by
    simpa [EffectiveOxoBond] using effective
  simp [normalizeBond,
    (effectiveOxoBond?_eq_true_iff mol { bond with kind := first }).2 firstEffective,
    (effectiveOxoBond?_eq_true_iff mol { bond with kind := second }).2 secondEffective]

/-- Formal charge is erased exactly on the P-93.2-insensitive atom set. -/
theorem normalizeAtom_charge_zero_of_insensitive
    (mol : RawMolecule) (index : Nat) (atom : AtomSpec)
    (insensitive : chargeInsensitiveAtom? mol index = true)
    (eligible : chargeNormalizedElement atom.element = true) :
    (normalizeAtom mol index atom).charge = 0 := by
  simp [normalizeAtom, insensitive, eligible]

@[simp] theorem normalizeAtom_allowedValences
    (mol : RawMolecule) (index : Nat) (atom : AtomSpec) :
    (normalizeAtom mol index atom).allowedValences = atom.allowedValences := by
  cases elementEq : atom.element <;>
    by_cases insensitive : chargeInsensitiveAtom? mol index = true <;>
      simp [normalizeAtom, insensitive, chargeNormalizedElement,
        AtomSpec.allowedValences, Element.allowedValences, elementEq]

/-- Every parsed bond kind denotes a positive constitutional edge. -/
theorem parsedBondKind_order_pos (kind : ParsedBondKind) : 0 < kind.order := by
  cases kind <;> decide

theorem normalizeBond_order_le (mol : RawMolecule) (bond : RawBond) :
    (normalizeBond mol bond).kind.order ≤ bond.kind.order := by
  by_cases effective : effectiveOxoBond? mol bond = true
  · simp [normalizeBond, effective]
    exact parsedBondKind_order_pos bond.kind
  · simp [normalizeBond, effective]

@[simp] theorem normalize_bond_edgeKeys (mol : RawMolecule) :
    (normalize mol).bonds.map RawBond.edgeKey = mol.bonds.map RawBond.edgeKey := by
  simp [normalize, List.map_map, Function.comp_def]

/-- Normalization preserves structural endpoint admission. -/
theorem normalize_wellFormed (mol : RawMolecule) : mol.WellFormed → (normalize mol).WellFormed := by
  intro wellFormed bond member
  obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
  have sourceOK := wellFormed source sourceMember
  simpa [RawMolecule.BondEndpointsOK] using sourceOK

/-- Normalization preserves the occurrence-sensitive unique-edge contract. -/
theorem normalize_bondRecordsUnique (mol : RawMolecule) :
    mol.BondRecordsUnique → (normalize mol).BondRecordsUnique := by
  intro unique
  simpa [RawMolecule.BondRecordsUnique, normalize_bond_edgeKeys] using unique

/-- P-93.2 changes multiplicity, never constitutional adjacency. -/
theorem normalize_bondOrder_pos_iff (mol : RawMolecule) (left right : Nat) :
    0 < (normalize mol).bondOrder left right ↔ 0 < mol.bondOrder left right := by
  by_cases distinct : left = right
  · subst right
    simp [RawMolecule.bondOrder_self]
  · rw [RawMolecule.bondOrder_pos_iff_exists_bond _ distinct,
      RawMolecule.bondOrder_pos_iff_exists_bond _ distinct]
    constructor
    · rintro ⟨bond, member, connects⟩
      obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
      exact ⟨source, sourceMember, by simpa using connects⟩
    · rintro ⟨bond, member, connects⟩
      exact ⟨normalizeBond mol bond, List.mem_map.mpr ⟨bond, member, rfl⟩,
        by simpa using connects⟩

@[simp] theorem normalize_writtenNeighbors (mol : RawMolecule) (index : Nat) :
    (normalize mol).writtenNeighbors index = mol.writtenNeighbors index := by
  unfold RawMolecule.writtenNeighbors
  cases observed : mol.neighborOrder[index]? with
  | some order => simp [normalize, observed]
  | none =>
      simp only [normalize, observed, List.filterMap_map]
      congr 1
      funext bond
      simp

/-- Exact parity frames survive the effective-graph quotient. -/
theorem normalize_writtenNeighborExact (mol : RawMolecule) :
    mol.WrittenNeighborExact → (normalize mol).WrittenNeighborExact := by
  intro exact
  apply RawMolecule.WrittenNeighborExact.of_at
  intro center
  let sourceCenter : Fin mol.atomCount :=
    ⟨center.val, by simpa using center.isLt⟩
  have clauses := RawMolecule.WrittenNeighborExact.at mol exact sourceCenter
  refine ⟨?_, ?_, ?_⟩
  · simpa [sourceCenter] using clauses.1
  · intro ligand member
    rw [normalize_atomCount]
    exact clauses.2.1 ligand (by simpa [sourceCenter] using member)
  · intro ligand
    let sourceLigand : Fin mol.atomCount :=
      ⟨ligand.val, by simpa using ligand.isLt⟩
    have clause := clauses.2.2 sourceLigand
    simpa [sourceCenter, sourceLigand, normalize_bondOrder_pos_iff] using clause

theorem normalize_admissible (mol : RawMolecule) :
    mol.Admissible → (normalize mol).Admissible := by
  rintro ⟨wellFormed, unique⟩
  exact ⟨normalize_wellFormed mol wellFormed,
    normalize_bondRecordsUnique mol unique⟩

/-- The quotient is safe to place before molecule-to-digraph construction: it preserves the full
structural/parity admission boundary. -/
theorem normalize_stereochemicalAdmissible (mol : RawMolecule) :
    mol.StereochemicalAdmissible → (normalize mol).StereochemicalAdmissible := by
  rintro ⟨admissible, exact⟩
  exact ⟨normalize_admissible mol admissible,
    normalize_writtenNeighborExact mol exact⟩

private theorem normalizeIncidentBondOrderFold_le (mol : RawMolecule) (index : Nat) :
    ∀ (bonds : List RawBond) (normalizedTotal sourceTotal : Nat),
      normalizedTotal ≤ sourceTotal →
      (bonds.map (normalizeBond mol)).foldl
          (fun total bond =>
            if bond.source == index || bond.target == index then
              total + bond.kind.order else total)
          normalizedTotal ≤
        bonds.foldl
          (fun total bond =>
            if bond.source == index || bond.target == index then
              total + bond.kind.order else total)
          sourceTotal
  | [], _, _, totals => totals
  | bond :: rest, normalizedTotal, sourceTotal, totals => by
      simp only [List.map_cons, List.foldl_cons]
      have normalizedIncident :
          ((normalizeBond mol bond).source == index ||
              (normalizeBond mol bond).target == index) =
            (bond.source == index || bond.target == index) := by
        simp only [normalizeBond_source, normalizeBond_target]
      by_cases incident : bond.source == index || bond.target == index
      · rw [normalizedIncident, if_pos incident, if_pos incident]
        apply normalizeIncidentBondOrderFold_le mol index rest
        exact Nat.add_le_add totals (normalizeBond_order_le mol bond)
      · rw [normalizedIncident, if_neg incident, if_neg incident]
        exact normalizeIncidentBondOrderFold_le mol index rest
          normalizedTotal sourceTotal totals

/-- Replacing an effective multiple bond by its mandated single edge can only lower the parser's
numeric valence demand. -/
theorem normalize_incidentBondOrderSum_le (mol : RawMolecule) (index : Nat) :
    (normalize mol).incidentBondOrderSum index ≤ mol.incidentBondOrderSum index := by
  unfold RawMolecule.incidentBondOrderSum
  exact normalizeIncidentBondOrderFold_le mol index mol.bonds 0 0 (Nat.le_refl 0)

theorem normalize_usedValenceAt_le (mol : RawMolecule) (index : Nat) :
    (normalize mol).usedValenceAt index ≤ mol.usedValenceAt index := by
  unfold RawMolecule.usedValenceAt
  rw [normalize_atomAt?]
  cases observed : mol.atomAt? index with
  | none => simp
  | some atom =>
      simp only [Option.map_some]
      simpa only [normalizeAtom_explicitHydrogens] using
        Nat.add_le_add_left (normalize_incidentBondOrderSum_le mol index)
          atom.explicitHydrogens

/-- Every source valence certificate remains valid after the P-93.2 quotient. -/
theorem normalize_valenceOK (mol : RawMolecule) :
    mol.ValenceOK → (normalize mol).ValenceOK := by
  intro valid index normalizedAtom normalizedLookup
  rw [normalize_atomAt?] at normalizedLookup
  cases sourceLookup : mol.atomAt? index with
  | none => simp [sourceLookup] at normalizedLookup
  | some atom =>
      simp [sourceLookup] at normalizedLookup
      subst normalizedAtom
      obtain ⟨allowed, allowedMember, sourceBound⟩ := valid index atom sourceLookup
      exact ⟨allowed, by simpa using allowedMember,
        (normalize_usedValenceAt_le mol index).trans sourceBound⟩

private theorem normalizeUnspecifiedIncidentFold_eq (mol : RawMolecule) (index : Nat) :
    ∀ (bonds : List RawBond) (total : Nat),
      (bonds.map mol.normalizeUnspecifiedBond).foldl
          (fun sum bond =>
            if bond.source == index || bond.target == index then
              sum + bond.kind.order else sum)
          total =
        bonds.foldl
          (fun sum bond =>
            if bond.source == index || bond.target == index then
              sum + bond.kind.order else sum)
          total
  | [], _ => rfl
  | bond :: rest, total => by
      simp only [List.map_cons, List.foldl_cons]
      have incidence :
          ((mol.normalizeUnspecifiedBond bond).source == index ||
              (mol.normalizeUnspecifiedBond bond).target == index) =
            (bond.source == index || bond.target == index) := by
        simp only [RawMolecule.normalizeUnspecifiedBond_source,
          RawMolecule.normalizeUnspecifiedBond_target]
      rw [incidence, RawMolecule.normalizeUnspecifiedBond_order]
      exact normalizeUnspecifiedIncidentFold_eq mol index rest _

@[simp] theorem normalizeUnspecifiedBonds_incidentBondOrderSum
    (mol : RawMolecule) (index : Nat) :
    mol.normalizeUnspecifiedBonds.incidentBondOrderSum index =
      mol.incidentBondOrderSum index := by
  unfold RawMolecule.incidentBondOrderSum
  exact normalizeUnspecifiedIncidentFold_eq mol index mol.bonds 0

@[simp] theorem normalizeUnspecifiedBonds_usedValenceAt
    (mol : RawMolecule) (index : Nat) :
    mol.normalizeUnspecifiedBonds.usedValenceAt index = mol.usedValenceAt index := by
  unfold RawMolecule.usedValenceAt
  have atomAtEq : mol.normalizeUnspecifiedBonds.atomAt? index = mol.atomAt? index := rfl
  rw [atomAtEq]
  cases mol.atomAt? index <;>
    simp only [normalizeUnspecifiedBonds_incidentBondOrderSum]

theorem normalizeUnspecifiedBonds_valenceOK (mol : RawMolecule) :
    mol.ValenceOK → mol.normalizeUnspecifiedBonds.ValenceOK := by
  intro valid index atom lookup
  obtain ⟨allowed, member, bound⟩ := valid index atom
    (by simpa [RawMolecule.normalizeUnspecifiedBonds,
      RawMolecule.atomAt?] using lookup)
  exact ⟨allowed, member, by simpa using bound⟩

/-- The representation quotient itself.  Two raw spellings are P-93.2-equivalent exactly when
their canonical effective atom, bond, and parity-order views agree. -/
structure RepresentationEquivalent (left right : RawMolecule) : Prop where
  atoms : normalizeAtoms left = normalizeAtoms right
  bonds : left.bonds.map (normalizeBond left) = right.bonds.map (normalizeBond right)
  neighborOrder : left.neighborOrder = right.neighborOrder
  introductionPredecessors : left.introductionPredecessors = right.introductionPredecessors

theorem normalize_eq_of_representationEquivalent {left right : RawMolecule}
    (equivalent : RepresentationEquivalent left right) :
    normalize left = normalize right := by
  rcases equivalent with ⟨atoms, bonds, neighbors, predecessors⟩
  cases left with
  | mk leftAtoms leftBonds leftNeighbors leftPredecessors =>
      cases right with
      | mk rightAtoms rightBonds rightNeighbors rightPredecessors =>
          simpa only [normalize, RawMolecule.mk.injEq] using
            And.intro atoms (And.intro bonds (And.intro neighbors predecessors))

theorem representationEquivalent_iff_normalize_eq (left right : RawMolecule) :
    RepresentationEquivalent left right ↔ normalize left = normalize right := by
  constructor
  · exact normalize_eq_of_representationEquivalent
  · intro equal
    have atoms := congrArg RawMolecule.atoms equal
    have bonds := congrArg RawMolecule.bonds equal
    have neighbors := congrArg RawMolecule.neighborOrder equal
    have predecessors := congrArg RawMolecule.introductionPredecessors equal
    exact ⟨atoms, bonds, neighbors, predecessors⟩

/-! ## Whole-molecule bond-formalism invariance -/

/-- Replace every applicable oxo bond by an arbitrary parsed bonding formalism. -/
def respellBond (mol : RawMolecule) (kind : ParsedBondKind) (bond : RawBond) : RawBond :=
  if effectiveOxoBond? mol bond then { bond with kind := kind } else bond

def respellBonds (mol : RawMolecule) (kind : ParsedBondKind) : RawMolecule where
  atoms := mol.atoms
  bonds := mol.bonds.map (respellBond mol kind)
  neighborOrder := mol.neighborOrder
  introductionPredecessors := mol.introductionPredecessors

@[simp] theorem respellBond_source (mol : RawMolecule) (kind : ParsedBondKind)
    (bond : RawBond) :
    (respellBond mol kind bond).source = bond.source := by
  by_cases effective : effectiveOxoBond? mol bond = true <;>
    simp [respellBond, effective]

@[simp] theorem respellBond_target (mol : RawMolecule) (kind : ParsedBondKind)
    (bond : RawBond) :
    (respellBond mol kind bond).target = bond.target := by
  by_cases effective : effectiveOxoBond? mol bond = true <;>
    simp [respellBond, effective]

@[simp] theorem respellBonds_atomAt? (mol : RawMolecule) (kind : ParsedBondKind)
    (index : Nat) :
    (respellBonds mol kind).atomAt? index = mol.atomAt? index := by
  rfl

@[simp] theorem respellBonds_atomCount (mol : RawMolecule) (kind : ParsedBondKind) :
    (respellBonds mol kind).atomCount = mol.atomCount := by
  rfl

@[simp] theorem respellBonds_writtenNeighbors (mol : RawMolecule)
    (kind : ParsedBondKind) (index : Nat) :
    (respellBonds mol kind).writtenNeighbors index = mol.writtenNeighbors index := by
  unfold RawMolecule.writtenNeighbors
  cases observed : mol.neighborOrder[index]? with
  | some order => simp [respellBonds, observed]
  | none =>
      simp only [respellBonds, observed, List.filterMap_map]
      congr 1
      funext bond
      simp

@[simp] theorem respellBonds_oxygenAt? (mol : RawMolecule)
    (kind : ParsedBondKind) (index : Nat) :
    oxygenAt? (respellBonds mol kind) index = oxygenAt? mol index := by
  simp [oxygenAt?]

@[simp] theorem respellBonds_effectiveOxoCenter? (mol : RawMolecule)
    (kind : ParsedBondKind) (center : Nat) :
    effectiveOxoCenter? (respellBonds mol kind) center = effectiveOxoCenter? mol center := by
  simp [effectiveOxoCenter?]

@[simp] theorem respellBonds_effectiveOxoBond? (mol : RawMolecule)
    (kind : ParsedBondKind) (bond : RawBond) :
    effectiveOxoBond? (respellBonds mol kind) (respellBond mol kind bond) =
      effectiveOxoBond? mol bond := by
  simp [effectiveOxoBond?]

@[simp] theorem respellBonds_chargeInsensitiveAtom? (mol : RawMolecule)
    (kind : ParsedBondKind) (index : Nat) :
    chargeInsensitiveAtom? (respellBonds mol kind) index =
      chargeInsensitiveAtom? mol index := by
  unfold chargeInsensitiveAtom?
  change
    (mol.bonds.map (respellBond mol kind)).any (fun bond =>
        effectiveOxoBond? (respellBonds mol kind) bond &&
          (bond.source == index || bond.target == index)) = _
  rw [List.any_map]
  congr 1
  funext bond
  change
    (effectiveOxoBond? (respellBonds mol kind) (respellBond mol kind bond) &&
        ((respellBond mol kind bond).source == index ||
          (respellBond mol kind bond).target == index)) =
      (effectiveOxoBond? mol bond && (bond.source == index || bond.target == index))
  rw [respellBonds_effectiveOxoBond?, respellBond_source, respellBond_target]

@[simp] theorem normalizeAtom_respellBonds (mol : RawMolecule)
    (kind : ParsedBondKind) (index : Nat) (atom : AtomSpec) :
    normalizeAtom (respellBonds mol kind) index atom = normalizeAtom mol index atom := by
  simp [normalizeAtom]

theorem normalizeAtomsAux_respellBonds (mol : RawMolecule) (kind : ParsedBondKind)
    (offset : Nat) (atoms : List AtomSpec) :
    normalizeAtomsAux (respellBonds mol kind) offset atoms =
      normalizeAtomsAux mol offset atoms := by
  induction atoms generalizing offset with
  | nil => rfl
  | cons atom rest ih =>
      simp [normalizeAtomsAux, ih]

@[simp] theorem normalizeBond_respellBonds (mol : RawMolecule)
    (kind : ParsedBondKind) (bond : RawBond) :
    normalizeBond (respellBonds mol kind) (respellBond mol kind bond) =
      normalizeBond mol bond := by
  have transported := respellBonds_effectiveOxoBond? mol kind bond
  by_cases effective : effectiveOxoBond? mol bond = true
  · have transformed :
        effectiveOxoBond? (respellBonds mol kind) (respellBond mol kind bond) = true := by
      rw [transported]
      exact effective
    simp only [normalizeBond]
    rw [if_pos transformed]
    simp [respellBond, effective]
  · have transformed :
        ¬effectiveOxoBond? (respellBonds mol kind) (respellBond mol kind bond) = true := by
      rw [transported]
      exact effective
    simp only [normalizeBond]
    rw [if_neg transformed]
    simp [respellBond, effective]

/-- Every whole-molecule choice of effective oxo bond spelling belongs to the same P-93.2
representation class. -/
theorem respellBonds_representationEquivalent (mol : RawMolecule)
    (kind : ParsedBondKind) : RepresentationEquivalent (respellBonds mol kind) mol := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · exact normalizeAtomsAux_respellBonds mol kind 0 mol.atoms
  · simp only [respellBonds, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro bond member
    exact normalizeBond_respellBonds mol kind bond

theorem normalize_respellBonds (mol : RawMolecule) (kind : ParsedBondKind) :
    normalize (respellBonds mol kind) = normalize mol :=
  normalize_eq_of_representationEquivalent
    (respellBonds_representationEquivalent mol kind)

/-! ## Whole-molecule formal-charge invariance -/

/-- Assign an arbitrary formal charge at every charge-insensitive effective-oxo endpoint. -/
def rechargeAtom (mol : RawMolecule) (charges : Nat → Int)
    (index : Nat) (atom : AtomSpec) : AtomSpec :=
  if chargeInsensitiveAtom? mol index && chargeNormalizedElement atom.element then
    { atom with charge := charges index }
  else atom

def rechargeAtomsAux (mol : RawMolecule) (charges : Nat → Int) :
    Nat → List AtomSpec → List AtomSpec
  | _, [] => []
  | index, atom :: rest =>
      rechargeAtom mol charges index atom :: rechargeAtomsAux mol charges (index + 1) rest

def recharge (mol : RawMolecule) (charges : Nat → Int) : RawMolecule where
  atoms := rechargeAtomsAux mol charges 0 mol.atoms
  bonds := mol.bonds
  neighborOrder := mol.neighborOrder
  introductionPredecessors := mol.introductionPredecessors

@[simp] theorem rechargeAtom_element (mol : RawMolecule) (charges : Nat → Int)
    (index : Nat) (atom : AtomSpec) :
    (rechargeAtom mol charges index atom).element = atom.element := by
  by_cases insensitive : chargeInsensitiveAtom? mol index = true <;>
    by_cases eligible : chargeNormalizedElement atom.element = true <;>
      simp [rechargeAtom, insensitive, eligible]

@[simp] theorem rechargeAtom_explicitHydrogens? (mol : RawMolecule) (charges : Nat → Int)
    (index : Nat) (atom : AtomSpec) :
    (rechargeAtom mol charges index atom).explicitHydrogens? = atom.explicitHydrogens? := by
  by_cases insensitive : chargeInsensitiveAtom? mol index = true <;>
    by_cases eligible : chargeNormalizedElement atom.element = true <;>
      simp [rechargeAtom, insensitive, eligible]

theorem rechargeAtomsAux_length (mol : RawMolecule) (charges : Nat → Int)
    (offset : Nat) (atoms : List AtomSpec) :
    (rechargeAtomsAux mol charges offset atoms).length = atoms.length := by
  induction atoms generalizing offset with
  | nil => rfl
  | cons atom rest ih => simp [rechargeAtomsAux, ih]

@[simp] theorem recharge_atomCount (mol : RawMolecule) (charges : Nat → Int) :
    (recharge mol charges).atomCount = mol.atomCount := by
  exact rechargeAtomsAux_length mol charges 0 mol.atoms

theorem listGet?_rechargeAtomsAux (mol : RawMolecule) (charges : Nat → Int)
    (offset : Nat) (atoms : List AtomSpec) (index : Nat) :
    listGet? (rechargeAtomsAux mol charges offset atoms) index =
      (listGet? atoms index).map (rechargeAtom mol charges (offset + index)) := by
  induction atoms generalizing offset index with
  | nil => simp [rechargeAtomsAux, listGet?]
  | cons atom rest ih =>
      cases index with
      | zero => simp [rechargeAtomsAux, listGet?]
      | succ index =>
          simpa [rechargeAtomsAux, listGet?, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using ih (offset + 1) index

@[simp] theorem recharge_atomAt? (mol : RawMolecule) (charges : Nat → Int)
    (index : Nat) :
    (recharge mol charges).atomAt? index =
      (mol.atomAt? index).map (rechargeAtom mol charges index) := by
  simp [RawMolecule.atomAt?, recharge, listGet?_rechargeAtomsAux]

@[simp] theorem recharge_writtenNeighbors (mol : RawMolecule) (charges : Nat → Int)
    (index : Nat) :
    (recharge mol charges).writtenNeighbors index = mol.writtenNeighbors index := by
  unfold RawMolecule.writtenNeighbors
  cases observed : mol.neighborOrder[index]? with
  | some order => simp [recharge, observed]
  | none => simp [recharge, observed]

@[simp] theorem recharge_oxygenAt? (mol : RawMolecule) (charges : Nat → Int)
    (index : Nat) :
    oxygenAt? (recharge mol charges) index = oxygenAt? mol index := by
  unfold oxygenAt?
  rw [recharge_atomAt?]
  cases mol.atomAt? index <;> simp

@[simp] theorem recharge_effectiveOxoCenter? (mol : RawMolecule)
    (charges : Nat → Int) (center : Nat) :
    effectiveOxoCenter? (recharge mol charges) center = effectiveOxoCenter? mol center := by
  unfold effectiveOxoCenter?
  rw [recharge_atomAt?]
  cases mol.atomAt? center <;> simp

@[simp] theorem recharge_effectiveOxoBond? (mol : RawMolecule)
    (charges : Nat → Int) (bond : RawBond) :
    effectiveOxoBond? (recharge mol charges) bond = effectiveOxoBond? mol bond := by
  simp [effectiveOxoBond?]

@[simp] theorem recharge_chargeInsensitiveAtom? (mol : RawMolecule)
    (charges : Nat → Int) (index : Nat) :
    chargeInsensitiveAtom? (recharge mol charges) index =
      chargeInsensitiveAtom? mol index := by
  unfold chargeInsensitiveAtom?
  congr 1
  funext bond
  rw [recharge_effectiveOxoBond?]

@[simp] theorem normalizeAtom_rechargeAtom (mol : RawMolecule)
    (charges : Nat → Int) (index : Nat) (atom : AtomSpec) :
    normalizeAtom (recharge mol charges) index (rechargeAtom mol charges index atom) =
      normalizeAtom mol index atom := by
  by_cases insensitive : chargeInsensitiveAtom? mol index = true <;>
    by_cases eligible : chargeNormalizedElement atom.element = true <;>
      simp [normalizeAtom, rechargeAtom, insensitive, eligible]

theorem normalizeAtomsAux_recharge (mol : RawMolecule) (charges : Nat → Int)
    (offset : Nat) (atoms : List AtomSpec) :
    normalizeAtomsAux (recharge mol charges) offset
        (rechargeAtomsAux mol charges offset atoms) =
      normalizeAtomsAux mol offset atoms := by
  induction atoms generalizing offset with
  | nil => rfl
  | cons atom rest ih =>
      simp [rechargeAtomsAux, normalizeAtomsAux, ih]

@[simp] theorem normalizeBond_recharge (mol : RawMolecule) (charges : Nat → Int)
    (bond : RawBond) :
    normalizeBond (recharge mol charges) bond = normalizeBond mol bond := by
  unfold normalizeBond
  rw [recharge_effectiveOxoBond?]

/-- Every assignment of the ignored formal charges belongs to the same P-93.2 representation
class. -/
theorem recharge_representationEquivalent (mol : RawMolecule) (charges : Nat → Int) :
    RepresentationEquivalent (recharge mol charges) mol := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · exact normalizeAtomsAux_recharge mol charges 0 mol.atoms
  · apply List.map_congr_left
    intro bond member
    exact normalizeBond_recharge mol charges bond

theorem normalize_recharge (mol : RawMolecule) (charges : Nat → Int) :
    normalize (recharge mol charges) = normalize mol :=
  normalize_eq_of_representationEquivalent
    (recharge_representationEquivalent mol charges)

/-! ### Insertion packet

Everything from this banner through `hydrogenAwareEquivalent_iff_normalize_and_frozen` is the
production insertion packet.  It deliberately declares no helper that duplicates a declaration of
`TetraStereo.OneCenter.RawSourceHydrogenPolicy`; every freezing invariant is imported from that
module.  The `open RawMolecule` command below is part of the packet: the production module has no
such open, so the packet must be inserted together with it. -/

open RawMolecule

/-! ## Explicit-hydrogen closure

Freezing stores `mol.hydrogenCountAt index` in every atom's `explicitHydrogens?` field.  On
molecules all of whose atoms already carry an explicit hydrogen policy this is the identity.  The
hydrogen-aware representation lemmas below are therefore stated for the explicit-hydrogen domain:
the unconditional freezing-commutation statements of the pre-repair packet are false once the
effective oxo-center gate counts the stored inline hydrogen, because an unbracketed center can be
effective under the written policy (`written + 0 = 4`) yet not effective under its filled source
count (`written + fill ≠ 4`). -/

/-- Every atom carries an explicit (bracket or frozen) hydrogen policy. -/
def AllExplicitHydrogens (mol : RawMolecule) : Prop :=
  ∀ index atom, mol.atomAt? index = some atom → ∃ count, atom.explicitHydrogens? = some count

private theorem listGet?_eq_getElem? {α : Type} (list : List α) (index : Nat) :
    listGet? list index = list[index]? := by
  induction list generalizing index with
  | nil => cases index <;> rfl
  | cons head tail ih =>
      cases index with
      | zero => rfl
      | succ index => exact ih index

private theorem list_eq_of_listGet?_eq {α : Type} {first second : List α}
    (equal : ∀ index, listGet? first index = listGet? second index) :
    first = second := by
  apply List.ext_getElem?
  intro index
  rw [← listGet?_eq_getElem? first index, ← listGet?_eq_getElem? second index]
  exact equal index

/-- On a molecule all of whose atoms already carry an explicit hydrogen policy, the freezing pass
is the identity: it rewrites `some count` to `some (hydrogenCountAt index)`, and the explicit
branch of `hydrogenCountAt` returns that very `count`. -/
theorem freezeSourceHydrogenCounts_eq_self_of_allExplicitHydrogens (mol : RawMolecule)
    (explicit : AllExplicitHydrogens mol) :
    freezeSourceHydrogenCounts mol = mol := by
  cases mol with
  | mk atoms bonds neighbors predecessors =>
      change RawMolecule.mk
        (freezeSourceHydrogenCountsAux (RawMolecule.mk atoms bonds neighbors predecessors) 0 atoms)
        bonds neighbors predecessors = RawMolecule.mk atoms bonds neighbors predecessors
      simp only [RawMolecule.mk.injEq, eq_self, and_true]
      apply list_eq_of_listGet?_eq
      intro index
      rw [listGet?_freezeSourceHydrogenCountsAux]
      simp only [Nat.zero_add]
      cases lookup : listGet? atoms index with
      | none => rfl
      | some atom =>
          have atomLookup :
              (⟨atoms, bonds, neighbors, predecessors⟩ : RawMolecule).atomAt? index = some atom := by
            simpa [RawMolecule.atomAt?] using lookup
          obtain ⟨count, explicitCount⟩ := explicit index atom atomLookup
          have countEq :
              (⟨atoms, bonds, neighbors, predecessors⟩ : RawMolecule).hydrogenCountAt index =
                count :=
            hydrogenCountAt_of_explicitHydrogens?_some _ index count atom atomLookup explicitCount
          simp only [Option.map_some]
          rw [countEq]
          have updateEq : ({ atom with explicitHydrogens? := some count } : AtomSpec) = atom := by
            cases atom
            simp_all
          rw [updateEq]

/-! ## Quotient predicates under source-hydrogen freezing

Freezing is a pure copy of the source hydrogen count, so the frozen effective-oxo predicates read
the source count rather than the bracket policy.  The oxygen test is element-based and remains
freezing-insensitive; the center test does not commute with freezing without the explicit-hydrogen
closure. -/

/-- The P-93.2 oxygen test is element-based and therefore insensitive to hydrogen freezing. -/
@[simp] theorem oxygenAt?_freezeSourceHydrogenCounts (mol : RawMolecule) (atom : Nat) :
    oxygenAt? (freezeSourceHydrogenCounts mol) atom = oxygenAt? mol atom := by
  unfold oxygenAt?
  rw [freezeSourceHydrogenCounts_atomAt?]
  cases mol.atomAt? atom <;> rfl

/-- On a source-hydrogen-frozen molecule the effective oxo-center test is exactly the element,
written-neighbour-count, and *source* hydrogen count test: freezing writes the exact source count
into `explicitHydrogens?`, and `getD 0` reads it back. -/
theorem effectiveOxoCenter?_freezeSourceHydrogenCounts_iff (mol : RawMolecule) (center : Nat) :
    effectiveOxoCenter? (freezeSourceHydrogenCounts mol) center = true ↔
      ∃ spec, mol.atomAt? center = some spec ∧
        oxoCenterElement spec.element = true ∧
        (mol.writtenNeighbors center).length + mol.hydrogenCountAt center = 4 := by
  rw [effectiveOxoCenter?_eq_true_iff]
  cases observed : mol.atomAt? center with
  | none => simp [EffectiveOxoCenter, freezeSourceHydrogenCounts_atomAt?, observed]
  | some spec =>
      simp [EffectiveOxoCenter, freezeSourceHydrogenCounts_atomAt?,
        freezeSourceHydrogenCounts_writtenNeighbors, observed]

/-- `normalizeAtom` preserves the exact `explicitHydrogens?` policy.  This is the only atom field
the repair touches, and the quotient never rewrites it. -/
@[simp] theorem normalizeAtom_explicitHydrogens? (mol : RawMolecule) (index : Nat)
    (atom : AtomSpec) :
    (normalizeAtom mol index atom).explicitHydrogens? = atom.explicitHydrogens? := by
  by_cases insensitive : chargeInsensitiveAtom? mol index = true <;>
    by_cases eligible : chargeNormalizedElement atom.element = true <;>
      simp [normalizeAtom, insensitive, eligible]

/-- The quotient atom map exposes an already frozen explicit hydrogen policy unchanged. -/
@[simp] theorem normalizeAtom_frozen_explicitHydrogens? (mol : RawMolecule) (index : Nat)
    (atom : AtomSpec) (count : Nat) :
    (normalizeAtom mol index { atom with explicitHydrogens? := some count }).explicitHydrogens? =
      some count := by
  rw [normalizeAtom_explicitHydrogens?]

/-! ## Atom arrays of the normalized frozen quotient -/

/-- Pointwise form of the normalized atom array. -/
theorem listGet?_normalizeAtoms (mol : RawMolecule) (index : Nat) :
    listGet? (normalizeAtoms mol) index =
      (mol.atomAt? index).map (normalizeAtom mol index) := by
  simp [normalizeAtoms, RawMolecule.atomAt?, listGet?_normalizeAtomsAux]

/-! ## The hydrogen-aware relation and the normalized frozen graph equality -/

/-- The algebraic repair of `normalize`-equivalence.  Two written graphs are hydrogen-aware
P-93.2-equivalent when their effective graphs agree in the P-93.2 quotient *and* every written
atom has the same total hydrogen count under the OpenSMILES source policy.

The first conjunct is the original `RepresentationEquivalent`/`normalize`-equality.  The second
conjunct is exactly what prevents the quotient from silently protonating (or deprotonating) an
atom whose source hydrogen count was fixed by the written bond orders. -/
def HydrogenAwareEquivalent (left right : RawMolecule) : Prop :=
  normalize left = normalize right ∧
    ∀ index, left.hydrogenCountAt index = right.hydrogenCountAt index

/-- `HydrogenAwareEquivalent` is the conjunction of P-93.2 representation equivalence and
pointwise source-hydrogen-count agreement. -/
theorem hydrogenAwareEquivalent_iff_representationEquivalent (left right : RawMolecule) :
    HydrogenAwareEquivalent left right ↔
      RepresentationEquivalent left right ∧
        ∀ index, left.hydrogenCountAt index = right.hydrogenCountAt index := by
  unfold HydrogenAwareEquivalent
  constructor
  · rintro ⟨normalizeEq, counts⟩
    exact ⟨(representationEquivalent_iff_normalize_eq left right).mpr normalizeEq, counts⟩
  · rintro ⟨equivalent, counts⟩
    exact ⟨(representationEquivalent_iff_normalize_eq left right).mp equivalent, counts⟩

theorem hydrogenAwareEquivalent_refl (mol : RawMolecule) :
    HydrogenAwareEquivalent mol mol :=
  ⟨rfl, fun _index => rfl⟩

theorem hydrogenAwareEquivalent_symm {left right : RawMolecule}
    (equivalent : HydrogenAwareEquivalent left right) :
    HydrogenAwareEquivalent right left := by
  unfold HydrogenAwareEquivalent at equivalent
  exact ⟨equivalent.1.symm, fun index => (equivalent.2 index).symm⟩

theorem hydrogenAwareEquivalent_trans {first second third : RawMolecule}
    (firstSecond : HydrogenAwareEquivalent first second)
    (secondThird : HydrogenAwareEquivalent second third) :
    HydrogenAwareEquivalent first third := by
  unfold HydrogenAwareEquivalent at firstSecond secondThird
  exact ⟨firstSecond.1.trans secondThird.1,
    fun index => (firstSecond.2 index).trans (secondThird.2 index)⟩

/-- `HydrogenAwareEquivalent` is an equivalence relation on raw molecules. -/
theorem hydrogenAwareEquivalent_equivalence :
    Equivalence HydrogenAwareEquivalent :=
  ⟨hydrogenAwareEquivalent_refl,
    @hydrogenAwareEquivalent_symm,
    @hydrogenAwareEquivalent_trans⟩

/-- Normalized frozen graph equality on the explicit-hydrogen domain.  On molecules all of whose
atoms already carry an explicit hydrogen policy, freezing is the identity, so the frozen quotient
is exactly the source quotient. -/
theorem normalize_freezeSourceHydrogenCounts_eq
    {left right : RawMolecule}
    (leftExplicit : AllExplicitHydrogens left) (rightExplicit : AllExplicitHydrogens right)
    (normalizeEq : normalize left = normalize right) :
    normalize (freezeSourceHydrogenCounts left) =
      normalize (freezeSourceHydrogenCounts right) := by
  rw [freezeSourceHydrogenCounts_eq_self_of_allExplicitHydrogens left leftExplicit,
    freezeSourceHydrogenCounts_eq_self_of_allExplicitHydrogens right rightExplicit]
  exact normalizeEq

/-- The P-93.2 quotient of a source-hydrogen-frozen molecule keeps the exact source hydrogen
count.  This is the direct statement that the repair prevents the quotient from changing the
hydrogen constitution: freezing makes the policy explicit, and `normalizeAtom` preserves it. -/
theorem normalize_freezeSourceHydrogenCounts_hydrogenCountAt (mol : RawMolecule) (index : Nat) :
    (normalize (freezeSourceHydrogenCounts mol)).hydrogenCountAt index =
      mol.hydrogenCountAt index := by
  cases sourceLookup : mol.atomAt? index with
  | none =>
      have frozenNone : (freezeSourceHydrogenCounts mol).atomAt? index = none := by
        rw [freezeSourceHydrogenCounts_atomAt?, sourceLookup]
        rfl
      have normalizeNone : (normalize (freezeSourceHydrogenCounts mol)).atomAt? index = none := by
        rw [normalize_atomAt?, frozenNone]
        rfl
      simp [RawMolecule.hydrogenCountAt, sourceLookup, normalizeNone]
  | some atom =>
      have frozenSome : (freezeSourceHydrogenCounts mol).atomAt? index =
          some { atom with explicitHydrogens? := some (mol.hydrogenCountAt index) } := by
        rw [freezeSourceHydrogenCounts_atomAt?, sourceLookup]
        rfl
      have normalizeSome : (normalize (freezeSourceHydrogenCounts mol)).atomAt? index =
          some (normalizeAtom (freezeSourceHydrogenCounts mol) index
            { atom with explicitHydrogens? := some (mol.hydrogenCountAt index) }) := by
        rw [normalize_atomAt?, frozenSome]
        rfl
      exact hydrogenCountAt_of_explicitHydrogens?_some
        (normalize (freezeSourceHydrogenCounts mol)) index (mol.hydrogenCountAt index) _
        normalizeSome (normalizeAtom_frozen_explicitHydrogens? _ _ _ _)

/-- The normalized frozen equality recovers pointwise source-hydrogen-count agreement, because
`normalizeAtom` preserves the exact `explicitHydrogens?` policy and freezing makes that policy the
exact source count. -/
theorem hydrogenCountAt_eq_of_normalize_freezeSource_eq
    {left right : RawMolecule}
    (frozenEq : normalize (freezeSourceHydrogenCounts left) =
      normalize (freezeSourceHydrogenCounts right))
    (index : Nat) :
    left.hydrogenCountAt index = right.hydrogenCountAt index := by
  have atomsEq : normalizeAtoms (freezeSourceHydrogenCounts left) =
      normalizeAtoms (freezeSourceHydrogenCounts right) := by
    have raw := congrArg RawMolecule.atoms frozenEq
    simpa [normalize] using raw
  have lookups : listGet? (normalizeAtoms (freezeSourceHydrogenCounts left)) index =
      listGet? (normalizeAtoms (freezeSourceHydrogenCounts right)) index := by rw [atomsEq]
  simp only [listGet?_normalizeAtoms, freezeSourceHydrogenCounts_atomAt?] at lookups
  cases leftLookup : left.atomAt? index with
  | none =>
      cases rightLookup : right.atomAt? index with
      | none =>
          rw [hydrogenCountAt_of_atomAt?_eq_none left index leftLookup,
            hydrogenCountAt_of_atomAt?_eq_none right index rightLookup]
      | some other =>
          rw [leftLookup, rightLookup] at lookups
          simp only [Option.map_none, Option.map_some] at lookups
          cases lookups
  | some atom =>
      cases rightLookup : right.atomAt? index with
      | none =>
          rw [leftLookup, rightLookup] at lookups
          simp only [Option.map_none, Option.map_some] at lookups
          cases lookups
      | some other =>
          rw [leftLookup, rightLookup] at lookups
          simp only [Option.map_some, Option.some.injEq] at lookups
          have explicit := congrArg AtomSpec.explicitHydrogens? lookups
          simp only [normalizeAtom_frozen_explicitHydrogens?] at explicit
          exact Option.some.inj explicit

/-- Exact algebraic characterization of the hydrogen-aware relation on the explicit-hydrogen
domain: it is precisely the conjunction of the original P-93.2 quotient equality and the
normalized frozen quotient equality. -/
theorem hydrogenAwareEquivalent_iff_normalize_and_frozen
    {left right : RawMolecule}
    (leftExplicit : AllExplicitHydrogens left) (rightExplicit : AllExplicitHydrogens right) :
    HydrogenAwareEquivalent left right ↔
      normalize left = normalize right ∧
        normalize (freezeSourceHydrogenCounts left) =
          normalize (freezeSourceHydrogenCounts right) := by
  unfold HydrogenAwareEquivalent
  constructor
  · rintro ⟨normalizeEq, _counts⟩
    exact ⟨normalizeEq, normalize_freezeSourceHydrogenCounts_eq leftExplicit rightExplicit normalizeEq⟩
  · rintro ⟨normalizeEq, frozenEq⟩
    exact ⟨normalizeEq,
      fun index => hydrogenCountAt_eq_of_normalize_freezeSource_eq frozenEq index⟩

/-- Production normalization now has a P-93.2 entry point: first freeze the exact source hydrogen
counts, then choose the canonical effective representation, then run the existing chemistry
normalizer and ordinary P-92 analyzer.  Freezing precedes the quotient because the quotient lowers
effective oxo multiple bonds and would otherwise change the source hydrogen inventory. -/
def normalizeRawMoleculeP93 (mol : RawMolecule) (cycles : List AromaticCycle := []) :
    ChemistryNormalizationResult :=
  normalizeRawMolecule (normalize (freezeSourceHydrogenCounts mol)) cycles

@[simp] theorem normalizeRawMoleculeP93_parsed
    (mol : RawMolecule) (cycles : List AromaticCycle := []) :
    (normalizeRawMoleculeP93 mol cycles).parsed =
      (normalize (freezeSourceHydrogenCounts mol)).normalizeUnspecifiedBonds := by
  rfl

/-! ## Source hydrogen freezing preserves Rule-2 mass admission

Freezing rewrites only each atom's `explicitHydrogens?` policy.  The Rule-2 key reads only element
and isotope, so every source mass certificate remains available.  These lemmas are local to the
production module; they do not extend the shared `RawSourceHydrogenPolicy` interface. -/

@[simp] theorem freezeSourceHydrogenCountsAux_rule2MassCheck (mol : RawMolecule)
    (offset : Nat) (atoms : List AtomSpec) :
    (freezeSourceHydrogenCountsAux mol offset atoms).all
        (fun atom => (rule2MassPico? atom.element atom.isotope?).isSome) =
      atoms.all
        (fun atom => (rule2MassPico? atom.element atom.isotope?).isSome) := by
  induction atoms generalizing offset with
  | nil => rfl
  | cons atom rest ih =>
      simp only [freezeSourceHydrogenCountsAux, List.all_cons, ih (offset + 1)]

@[simp] theorem freezeSourceHydrogenCounts_rule2MassesKnown? (mol : RawMolecule) :
    (freezeSourceHydrogenCounts mol).rule2MassesKnown? = mol.rule2MassesKnown? := by
  simp [RawMolecule.rule2MassesKnown?, freezeSourceHydrogenCounts]

@[simp] theorem freezeSourceHydrogenCounts_rule2MassesKnown_iff (mol : RawMolecule) :
    (freezeSourceHydrogenCounts mol).Rule2MassesKnown ↔ mol.Rule2MassesKnown := by
  rw [← (freezeSourceHydrogenCounts mol).rule2MassesKnown?_eq_true_iff,
    ← mol.rule2MassesKnown?_eq_true_iff, freezeSourceHydrogenCounts_rule2MassesKnown?]

/-- Freezing preserves the source-backed Rule-2 mass obligation. -/
theorem freezeSourceHydrogenCounts_rule2MassesKnown (mol : RawMolecule)
    (known : mol.Rule2MassesKnown) :
    (freezeSourceHydrogenCounts mol).Rule2MassesKnown :=
  (freezeSourceHydrogenCounts_rule2MassesKnown_iff mol).mpr known

/-- Structural chemistry admission is transported constructively through source-hydrogen freezing,
the effective-graph quotient, and default-bond normalization.  Freezing is a structural no-op, so
each source certificate is threaded through the frozen quotient rather than re-assumed. -/
def certifyP93 (mol : RawMolecule) (cycles : List AromaticCycle)
    (admissible : mol.Admissible) (writtenExact : mol.WrittenNeighborExact)
    (valence : mol.ValenceOK) (masses : mol.Rule2MassesKnown) :
    CertifiedChemistryNormalizationResult where
  result := normalizeRawMoleculeP93 mol cycles
  admissible := by
    simpa using (normalize (freezeSourceHydrogenCounts mol)).normalizeUnspecifiedBonds_admissible
      (normalize_admissible (freezeSourceHydrogenCounts mol)
        (freezeSourceHydrogenCounts_admissible mol admissible))
  writtenNeighborExact := by
    simpa using
      (normalize (freezeSourceHydrogenCounts mol)).normalizeUnspecifiedBonds_writtenNeighborExact
        (normalize_writtenNeighborExact (freezeSourceHydrogenCounts mol)
          (freezeSourceHydrogenCounts_writtenNeighborExact mol writtenExact))
  valenceOK := by
    simpa using normalizeUnspecifiedBonds_valenceOK (normalize (freezeSourceHydrogenCounts mol))
      (normalize_valenceOK (freezeSourceHydrogenCounts mol)
        (freezeSourceHydrogenCounts_valenceOK mol valence))
  rule2MassesKnown := by
    simpa using freezeSourceHydrogenCounts_rule2MassesKnown mol masses

/-- Executable certified normalization. -/
def normalizeRawMoleculeP93Certified? (mol : RawMolecule)
    (cycles : List AromaticCycle := []) : Option CertifiedChemistryNormalizationResult :=
  (normalizeRawMoleculeP93 mol cycles).certify?

/-- The P-93 representation change preserves every source-introduction consistency check. -/
@[simp] theorem normalize_introductionPredecessorsValid (mol : RawMolecule) :
    (normalize mol).introductionPredecessorsValid? = mol.introductionPredecessorsValid? := by
  simp only [RawMolecule.introductionPredecessorsValid?,
    show (normalize mol).introductionPredecessors = mol.introductionPredecessors from rfl,
    normalize_atomCount, normalize_writtenNeighbors,
    show (normalize mol).bonds = mol.bonds.map (normalizeBond mol) from rfl,
    List.any_map, Function.comp_def, normalizeBond_source, normalizeBond_target]

private theorem normalizeUnspecifiedBonds_introductionPredecessorsValid (mol : RawMolecule) :
    mol.normalizeUnspecifiedBonds.introductionPredecessorsValid? =
      mol.introductionPredecessorsValid? := by
  simp only [RawMolecule.introductionPredecessorsValid?,
    show mol.normalizeUnspecifiedBonds.introductionPredecessors =
      mol.introductionPredecessors from rfl,
    show mol.normalizeUnspecifiedBonds.atomCount = mol.atomCount from rfl,
    RawMolecule.normalizeUnspecifiedBonds_writtenNeighbors,
    show mol.normalizeUnspecifiedBonds.bonds =
      mol.bonds.map mol.normalizeUnspecifiedBond from rfl,
    List.any_map, Function.comp_def, RawMolecule.normalizeUnspecifiedBond_source,
    RawMolecule.normalizeUnspecifiedBond_target]

/-- No admitted finite molecule with internally consistent source-introduction metadata is
refused merely because the source-mandated P-93.2 quotient was inserted. Empty legacy prefixes
satisfy the metadata condition; no external source authentication is inferred. -/
theorem normalizeRawMoleculeP93Certified?_exists
    (mol : RawMolecule) (cycles : List AromaticCycle)
    (admissible : mol.Admissible) (writtenExact : mol.WrittenNeighborExact)
    (valence : mol.ValenceOK) (masses : mol.Rule2MassesKnown)
    (introduction : mol.introductionPredecessorsValid? = true) :
    ∃ certified, normalizeRawMoleculeP93Certified? mol cycles = some certified := by
  let expected := certifyP93 mol cycles admissible writtenExact valence masses
  have hadmissible : (normalizeRawMoleculeP93 mol cycles).parsed.admissible? = true :=
    ((normalizeRawMoleculeP93 mol cycles).parsed.admissible?_eq_true_iff).2 expected.admissible
  have hwritten :
      (normalizeRawMoleculeP93 mol cycles).parsed.writtenNeighborExact? = true :=
    ((normalizeRawMoleculeP93 mol cycles).parsed.writtenNeighborExact?_eq_true_iff).2
      expected.writtenNeighborExact
  have hvalence : (normalizeRawMoleculeP93 mol cycles).parsed.valenceOK? = true :=
    ((normalizeRawMoleculeP93 mol cycles).parsed.valenceOK?_eq_true_iff).2 expected.valenceOK
  have hmasses : (normalizeRawMoleculeP93 mol cycles).parsed.rule2MassesKnown? = true :=
    ((normalizeRawMoleculeP93 mol cycles).parsed.rule2MassesKnown?_eq_true_iff).2
      expected.rule2MassesKnown
  have hintroduction :
      (normalizeRawMoleculeP93 mol cycles).parsed.introductionPredecessorsValid? = true := by
    rw [normalizeRawMoleculeP93_parsed mol cycles,
      normalizeUnspecifiedBonds_introductionPredecessorsValid,
      normalize_introductionPredecessorsValid,
      freezeSourceHydrogenCounts_introductionPredecessorsValid?]
    exact introduction
  unfold normalizeRawMoleculeP93Certified?
  unfold ChemistryNormalizationResult.certify?
  rw [if_pos hintroduction, dif_pos hadmissible, dif_pos hwritten, dif_pos hvalence, dif_pos hmasses]
  exact ⟨_, rfl⟩

def analyzeRawP93 (mol : RawMolecule) (cycles : List AromaticCycle := []) :
    List StereoAssignment :=
  analyzeNormalized (normalizeRawMoleculeP93 mol cycles)

/-- Authority-facing string entry point using the P-93.2 effective graph. -/
def analyzeSmilesP93 (input : String) : Except ParserError (List StereoAssignment) := do
  let mol ← parseOpenSMILES input
  match normalizeRawMoleculeP93Certified? mol with
  | none =>
      Except.error
        "P-93-normalized molecule failed structural, valence, or Rule-2 mass admission"
  | some certified =>
      if !certified.result.expandedStereochemicalAdmissible? then
        Except.error "hydrogen-expanded P-93 molecule failed stereochemical admission"
      else
        Except.ok (analyzeNormalized certified.result)

/-! ## Source-hydrogen counts are invariant under formal-charge respelling

`rechargeAtom` rewrites only the `charge` field.  `hydrogenCountAt` reads the hydrogen policy, the
element, the aromatic flag, and the bond-order sum; it never reads charge.  Hence every recharge
has the same source hydrogen inventory. -/

@[simp] theorem rechargeAtom_aromatic (mol : RawMolecule) (charges : Nat → Int)
    (index : Nat) (atom : AtomSpec) :
    (rechargeAtom mol charges index atom).aromatic = atom.aromatic := by
  by_cases insensitive : chargeInsensitiveAtom? mol index = true <;>
    by_cases eligible : chargeNormalizedElement atom.element = true <;>
      simp [rechargeAtom, insensitive, eligible]

@[simp] theorem recharge_incidentBondOrderSum (mol : RawMolecule) (charges : Nat → Int)
    (index : Nat) :
    (recharge mol charges).incidentBondOrderSum index = mol.incidentBondOrderSum index := by
  unfold RawMolecule.incidentBondOrderSum
  rfl

/-- `defaultValences` reads only the element and the aromatic flag. -/
theorem defaultValences_eq_of_element_aromatic {first second : AtomSpec}
    (elementEq : first.element = second.element)
    (aromaticEq : first.aromatic = second.aromatic) :
    RawMolecule.defaultValences first = RawMolecule.defaultValences second := by
  unfold RawMolecule.defaultValences
  rw [elementEq, aromaticEq]

/-- Formal-charge respelling does not change the default fill valence. -/
@[simp] theorem defaultValences_rechargeAtom (mol : RawMolecule) (charges : Nat → Int)
    (index : Nat) (atom : AtomSpec) :
    RawMolecule.defaultValences (rechargeAtom mol charges index atom) =
      RawMolecule.defaultValences atom :=
  defaultValences_eq_of_element_aromatic
    (rechargeAtom_element mol charges index atom)
    (rechargeAtom_aromatic mol charges index atom)

@[simp] theorem hydrogenCountAt_recharge (mol : RawMolecule) (charges : Nat → Int)
    (index : Nat) :
    (recharge mol charges).hydrogenCountAt index = mol.hydrogenCountAt index := by
  unfold RawMolecule.hydrogenCountAt
  rw [recharge_atomAt?]
  cases observed : mol.atomAt? index with
  | none =>
      simp only [Option.map_none]
  | some atom =>
      simp only [Option.map_some, rechargeAtom_explicitHydrogens?,
        recharge_incidentBondOrderSum, defaultValences_rechargeAtom]

/-- Recharging changes only the charge field, so the explicit-hydrogen closure is preserved. -/
theorem allExplicitHydrogens_recharge (mol : RawMolecule) (charges : Nat → Int)
    (explicit : AllExplicitHydrogens mol) :
    AllExplicitHydrogens (recharge mol charges) := by
  intro index atom lookup
  rw [recharge_atomAt?] at lookup
  cases sourceLookup : mol.atomAt? index with
  | none => simp [sourceLookup] at lookup
  | some source =>
      simp [sourceLookup] at lookup
      have atomEq : rechargeAtom mol charges index source = atom := lookup
      subst atom
      obtain ⟨count, explicitCount⟩ := explicit index source sourceLookup
      exact ⟨count, by rw [rechargeAtom_explicitHydrogens?]; exact explicitCount⟩

/-- Respelling preserves atoms, so the explicit-hydrogen closure is unchanged. -/
theorem allExplicitHydrogens_respellBonds (mol : RawMolecule) (kind : ParsedBondKind)
    (explicit : AllExplicitHydrogens mol) :
    AllExplicitHydrogens (respellBonds mol kind) := by
  intro index atom lookup
  have lookup' : mol.atomAt? index = some atom := by
    simpa [respellBonds] using lookup
  exact explicit index atom lookup'

/-- Equivalent bond/charge spellings produce definitionally identical complete descriptor lists on
the explicit-hydrogen domain.  The explicit-hydrogen premise is essential: once the effective
oxo-center gate counts the stored inline hydrogen, an unbracketed center can be effective under the
written policy yet not under its filled source count, so freezing is no longer invisible without
the explicit-hydrogen closure. -/
theorem analyzeRawP93_eq_of_representationEquivalent {left right : RawMolecule}
    (leftExplicit : AllExplicitHydrogens left) (rightExplicit : AllExplicitHydrogens right)
    (equivalent : RepresentationEquivalent left right)
    (cycles : List AromaticCycle := []) :
    analyzeRawP93 left cycles = analyzeRawP93 right cycles := by
  simp only [analyzeRawP93, normalizeRawMoleculeP93]
  rw [normalize_freezeSourceHydrogenCounts_eq leftExplicit rightExplicit
    ((representationEquivalent_iff_normalize_eq left right).mp equivalent)]

/-- Whole-pipeline form of P-93.2.3--.5 bond-formalism irrelevance on the explicit-hydrogen
domain. -/
theorem analyzeRawP93_respellBonds (mol : RawMolecule) (kind : ParsedBondKind)
    (explicit : AllExplicitHydrogens mol)
    (cycles : List AromaticCycle := []) :
    analyzeRawP93 (respellBonds mol kind) cycles = analyzeRawP93 mol cycles :=
  analyzeRawP93_eq_of_representationEquivalent
    (allExplicitHydrogens_respellBonds mol kind explicit) explicit
    (respellBonds_representationEquivalent mol kind) cycles

/-- Whole-pipeline form of P-93.2.4 formal-charge irrelevance on the explicit-hydrogen domain. -/
theorem analyzeRawP93_recharge (mol : RawMolecule) (charges : Nat → Int)
    (explicit : AllExplicitHydrogens mol)
    (cycles : List AromaticCycle := []) :
    analyzeRawP93 (recharge mol charges) cycles = analyzeRawP93 mol cycles :=
  analyzeRawP93_eq_of_representationEquivalent
    (allExplicitHydrogens_recharge mol charges explicit) explicit
    (recharge_representationEquivalent mol charges) cycles

/-- Bond order and formal-charge placement may vary simultaneously without changing any emitted
unit, refusal, descriptor family, or descriptor value, provided the source molecule is on the
explicit-hydrogen domain (equivalently, already frozen). -/
theorem analyzeRawP93_representation_invariant (mol : RawMolecule)
    (charges : Nat → Int) (kind : ParsedBondKind)
    (explicit : AllExplicitHydrogens mol)
    (cycles : List AromaticCycle := []) :
    analyzeRawP93 (respellBonds (recharge mol charges) kind) cycles =
      analyzeRawP93 mol cycles := by
  calc
    analyzeRawP93 (respellBonds (recharge mol charges) kind) cycles =
        analyzeRawP93 (recharge mol charges) cycles :=
      analyzeRawP93_respellBonds (recharge mol charges) kind
        (allExplicitHydrogens_recharge mol charges explicit) cycles
    _ = analyzeRawP93 mol cycles := analyzeRawP93_recharge mol charges explicit cycles

/-- End-to-end soundness of the P-93.2 entry point against the existing independent assignment
sum, now evaluated on the source-mandated effective graph. -/
theorem mem_analyzeRawP93_iff_independently_judged
    (mol : RawMolecule) (cycles : List AromaticCycle) (assignment : StereoAssignment) :
    assignment ∈ analyzeRawP93 mol cycles ↔
      let result := normalizeRawMoleculeP93 mol cycles
      result.parsed.rule2MassesKnown? = true ∧
        result.expandedStereochemicalAdmissible? = true ∧
          IndependentlyJudgedNormalizedStereoAssignment result assignment := by
  exact mem_analyzeNormalized_iff_independently_judged
    (normalizeRawMoleculeP93 mol cycles) assignment

/-! ## Kernel-authority guards for the hydrogen-aware patch -/

assert_kernel_only oxygenAt?_freezeSourceHydrogenCounts
assert_kernel_only effectiveOxoCenter?_freezeSourceHydrogenCounts_iff
assert_kernel_only normalizeAtom_explicitHydrogens?
assert_kernel_only normalizeAtom_frozen_explicitHydrogens?
assert_kernel_only listGet?_normalizeAtoms
assert_kernel_only freezeSourceHydrogenCounts_eq_self_of_allExplicitHydrogens
assert_kernel_only hydrogenAwareEquivalent_iff_representationEquivalent
assert_kernel_only hydrogenAwareEquivalent_refl
assert_kernel_only hydrogenAwareEquivalent_symm
assert_kernel_only hydrogenAwareEquivalent_trans
assert_kernel_only hydrogenAwareEquivalent_equivalence
assert_kernel_only normalize_freezeSourceHydrogenCounts_eq
assert_kernel_only normalize_freezeSourceHydrogenCounts_hydrogenCountAt
assert_kernel_only hydrogenCountAt_eq_of_normalize_freezeSource_eq
assert_kernel_only hydrogenAwareEquivalent_iff_normalize_and_frozen
assert_kernel_only freezeSourceHydrogenCountsAux_rule2MassCheck
assert_kernel_only freezeSourceHydrogenCounts_rule2MassesKnown?
assert_kernel_only freezeSourceHydrogenCounts_rule2MassesKnown_iff
assert_kernel_only freezeSourceHydrogenCounts_rule2MassesKnown
assert_kernel_only rechargeAtom_aromatic
assert_kernel_only rechargeAtom_explicitHydrogens?
assert_kernel_only recharge_incidentBondOrderSum
assert_kernel_only defaultValences_eq_of_element_aromatic
assert_kernel_only defaultValences_rechargeAtom
assert_kernel_only hydrogenCountAt_recharge
assert_kernel_only allExplicitHydrogens_recharge
assert_kernel_only allExplicitHydrogens_respellBonds
assert_kernel_only normalizeRawMoleculeP93_parsed
assert_kernel_only normalizeRawMoleculeP93Certified?_exists
assert_kernel_only analyzeRawP93_eq_of_representationEquivalent
assert_kernel_only analyzeRawP93_respellBonds
assert_kernel_only analyzeRawP93_recharge
assert_kernel_only analyzeRawP93_representation_invariant

end BlueBookP93.NoncarbonTetrahedra.Production
end TetraStereo.OneCenter
