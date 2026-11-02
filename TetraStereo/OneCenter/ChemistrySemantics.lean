import TetraStereo.OneCenter.CIPOfficialRules
import TetraStereo.OneCenter.CIPRule2MassData

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

/-!
  Production-facing chemical semantics.

  This module is the intake/normalization layer in front of the formal stereochemistry engine.  It
  does six jobs in one pipeline:

  * parse an OpenSMILES-style molecular string into atoms and bonds,
  * assign executable valence checks,
  * normalize aromatic bond defaults,
  * record resonance-delocalized bond semantics,
  * preserve stereobond and tetrahedral input annotations,
  * collect mobile-hydrogen/tautomer sites into a fixed-H aware normalization object.

  The current parser is deliberately small but real: it handles organic-subset atoms, aromatic
  lowercase atoms, bracket atoms with isotope/chirality/H/charge markers, branches, ring closures,
  single/double/triple/aromatic/directional bonds, and disconnected components.  The surrounding
  semantic records are designed so later importers (SDF/Molfile/InChI/RDKit dumps) can target the
  same normalized representation without changing the proof-facing API.
-/

/-! ### Chemical atoms and bonds -/

/-- Local list lookup to avoid depending on parser-facing APIs outside core/mathlib. -/
def listGet? {α : Type*} : List α → ℕ → Option α
  | [], _ => none
  | value :: _, 0 => some value
  | _ :: rest, index + 1 => listGet? rest index

theorem listGet?_exists_of_lt {α : Type*} (values : List α) (index : ℕ)
    (bound : index < values.length) : ∃ value, listGet? values index = some value := by
  induction values generalizing index with
  | nil => simp at bound
  | cons head tail inductionHypothesis =>
      cases index with
      | zero => exact ⟨head, rfl⟩
      | succ index =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at bound
          simpa [listGet?] using inductionHypothesis index bound

theorem listGet?_eq_some_implies_lt {α : Type*} (values : List α) (index : ℕ) (value : α)
    (lookup : listGet? values index = some value) : index < values.length := by
  induction values generalizing index with
  | nil => simp [listGet?] at lookup
  | cons head tail inductionHypothesis =>
      cases index with
      | zero => simp
      | succ index =>
          simp only [listGet?] at lookup
          simpa using inductionHypothesis index lookup

theorem listGet?_eq_some_implies_mem {α : Type*} (values : List α) (index : ℕ) (value : α)
    (lookup : listGet? values index = some value) : value ∈ values := by
  induction values generalizing index with
  | nil => simp [listGet?] at lookup
  | cons head tail inductionHypothesis =>
      cases index with
      | zero =>
          have equality : head = value := by simpa [listGet?] using lookup
          simp [equality]
      | succ index =>
          exact List.mem_cons_of_mem head
            (inductionHypothesis index (by simpa [listGet?] using lookup))

theorem listGet?_eq_some_get {α : Type*} (values : List α) (index : Fin values.length) :
    listGet? values index = some (values.get index) := by
  induction values with
  | nil => exact Fin.elim0 index
  | cons value values inductionHypothesis =>
      refine Fin.cases ?_ (fun tail => ?_) index
      · rfl
      · simpa [listGet?] using inductionHypothesis tail

/-- Enumerate a list from a supplied starting index. -/
def enumerateFrom {α : Type*} : ℕ → List α → List (ℕ × α)
  | _, [] => []
  | index, value :: rest => (index, value) :: enumerateFrom (index + 1) rest

/-- Enumerate a list from zero. -/
def enumerate {α : Type*} (values : List α) : List (ℕ × α) :=
  enumerateFrom 0 values

/-- Local list bind. -/
def listBind {α β : Type*} (values : List α) (f : α → List β) : List β :=
  values.foldr (fun value acc => f value ++ acc) []

/-- Elements currently needed by parser intake, plus wildcard atoms.

Sodium, silicon, and germanium are accepted in bracketed validation-suite input even though they
are not members of the unbracketed OpenSMILES organic subset. -/
inductive Element where
  | wildcard
  | H
  | B
  | C
  | N
  | O
  | F
  | P
  | S
  | Na
  | Si
  | Ge
  | As
  | Se
  | Sn
  | Sb
  | Te
  | Pb
  | Bi
  | Cl
  | Br
  | I
  deriving DecidableEq, Repr

namespace Element

/-- Atomic number used by the existing CIP graph layer.  Wildcards intentionally receive `0`. -/
def atomicNumber : Element → AtomicNumber
  | wildcard => 0
  | H => 1
  | B => 5
  | C => 6
  | N => 7
  | O => 8
  | F => 9
  | P => 15
  | S => 16
  | Na => 11
  | Si => 14
  | Ge => 32
  | As => 33
  | Se => 34
  | Sn => 50
  | Sb => 51
  | Te => 52
  | Pb => 82
  | Bi => 83
  | Cl => 17
  | Br => 35
  | I => 53

/-- Elements that can reasonably receive aromatic lowercase input in OpenSMILES-style syntax. -/
def aromaticEligible : Element → Bool
  | B | C | N | O | P | S | wildcard => true
  | _ => false

/-- Organic-subset default valence table for lightweight validation. -/
def allowedValences : Element → List ℕ
  | wildcard => []
  | H => [1]
  | B => [3]
  | C => [4]
  | N => [3, 4]
  | O => [1, 2, 3]
  | F => [1]
  | P => [3, 5]
  | S => [2, 4, 6]
  | Na => [1]
  | Si => [4]
  | Ge => [4]
  | As => [3, 5]
  | Se => [2, 4, 6]
  | Sn => [2, 4]
  | Sb => [3, 5]
  | Te => [2, 4, 6]
  | Pb => [2, 4]
  | Bi => [3, 5]
  | Cl => [1]
  | Br => [1]
  | I => [1]

end Element

/-- Tetrahedral atom-parity annotation from `@`/`@@`-style input. -/
inductive TetrahedralInputParity where
  | anticlockwise
  | clockwise
  deriving DecidableEq, Repr

/-- Input atom specification.

`explicitHydrogens?` also records the SMILES implicit-hydrogen policy: `none` means an unbracketed
organic-subset atom whose hydrogens are filled from its default valence, while `some n` means a
bracket atom with exactly `n` attached hydrogens.  In particular, a bracket atom with no `H` suffix
stores `some 0`; OpenSMILES does not infer hydrogens inside brackets. -/
structure AtomSpec where
  element : Element
  isotope? : Option ℕ := none
  charge : Int := 0
  explicitHydrogens? : Option ℕ := none
  aromatic : Bool := false
  tetrahedral? : Option TetrahedralInputParity := none
  deriving DecidableEq, Repr

namespace AtomSpec

/-- Ordinary aliphatic atom specification. -/
def aliphatic (element : Element) : AtomSpec where
  element := element

/-- Aromatic atom specification. -/
def aromaticAtom (element : Element) : AtomSpec where
  element := element
  aromatic := true

/-- Explicit hydrogens counted as valence demand. -/
def explicitHydrogens (atom : AtomSpec) : ℕ :=
  atom.explicitHydrogens?.getD 0

/-- Atom-specific allowed valence table, with aromatic atoms using the SMILES-style aromatic
valence layer rather than ordinary localized valence. -/
def allowedValences (atom : AtomSpec) : List ℕ :=
  if atom.aromatic then
    match atom.element with
    | Element.C | Element.B | Element.N => [3]
    | Element.O | Element.S | Element.P => [2, 3]
    | Element.wildcard => []
    | _ => atom.element.allowedValences
  else
    match atom.element with
    | Element.B => if atom.charge < 0 then [3, 4] else atom.element.allowedValences
    | _ => atom.element.allowedValences

/-- Whether the atom can be a mobile-hydrogen donor in the lightweight tautomer layer. -/
def mobileHydrogenDonor (atom : AtomSpec) : Bool :=
  atom.explicitHydrogens > 0 &&
    match atom.element with
    | Element.N | Element.O | Element.S | Element.P => true
    | _ => false

/-- Whether the atom can receive a mobile hydrogen in the lightweight tautomer layer. -/
def mobileHydrogenAcceptor (atom : AtomSpec) : Bool :=
  match atom.element with
  | Element.N | Element.O | Element.S | Element.P => true
  | _ => false

/-- Lightweight π-electron contribution used by the aromaticity validator. -/
def piElectronContribution (atom : AtomSpec) : ℕ :=
  if atom.aromatic then
    match atom.element with
    | Element.N | Element.O | Element.S | Element.P => 2
    | _ => 1
  else
    0

end AtomSpec

/-- Parsed bond kinds, including directional stereobond markers. -/
inductive ParsedBondKind where
  | unspecified
  | single
  | double
  | triple
  | aromatic
  | up
  | down
  deriving DecidableEq, Repr

namespace ParsedBondKind

/-- Bond order seen by the current graph/CIP layer.  Directional single bonds still have order 1. -/
def order : ParsedBondKind → BondOrder
  | unspecified => 1
  | single => 1
  | double => 2
  | triple => 3
  | aromatic => 1
  | up => 1
  | down => 1

/-- Whether this bond carries a directional stereochemical marker. -/
def directional? : ParsedBondKind → Option Bool
  | up => some true
  | down => some false
  | _ => none

end ParsedBondKind

/-- A parsed bond between atom indices. -/
structure RawBond where
  source : ℕ
  target : ℕ
  kind : ParsedBondKind
  deriving DecidableEq, Repr

namespace RawBond

/-- Undirected incidence test. -/
def connects (bond : RawBond) (u v : ℕ) : Bool :=
  (bond.source == u && bond.target == v) || (bond.source == v && bond.target == u)

/-- Directed incidence test. -/
def directedConnects (bond : RawBond) (u v : ℕ) : Bool :=
  bond.source == u && bond.target == v

/-- Orientation-independent identity of one raw molecular edge.  Bond-record uniqueness is stated
on this key because two oppositely oriented or differently typed records still denote the same
constitutional edge and would otherwise be expanded twice by occurrence-sensitive consumers. -/
def edgeKey (bond : RawBond) : ℕ × ℕ :=
  (min bond.source bond.target, max bond.source bond.target)

end RawBond

/-- Parsed molecule before proof-level graph conversion. -/
structure RawMolecule where
  atoms : List AtomSpec
  bonds : List RawBond
  /-- Neighbours of each atom in OpenSMILES written order.

  A ring bond occupies a *different* position in each of its two endpoints' orders — the position
  where that endpoint's ring digit was written — so a single global bond list cannot express both.
  The parser records the per-atom order here; it is empty for molecules built by hand, and consumers
  fall back to bond-list order in that case. -/
  neighborOrder : List (List ℕ) := []
  /-- Source-token introduction predecessors, indexed by atom. A missing entry means that source
  history is unknown (the legacy hand-built representation); `some none` on lookup records a
  component root, while `some (some parent)` records the atom from which this atom was introduced.
  Ring-closure bonds do not change this history. Hydrogen materialization preserves this original
  prefix: generated hydrogen atoms did not have source atom tokens. -/
  introductionPredecessors : List (Option ℕ) := []
  deriving DecidableEq, Repr

namespace RawMolecule

/-- Number of parsed atoms. -/
def atomCount (mol : RawMolecule) : ℕ :=
  mol.atoms.length

/-- Lookup an atom specification by parser index. -/
def atomAt? (mol : RawMolecule) (idx : ℕ) : Option AtomSpec :=
  listGet? mol.atoms idx

/-- Exact Rule-2 datum for one parser element/isotope spelling. Source decimal values are scaled by
`10^12`; an unknown wildcard or a mass number absent from the frozen AME table returns `none`. -/
def rule2MassPico? (element : Element) (isotope? : Option ℕ) : Option ℕ :=
  if element = .wildcard then none
  else CIPRule2MassData.rule2MassPico? element.atomicNumber isotope?

/-- Total internal key. Public production admission proves that the `0` fallback is unreachable. -/
def rule2MassPico (element : Element) (isotope? : Option ℕ) : ℕ :=
  (rule2MassPico? element isotope?).getD 0

/-- Optional exact Rule-2 mass of a parsed atom. -/
def atomMassAt? (mol : RawMolecule) (idx : ℕ) : Option ℕ := do
  let spec ← mol.atomAt? idx
  rule2MassPico? spec.element spec.isotope?

/-- Exact picodalton-scaled Rule-2 key of a parsed atom, or the internal fallback for an absent atom
or an unadmitted atom spelling. -/
def atomMassAt (mol : RawMolecule) (idx : ℕ) : ℕ := (mol.atomMassAt? idx).getD 0

/-- Every real parsed atom has a source-backed Rule-2 mass. -/
def Rule2MassesKnown (mol : RawMolecule) : Prop :=
  ∀ atom, atom ∈ mol.atoms → ∃ mass, rule2MassPico? atom.element atom.isotope? = some mass

def rule2MassesKnown? (mol : RawMolecule) : Bool :=
  mol.atoms.all fun atom => (rule2MassPico? atom.element atom.isotope?).isSome

@[simp] theorem rule2MassesKnown?_eq_true_iff (mol : RawMolecule) :
    mol.rule2MassesKnown? = true ↔ mol.Rule2MassesKnown := by
  constructor
  · intro accepted atom membership
    have present := (List.all_eq_true.mp accepted) atom membership
    exact Option.isSome_iff_exists.mp present
  · intro known
    apply List.all_eq_true.mpr
    intro atom membership
    exact Option.isSome_iff_exists.mpr (known atom membership)

/-- On admitted parser molecules, every real atom key is exactly the source lookup and cannot be
the internal fallback. -/
theorem atomMassAt_eq_of_rule2MassesKnown (mol : RawMolecule) (known : mol.Rule2MassesKnown)
    (idx : ℕ) (spec : AtomSpec) (observed : mol.atomAt? idx = some spec) :
    ∃ mass, rule2MassPico? spec.element spec.isotope? = some mass ∧ mol.atomMassAt idx = mass := by
  have membership : spec ∈ mol.atoms :=
    listGet?_eq_some_implies_mem mol.atoms idx spec (by simpa [atomAt?] using observed)
  obtain ⟨mass, massObserved⟩ := known spec membership
  refine ⟨mass, massObserved, ?_⟩
  simp [atomMassAt, atomMassAt?, observed, massObserved]

/-- Default bond between two atoms when no explicit bond token is present. -/
def defaultBondKind (left right : AtomSpec) : ParsedBondKind :=
  if left.aromatic && right.aromatic then ParsedBondKind.aromatic else ParsedBondKind.single

/-- Directed bond order contribution. -/
def directedBondOrder (mol : RawMolecule) (u v : ℕ) : BondOrder :=
  mol.bonds.foldl
    (fun order bond =>
      if bond.directedConnects u v then max order bond.kind.order else order)
    0

/-- Symmetric bond order seen by `MoleculeGraph`. -/
def bondOrder (mol : RawMolecule) (u v : ℕ) : BondOrder :=
  if u = v then 0 else max (mol.directedBondOrder u v) (mol.directedBondOrder v u)

/-- Neighbours of an atom in OpenSMILES written order.

Uses the parser's recorded order when present, because a ring bond sits at a different position in
each of its two endpoints' orders and the bond list can only express one of them.  Falls back to
bond-list order for molecules built by hand. -/
def writtenNeighbors (mol : RawMolecule) (idx : ℕ) : List ℕ :=
  match mol.neighborOrder[idx]? with
  | some order => order
  | none =>
      mol.bonds.filterMap fun bond =>
        if bond.source == idx then some bond.target
        else if bond.target == idx then some bond.source
        else none

/-- Executable exactness check for the stored/fallback written-neighbour view.

For every real center, the list must be duplicate-free, every listed index must be a real atom,
and membership for every real atom must agree exactly with positive molecular bond order. -/
def writtenNeighborExact? (mol : RawMolecule) : Bool :=
  (List.range mol.atomCount).all fun center =>
    let neighbors := mol.writtenNeighbors center
    decide neighbors.Nodup &&
      neighbors.all (fun ligand => decide (ligand < mol.atomCount)) &&
      (List.range mol.atomCount).all fun ligand =>
        decide (ligand ∈ neighbors ↔ 0 < mol.bondOrder center ligand)

/-- Exact integrity of the written-neighbour view consumed by stereochemical perception.

This rules out both invented ligands and silently omitted ligands in a hand-built `neighborOrder`;
either defect can change an OpenSMILES parity permutation or the perceived ligand count. -/
def WrittenNeighborExact (mol : RawMolecule) : Prop :=
  mol.writtenNeighborExact? = true

/-- Internal consistency of the available source-introduction prefix. This checks chronology,
actual directed introduction edges and their first-neighbor position. It cannot authenticate a
claimed component root against an absent original source string. Empty legacy metadata is accepted;
a materialized molecule may retain only its original source-atom prefix. -/
def introductionPredecessorsValid? (mol : RawMolecule) : Bool :=
  decide (mol.introductionPredecessors.length ≤ mol.atomCount) &&
    (List.range mol.introductionPredecessors.length).all fun index =>
      match mol.introductionPredecessors[index]? with
      | none => false
      | some none => true
      | some (some parent) =>
          decide (parent < index) &&
            mol.bonds.any (fun bond => bond.source == parent && bond.target == index) &&
              ((mol.writtenNeighbors index).head? == some parent)

/-- Parser output has source-introduction metadata for every parsed atom. -/
def parserIntroductionValid? (mol : RawMolecule) : Bool :=
  decide (mol.introductionPredecessors.length = mol.atomCount) &&
    mol.introductionPredecessorsValid?

/-- Endpoint validity for a parsed bond. -/
def BondEndpointsOK (mol : RawMolecule) (bond : RawBond) : Prop :=
  bond.source < mol.atomCount ∧ bond.target < mol.atomCount ∧ bond.source ≠ bond.target

/-- Basic parser well-formedness: every bond points to two distinct parsed atoms. -/
def WellFormed (mol : RawMolecule) : Prop :=
  ∀ bond, bond ∈ mol.bonds → mol.BondEndpointsOK bond

/-- Occurrence-sensitive uniqueness of unordered raw bond records.

This is stronger than `mol.bonds.Nodup`: reversed or differently typed records for the same atom
pair are also rejected. -/
def BondRecordsUnique (mol : RawMolecule) : Prop :=
  (mol.bonds.map RawBond.edgeKey).Nodup

/-- The single structural admission contract shared by parser output, external bridge packets, and
proof-facing production hierarchy construction. -/
def Admissible (mol : RawMolecule) : Prop :=
  mol.WellFormed ∧ mol.BondRecordsUnique

/-- Full structural admission required by stereochemical consumers.  `Admissible` validates the
edge records themselves; this additional clause validates the per-atom written-neighbour view from
which parity frames and physical CIP roots are constructed. -/
def StereochemicalAdmissible (mol : RawMolecule) : Prop :=
  mol.Admissible ∧ mol.WrittenNeighborExact

/-- Executable endpoint check reflected by `BondEndpointsOK`. -/
def bondEndpointsOK? (mol : RawMolecule) (bond : RawBond) : Bool :=
  decide (bond.source < mol.atomCount) &&
    decide (bond.target < mol.atomCount) &&
      decide (bond.source ≠ bond.target)

/-- Executable unordered-edge uniqueness check. -/
def bondRecordsUnique? (mol : RawMolecule) : Bool :=
  decide (mol.bonds.map RawBond.edgeKey).Nodup

/-- Executable reflection of the complete raw-molecule admission contract. -/
def admissible? (mol : RawMolecule) : Bool :=
  mol.bonds.all (mol.bondEndpointsOK?) && mol.bondRecordsUnique?

/-- Executable stereochemical admission: structural edge validity plus an exact written-neighbour
view. -/
def stereochemicalAdmissible? (mol : RawMolecule) : Bool :=
  mol.admissible? && mol.writtenNeighborExact?

@[simp] theorem bondEndpointsOK?_eq_true_iff (mol : RawMolecule) (bond : RawBond) :
    mol.bondEndpointsOK? bond = true ↔ mol.BondEndpointsOK bond := by
  simp only [bondEndpointsOK?, Bool.and_eq_true, decide_eq_true_eq, BondEndpointsOK]
  tauto

theorem wellFormed_iff_all_bondEndpointsOK (mol : RawMolecule) :
    mol.WellFormed ↔ mol.bonds.all (mol.bondEndpointsOK?) = true := by
  simp only [WellFormed, List.all_eq_true, bondEndpointsOK?_eq_true_iff]

@[simp] theorem bondRecordsUnique?_eq_true_iff (mol : RawMolecule) :
    mol.bondRecordsUnique? = true ↔ mol.BondRecordsUnique := by
  simp [bondRecordsUnique?, BondRecordsUnique]

/-- Kernel reflection theorem for the unified executable admission boundary. -/
@[simp] theorem admissible?_eq_true_iff (mol : RawMolecule) :
    mol.admissible? = true ↔ mol.Admissible := by
  rw [admissible?, Bool.and_eq_true, bondRecordsUnique?_eq_true_iff,
    ← wellFormed_iff_all_bondEndpointsOK]
  rfl

@[simp] theorem writtenNeighborExact?_eq_true_iff (mol : RawMolecule) :
    mol.writtenNeighborExact? = true ↔ mol.WrittenNeighborExact := by
  rfl

/-- Relational form of the finite written-neighbour exactness check at one real center. -/
theorem WrittenNeighborExact.at (mol : RawMolecule) (exact : mol.WrittenNeighborExact)
    (center : Fin mol.atomCount) :
    (mol.writtenNeighbors center.val).Nodup ∧
      (∀ ligand, ligand ∈ mol.writtenNeighbors center.val → ligand < mol.atomCount) ∧
      ∀ ligand : Fin mol.atomCount,
        ligand.val ∈ mol.writtenNeighbors center.val ↔
          0 < mol.bondOrder center.val ligand.val := by
  have centerChecked :=
    (List.all_eq_true.mp exact) center.val (List.mem_range.mpr center.isLt)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at centerChecked
  refine ⟨centerChecked.1.1, ?_, ?_⟩
  · intro ligand member
    have bounded :=
      (List.all_eq_true.mp centerChecked.1.2) ligand member
    exact of_decide_eq_true bounded
  · intro ligand
    have compared :=
      (List.all_eq_true.mp centerChecked.2) ligand.val
        (List.mem_range.mpr ligand.isLt)
    exact of_decide_eq_true compared

/-- Construct exact written-neighbour admission from its relational clauses at every real center. -/
theorem WrittenNeighborExact.of_at (mol : RawMolecule)
    (exact : ∀ center : Fin mol.atomCount,
      (mol.writtenNeighbors center.val).Nodup ∧
        (∀ ligand, ligand ∈ mol.writtenNeighbors center.val → ligand < mol.atomCount) ∧
        ∀ ligand : Fin mol.atomCount,
          ligand.val ∈ mol.writtenNeighbors center.val ↔
            0 < mol.bondOrder center.val ligand.val) :
    mol.WrittenNeighborExact := by
  rw [WrittenNeighborExact, writtenNeighborExact?, List.all_eq_true]
  intro center centerMem
  have centerLt : center < mol.atomCount := List.mem_range.mp centerMem
  have clauses := exact ⟨center, centerLt⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨clauses.1, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro ligand ligandMem
    exact decide_eq_true (clauses.2.1 ligand ligandMem)
  · rw [List.all_eq_true]
    intro ligand ligandMem
    have ligandLt : ligand < mol.atomCount := List.mem_range.mp ligandMem
    exact decide_eq_true (clauses.2.2 ⟨ligand, ligandLt⟩)

/-- Preserve a valid preferred order, delete any invalid/duplicate entries, and append every
genuinely bonded atom that the preferred row omitted. -/
def exactWrittenNeighbors (mol : RawMolecule) (center : ℕ) : List ℕ :=
  let bonded := (List.range mol.atomCount).filter fun ligand =>
    decide (0 < mol.bondOrder center ligand)
  let preferred := (mol.writtenNeighbors center).filter (fun ligand =>
    decide (ligand < mol.atomCount ∧ 0 < mol.bondOrder center ligand)) |>.dedup
  preferred ++ bonded.filter fun ligand => decide (ligand ∉ preferred)

/-- Canonicalize only the stored written-neighbour table; atoms and bonds are unchanged. -/
def withExactWrittenNeighbors (mol : RawMolecule) : RawMolecule :=
  { mol with neighborOrder := (List.range mol.atomCount).map mol.exactWrittenNeighbors }

@[simp] theorem withExactWrittenNeighbors_atoms (mol : RawMolecule) :
    mol.withExactWrittenNeighbors.atoms = mol.atoms := rfl

@[simp] theorem withExactWrittenNeighbors_bonds (mol : RawMolecule) :
    mol.withExactWrittenNeighbors.bonds = mol.bonds := rfl

@[simp] theorem withExactWrittenNeighbors_atomCount (mol : RawMolecule) :
    mol.withExactWrittenNeighbors.atomCount = mol.atomCount := rfl

private theorem getElem?_map_range_exact {α : Type} (f : ℕ → α)
    (n idx : ℕ) (lt : idx < n) :
    ((List.range n).map f)[idx]? = some (f idx) := by
  rw [List.getElem?_eq_getElem (by simp [lt])]
  simp

@[simp] theorem withExactWrittenNeighbors_writtenNeighbors
    (mol : RawMolecule) (center : Fin mol.withExactWrittenNeighbors.atomCount) :
    mol.withExactWrittenNeighbors.writtenNeighbors center.val =
      mol.exactWrittenNeighbors center.val := by
  unfold withExactWrittenNeighbors writtenNeighbors
  have centerLt : center.val < mol.atomCount := by simp
  change (match ((List.range mol.atomCount).map mol.exactWrittenNeighbors)[center.val]? with
    | some order => order
    | none => _) = _
  rw [getElem?_map_range_exact _ _ _ centerLt]

theorem exactWrittenNeighbors_nodup (mol : RawMolecule) (center : ℕ) :
    (mol.exactWrittenNeighbors center).Nodup := by
  unfold exactWrittenNeighbors
  rw [List.nodup_append]
  refine ⟨List.nodup_dedup _, (List.nodup_range.filter _).filter _, ?_⟩
  intro first firstMem second secondMem equal
  subst second
  have rejected := of_decide_eq_true (List.mem_filter.mp secondMem).2
  exact rejected firstMem

theorem exactWrittenNeighbors_bound (mol : RawMolecule) (center ligand : ℕ)
    (member : ligand ∈ mol.exactWrittenNeighbors center) : ligand < mol.atomCount := by
  unfold exactWrittenNeighbors at member
  rcases List.mem_append.mp member with preferred | bonded
  · have raw : ligand ∈ (mol.writtenNeighbors center).filter (fun ligand =>
        decide (ligand < mol.atomCount ∧ 0 < mol.bondOrder center ligand)) :=
      List.mem_dedup.mp preferred
    exact (of_decide_eq_true (List.mem_filter.mp raw).2).1
  · have checked := List.mem_filter.mp bonded
    exact List.mem_range.mp (List.mem_filter.mp checked.1).1

theorem mem_exactWrittenNeighbors_iff (mol : RawMolecule)
    (center ligand : Fin mol.atomCount) :
    ligand.val ∈ mol.exactWrittenNeighbors center.val ↔
      0 < mol.bondOrder center.val ligand.val := by
  unfold exactWrittenNeighbors
  constructor
  · intro member
    rcases List.mem_append.mp member with preferredMember | bondedMember
    · have raw : ligand.val ∈
          (mol.writtenNeighbors center.val).filter (fun candidate =>
            decide (candidate < mol.atomCount ∧
              0 < mol.bondOrder center.val candidate)) :=
        List.mem_dedup.mp preferredMember
      exact (of_decide_eq_true (List.mem_filter.mp raw).2).2
    · have inBonded := (List.mem_filter.mp bondedMember).1
      exact of_decide_eq_true (List.mem_filter.mp inBonded).2
  · intro positive
    let preferred := (mol.writtenNeighbors center.val).filter (fun candidate =>
      decide (candidate < mol.atomCount ∧
        0 < mol.bondOrder center.val candidate)) |>.dedup
    by_cases already : ligand.val ∈ preferred
    · exact List.mem_append_left _ already
    · apply List.mem_append_right preferred
      apply List.mem_filter.mpr
      refine ⟨?_, decide_eq_true already⟩
      apply List.mem_filter.mpr
      exact ⟨List.mem_range.mpr ligand.isLt, decide_eq_true positive⟩

/-- Exact-neighbour normalization always establishes the complete relational certificate. -/
theorem withExactWrittenNeighbors_writtenNeighborExact (mol : RawMolecule) :
    mol.withExactWrittenNeighbors.WrittenNeighborExact := by
  apply WrittenNeighborExact.of_at
  intro center
  refine ⟨?_, ?_, ?_⟩
  · simpa using exactWrittenNeighbors_nodup mol center.val
  · intro ligand member
    exact exactWrittenNeighbors_bound mol center.val ligand (by simpa using member)
  · intro ligand
    let sourceCenter : Fin mol.atomCount := ⟨center.val, by simp⟩
    let sourceLigand : Fin mol.atomCount := ⟨ligand.val, by simp⟩
    rw [withExactWrittenNeighbors_writtenNeighbors]
    change ligand.val ∈ mol.exactWrittenNeighbors center.val ↔
      0 < mol.bondOrder center.val ligand.val
    have result := mem_exactWrittenNeighbors_iff mol sourceCenter sourceLigand
    simpa [sourceCenter, sourceLigand] using result

@[simp] theorem withExactWrittenNeighbors_admissible_iff (mol : RawMolecule) :
    mol.withExactWrittenNeighbors.Admissible ↔ mol.Admissible := by
  rfl

/-- Canonicalization is observationally the identity on an already exact real-center row. -/
theorem exactWrittenNeighbors_eq_of_exact (mol : RawMolecule)
    (exact : mol.WrittenNeighborExact) (center : Fin mol.atomCount) :
    mol.exactWrittenNeighbors center.val = mol.writtenNeighbors center.val := by
  have clauses := WrittenNeighborExact.at mol exact center
  unfold exactWrittenNeighbors
  have preferredFilter :
      (mol.writtenNeighbors center.val).filter (fun ligand =>
        decide (ligand < mol.atomCount ∧ 0 < mol.bondOrder center.val ligand)) =
        mol.writtenNeighbors center.val := by
    apply List.filter_eq_self.mpr
    intro ligand member
    have bound := clauses.2.1 ligand member
    let asFin : Fin mol.atomCount := ⟨ligand, bound⟩
    exact decide_eq_true ⟨bound, (clauses.2.2 asFin).mp member⟩
  rw [preferredFilter, List.dedup_eq_self.mpr clauses.1]
  have missingNil :
      ((List.range mol.atomCount).filter (fun ligand =>
        decide (0 < mol.bondOrder center.val ligand))).filter (fun ligand =>
          decide (ligand ∉ mol.writtenNeighbors center.val)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro ligand inBonded
    have ligandRange := (List.mem_filter.mp inBonded).1
    have positive := of_decide_eq_true (List.mem_filter.mp inBonded).2
    let asFin : Fin mol.atomCount := ⟨ligand, List.mem_range.mp ligandRange⟩
    have present := (clauses.2.2 asFin).mpr positive
    simpa using present
  simp only [missingNil, List.append_nil]

/-- Kernel reflection theorem for the exact stereochemical intake boundary. -/
@[simp] theorem stereochemicalAdmissible?_eq_true_iff (mol : RawMolecule) :
    mol.stereochemicalAdmissible? = true ↔ mol.StereochemicalAdmissible := by
  simp [stereochemicalAdmissible?, StereochemicalAdmissible]

/-- Sum of bond orders incident at an atom. -/
def incidentBondOrderSum (mol : RawMolecule) (idx : ℕ) : ℕ :=
  mol.bonds.foldl
    (fun total bond =>
      if bond.source == idx || bond.target == idx then total + bond.kind.order else total)
    0

/-- Valence used at an atom, including explicit hydrogens. -/
def usedValenceAt (mol : RawMolecule) (idx : ℕ) : ℕ :=
  match mol.atomAt? idx with
  | none => 0
  | some atom => atom.explicitHydrogens + mol.incidentBondOrderSum idx

/-- Lightweight valence check at one atom. -/
def ValenceOKAt (mol : RawMolecule) (idx : ℕ) : Prop :=
  ∃ atom, mol.atomAt? idx = some atom ∧
    ∃ allowed, allowed ∈ atom.allowedValences ∧ mol.usedValenceAt idx ≤ allowed

/-- Lightweight valence check for every parsed atom. -/
def ValenceOK (mol : RawMolecule) : Prop :=
  ∀ idx atom, mol.atomAt? idx = some atom →
    ∃ allowed, allowed ∈ atom.allowedValences ∧ mol.usedValenceAt idx ≤ allowed

/-- Executable valence-table check at one parsed atom index. -/
def valenceOKAt? (mol : RawMolecule) (idx : ℕ) : Bool :=
  match mol.atomAt? idx with
  | none => false
  | some atom => atom.allowedValences.any fun allowed => decide (mol.usedValenceAt idx ≤ allowed)

/-- Executable valence-table check for every stored atom. -/
def valenceOK? (mol : RawMolecule) : Bool :=
  (List.range mol.atomCount).all mol.valenceOKAt?

@[simp] theorem valenceOKAt?_eq_true_iff (mol : RawMolecule) (idx : ℕ) :
    mol.valenceOKAt? idx = true ↔ mol.ValenceOKAt idx := by
  unfold valenceOKAt? ValenceOKAt
  cases lookup : mol.atomAt? idx with
  | none => simp
  | some atom => simp

@[simp] theorem valenceOK?_eq_true_iff (mol : RawMolecule) :
    mol.valenceOK? = true ↔ mol.ValenceOK := by
  rw [valenceOK?, List.all_eq_true]
  constructor
  · intro checked idx atom lookup
    have bound : idx < mol.atomCount := by
      exact listGet?_eq_some_implies_lt mol.atoms idx atom lookup
    have localCheck := checked idx (List.mem_range.mpr bound)
    rcases (mol.valenceOKAt?_eq_true_iff idx).mp localCheck with
      ⟨observed, observedLookup, supported⟩
    rw [lookup] at observedLookup
    cases observedLookup
    exact supported
  · intro valid idx member
    have bound : idx < mol.atomCount := List.mem_range.mp member
    rcases listGet?_exists_of_lt mol.atoms idx bound with ⟨atom, lookup⟩
    apply (mol.valenceOKAt?_eq_true_iff idx).mpr
    exact ⟨atom, lookup, valid idx atom lookup⟩

/-- Implied hydrogen count at an atom, when the valence table supplies a compatible target. -/
def implicitHydrogensAt? (mol : RawMolecule) (idx : ℕ) : Option ℕ :=
  match mol.atomAt? idx with
  | none => none
  | some atom =>
      (atom.allowedValences.find? fun allowed => mol.usedValenceAt idx ≤ allowed).map
        fun allowed => allowed - mol.usedValenceAt idx

/-- Resolve one unspecified raw bond without changing its endpoints. -/
def normalizeUnspecifiedBond (mol : RawMolecule) (bond : RawBond) : RawBond :=
  match bond.kind with
  | ParsedBondKind.unspecified =>
      let left := mol.atomAt? bond.source
      let right := mol.atomAt? bond.target
      let kind :=
        match left, right with
        | some a, some b => defaultBondKind a b
        | _, _ => ParsedBondKind.single
      { bond with kind := kind }
  | _ => bond

/-- Normalize unspecified bonds using the OpenSMILES aromatic/default-single convention. -/
def normalizeUnspecifiedBonds (mol : RawMolecule) : RawMolecule where
  neighborOrder := mol.neighborOrder
  introductionPredecessors := mol.introductionPredecessors
  atoms := mol.atoms
  bonds := mol.bonds.map mol.normalizeUnspecifiedBond

@[simp] theorem normalizeUnspecifiedBonds_atoms (mol : RawMolecule) :
    mol.normalizeUnspecifiedBonds.atoms = mol.atoms :=
  rfl

@[simp] theorem normalizeUnspecifiedBonds_rule2MassesKnown (mol : RawMolecule) :
    mol.normalizeUnspecifiedBonds.Rule2MassesKnown ↔ mol.Rule2MassesKnown := by
  rfl

@[simp] theorem normalizeUnspecifiedBonds_rule2MassesKnown? (mol : RawMolecule) :
    mol.normalizeUnspecifiedBonds.rule2MassesKnown? = mol.rule2MassesKnown? := by
  rfl

@[simp] theorem normalizeUnspecifiedBond_source (mol : RawMolecule) (bond : RawBond) :
    (mol.normalizeUnspecifiedBond bond).source = bond.source := by
  unfold normalizeUnspecifiedBond
  split <;> rfl

@[simp] theorem normalizeUnspecifiedBond_target (mol : RawMolecule) (bond : RawBond) :
    (mol.normalizeUnspecifiedBond bond).target = bond.target := by
  unfold normalizeUnspecifiedBond
  split <;> rfl

@[simp] theorem normalizeUnspecifiedBond_order (mol : RawMolecule) (bond : RawBond) :
    (mol.normalizeUnspecifiedBond bond).kind.order = bond.kind.order := by
  rcases bond with ⟨source, target, kind⟩
  cases kind with
  | unspecified =>
      simp only [normalizeUnspecifiedBond]
      cases sourceAtom : mol.atomAt? source with
      | none => rfl
      | some left =>
          cases targetAtom : mol.atomAt? target with
          | none => rfl
          | some right =>
              simp only [defaultBondKind]
              split <;> rfl
  | single | double | triple | aromatic | up | down => rfl

@[simp] theorem normalizeUnspecifiedBond_edgeKey (mol : RawMolecule) (bond : RawBond) :
    RawBond.edgeKey (mol.normalizeUnspecifiedBond bond) = RawBond.edgeKey bond := by
  simp [RawBond.edgeKey]

/-- Bond-kind normalization preserves endpoint validity. -/
theorem normalizeUnspecifiedBonds_wellFormed (mol : RawMolecule) :
    mol.WellFormed → mol.normalizeUnspecifiedBonds.WellFormed := by
  intro hwell bond hbond
  rw [normalizeUnspecifiedBonds] at hbond
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hbond
  have hendpoints := hwell source hsource
  simpa [BondEndpointsOK, atomCount] using hendpoints

/-- Bond-kind normalization preserves unordered bond-record uniqueness exactly. -/
theorem normalizeUnspecifiedBonds_bondRecordsUnique (mol : RawMolecule) :
    mol.BondRecordsUnique → mol.normalizeUnspecifiedBonds.BondRecordsUnique := by
  intro hunique
  simpa [BondRecordsUnique, normalizeUnspecifiedBonds, List.map_map,
    Function.comp_def] using hunique

/-- The actual normalized molecule consumed by the proof-facing engine retains the complete raw
admission certificate established at intake. -/
theorem normalizeUnspecifiedBonds_admissible (mol : RawMolecule) :
    mol.Admissible → mol.normalizeUnspecifiedBonds.Admissible := by
  rintro ⟨hwell, hunique⟩
  exact ⟨mol.normalizeUnspecifiedBonds_wellFormed hwell,
    mol.normalizeUnspecifiedBonds_bondRecordsUnique hunique⟩

private theorem normalizeUnspecifiedBonds_directedBondOrder_loop
    (mol : RawMolecule) (bonds : List RawBond) (u v initial : ℕ) :
    (bonds.map mol.normalizeUnspecifiedBond).foldl
        (fun order bond =>
          if bond.directedConnects u v then max order bond.kind.order else order)
        initial =
      bonds.foldl
        (fun order bond =>
          if bond.directedConnects u v then max order bond.kind.order else order)
        initial := by
  induction bonds generalizing initial with
  | nil => rfl
  | cons bond rest ih =>
      simp only [List.map_cons, List.foldl_cons]
      rw [ih]
      simp [RawBond.directedConnects]

@[simp] theorem normalizeUnspecifiedBonds_directedBondOrder
    (mol : RawMolecule) (u v : ℕ) :
    mol.normalizeUnspecifiedBonds.directedBondOrder u v = mol.directedBondOrder u v := by
  exact normalizeUnspecifiedBonds_directedBondOrder_loop mol mol.bonds u v 0

@[simp] theorem normalizeUnspecifiedBonds_bondOrder
    (mol : RawMolecule) (u v : ℕ) :
    mol.normalizeUnspecifiedBonds.bondOrder u v = mol.bondOrder u v := by
  simp [bondOrder]

@[simp] theorem normalizeUnspecifiedBonds_writtenNeighbors
    (mol : RawMolecule) (idx : ℕ) :
    mol.normalizeUnspecifiedBonds.writtenNeighbors idx = mol.writtenNeighbors idx := by
  unfold writtenNeighbors
  cases observed : mol.neighborOrder[idx]? with
  | some order => simp [normalizeUnspecifiedBonds, observed]
  | none =>
      simp only [normalizeUnspecifiedBonds, observed, List.filterMap_map]
      congr 1
      funext bond
      simp

theorem normalizeUnspecifiedBonds_writtenNeighborExact
    (mol : RawMolecule) :
    mol.WrittenNeighborExact → mol.normalizeUnspecifiedBonds.WrittenNeighborExact := by
  intro exact
  apply WrittenNeighborExact.of_at
  intro center
  change Fin mol.atomCount at center
  simpa only [normalizeUnspecifiedBonds_writtenNeighbors,
    normalizeUnspecifiedBonds_bondOrder, normalizeUnspecifiedBonds_atoms, atomCount] using
      WrittenNeighborExact.at mol exact center

/-- Bond normalization preserves the entire checked stereochemical intake contract. -/
theorem normalizeUnspecifiedBonds_stereochemicalAdmissible
    (mol : RawMolecule) :
    mol.StereochemicalAdmissible → mol.normalizeUnspecifiedBonds.StereochemicalAdmissible := by
  rintro ⟨admissible, exact⟩
  exact ⟨mol.normalizeUnspecifiedBonds_admissible admissible,
    mol.normalizeUnspecifiedBonds_writtenNeighborExact exact⟩

theorem bondOrder_self (mol : RawMolecule) (idx : ℕ) :
    mol.bondOrder idx idx = 0 := by
  simp [bondOrder]

theorem bondOrder_symm (mol : RawMolecule) (u v : ℕ) :
    mol.bondOrder u v = mol.bondOrder v u := by
  by_cases h : u = v
  · subst h
    simp [bondOrder]
  · have hvu : v ≠ u := by
      intro hv
      exact h hv.symm
    simp [bondOrder, h, hvu, Nat.max_comm]

/-- Convert a parsed molecule to the proof-facing molecular graph over `Fin atomCount`.

Rule 2 uses the same exact picodalton-scaled source lookup as the production hierarchical
comparator. `0` is only the total constructor's fallback for wildcard/unknown nuclide spellings;
authoritative public admission separately proves that fallback unreachable. -/
def toMoleculeGraph (mol : RawMolecule) : MoleculeGraph (Fin mol.atomCount) where
  atomZ := fun idx => (mol.atoms.get idx).element.atomicNumber
  atomMass := fun idx => mol.atomMassAt idx
  formalCharge := fun idx => (mol.atoms.get idx).charge
  bond := fun u v => mol.bondOrder u.val v.val
  bond_symm := by
    intro u v
    exact mol.bondOrder_symm u.val v.val
  bond_self := by
    intro u
    exact mol.bondOrder_self u.val

@[simp] theorem toMoleculeGraph_atomMass (mol : RawMolecule) (idx : Fin mol.atomCount) :
    mol.toMoleculeGraph.atomMass idx = mol.atomMassAt idx := rfl

end RawMolecule

/-! ### OpenSMILES-style parser -/

abbrev ParserError := String

/-- Ring opening while parsing.

`bondIndex` is the slot the ring-closure bond occupies in the bond list.  It is reserved when the
digit is *opened*, because that is where the ring neighbour sits in OpenSMILES neighbour order: the
digit is written immediately after its atom, before any branch or chain that follows.  Appending the
bond when the ring closes instead would place the ring neighbour last, transposing it past every
substituent written in between and mirroring the descriptor at any stereocentre on the ring. -/
structure RingOpening where
  digit : ℕ
  atom : ℕ
  bond? : Option ParsedBondKind
  bondIndex : ℕ
  orderIndex : ℕ
  deriving DecidableEq, Repr

/-- Parser state for an OpenSMILES-style recursive-descent pass. -/
structure ParseState where
  atoms : List AtomSpec := []
  bonds : List RawBond := []
  current? : Option ℕ := none
  branches : List ℕ := []
  rings : List RingOpening := []
  pendingBond? : Option ParsedBondKind := none
  order : List (List ℕ) := []
  introductionPredecessors : List (Option ℕ) := []
  deriving DecidableEq, Repr

namespace ParseState

/-- Parsed molecule stored in a parser state. -/
def molecule (state : ParseState) : RawMolecule where
  atoms := state.atoms
  bonds := state.bonds
  neighborOrder := state.order
  introductionPredecessors := state.introductionPredecessors

/-- Append `neighbour` to `atom`'s written neighbour order. -/
def noteOrder (order : List (List ℕ)) (atom neighbour : ℕ) : List (List ℕ) :=
  order.set atom ((order.getD atom []) ++ [neighbour])

/-- Next atom index. -/
def nextAtomId (state : ParseState) : ℕ :=
  state.atoms.length

/-- Add a bond with a resolved default if needed. -/
def addBond (state : ParseState) (source target : ℕ) (kind? : Option ParsedBondKind) :
    ParseState :=
  let mol := state.molecule
  let kind :=
    match kind? with
    | some kind => kind
    | none =>
        match mol.atomAt? source, mol.atomAt? target with
        | some left, some right => RawMolecule.defaultBondKind left right
        | _, _ => ParsedBondKind.single
  { state with bonds := state.bonds ++ [{ source := source, target := target, kind := kind }] }

/-- Add an atom and attach it to the previous atom when present. -/
def addAtom (state : ParseState) (atom : AtomSpec) : ParseState :=
  let newId := state.nextAtomId
  let withAtom :=
    { state with
      atoms := state.atoms ++ [atom]
      order := state.order ++ [[]]
      introductionPredecessors :=
        if state.introductionPredecessors.length = state.atoms.length then
          state.introductionPredecessors ++ [state.current?]
        else state.introductionPredecessors }
  match state.current? with
  | none => { withAtom with current? := some newId, pendingBond? := none }
  | some previous =>
      let linked := withAtom.addBond previous newId state.pendingBond?
      { linked with
        current? := some newId
        pendingBond? := none
        order := noteOrder (noteOrder linked.order previous newId) newId previous }

/-- Push the current atom as a branch point. -/
def pushBranch (state : ParseState) : Except ParserError ParseState :=
  match state.current? with
  | none => Except.error "branch opened before any atom"
  | some current => Except.ok { state with branches := current :: state.branches }

/-- Close a branch and restore its branch point. -/
def popBranch (state : ParseState) : Except ParserError ParseState :=
  match state.branches with
  | [] => Except.error "branch closed without a matching open parenthesis"
  | current :: rest => Except.ok { state with current? := some current, branches := rest }

/-- Find a ring opening by digit. -/
def findRing? (state : ParseState) (digit : ℕ) : Option RingOpening :=
  state.rings.find? fun opening => opening.digit == digit

/-- Remove all openings for a digit.  Well-formed parser states contain at most one. -/
def eraseRing (state : ParseState) (digit : ℕ) : ParseState :=
  { state with rings := state.rings.filter fun opening => !(opening.digit == digit) }

/-- Resolve the bond token associated with a ring closure. -/
def resolveRingBondKind (state : ParseState) (opening : RingOpening) (current : ℕ) :
    Except ParserError ParsedBondKind :=
  match opening.bond?, state.pendingBond? with
  | some left, some right =>
      if left = right then Except.ok left else Except.error "conflicting ring-closure bond markers"
  | some left, none => Except.ok left
  | none, some right => Except.ok right
  | none, none =>
      match state.molecule.atomAt? opening.atom, state.molecule.atomAt? current with
      | some left, some right => Except.ok (RawMolecule.defaultBondKind left right)
      | _, _ => Except.error "ring closure refers to a missing atom"

/-- Open or close a ring digit. -/
def handleRingDigit (state : ParseState) (digit : ℕ) : Except ParserError ParseState :=
  match state.current? with
  | none => Except.error "ring digit appeared before any atom"
  | some current =>
      match state.findRing? digit with
      | none =>
          -- Reserve the ring neighbour's slot now, with a self-bond placeholder that the closing
          -- digit overwrites.  Unclosed rings are rejected by `finalizeParseState`, so a
          -- placeholder never reaches a parsed molecule.
          Except.ok
            { state with
              rings :=
                { digit := digit, atom := current, bond? := state.pendingBond?
                  bondIndex := state.bonds.length
                  orderIndex := (state.order.getD current []).length } :: state.rings
              bonds :=
                state.bonds ++
                  [{ source := current, target := current, kind := ParsedBondKind.unspecified }]
              order := noteOrder state.order current current
              pendingBond? := none }
      | some opening => do
          let kind ← state.resolveRingBondKind opening current
          let openerOrder :=
            state.order.set opening.atom
              ((state.order.getD opening.atom []).set opening.orderIndex current)
          Except.ok
            { (state.eraseRing digit) with
              bonds :=
                state.bonds.set opening.bondIndex
                  { source := opening.atom, target := current, kind := kind }
              order := noteOrder openerOrder current opening.atom
              pendingBond? := none }

end ParseState

/-- Parse a decimal digit. -/
def digit? : Char → Option ℕ
  | '0' => some 0
  | '1' => some 1
  | '2' => some 2
  | '3' => some 3
  | '4' => some 4
  | '5' => some 5
  | '6' => some 6
  | '7' => some 7
  | '8' => some 8
  | '9' => some 9
  | _ => none

/-- Parse an element token from a character stream. -/
def parseElement? : List Char → Option (Element × Bool × List Char)
  | 'C' :: 'l' :: rest => some (Element.Cl, false, rest)
  | 'B' :: 'r' :: rest => some (Element.Br, false, rest)
  | 'N' :: 'a' :: rest => some (Element.Na, false, rest)
  | 'S' :: 'i' :: rest => some (Element.Si, false, rest)
  | 'G' :: 'e' :: rest => some (Element.Ge, false, rest)
  | 'A' :: 's' :: rest => some (Element.As, false, rest)
  | 'S' :: 'e' :: rest => some (Element.Se, false, rest)
  | 'S' :: 'n' :: rest => some (Element.Sn, false, rest)
  | 'S' :: 'b' :: rest => some (Element.Sb, false, rest)
  | 'T' :: 'e' :: rest => some (Element.Te, false, rest)
  | 'P' :: 'b' :: rest => some (Element.Pb, false, rest)
  | 'B' :: 'i' :: rest => some (Element.Bi, false, rest)
  | 'H' :: rest => some (Element.H, false, rest)
  | 'B' :: rest => some (Element.B, false, rest)
  | 'C' :: rest => some (Element.C, false, rest)
  | 'N' :: rest => some (Element.N, false, rest)
  | 'O' :: rest => some (Element.O, false, rest)
  | 'F' :: rest => some (Element.F, false, rest)
  | 'P' :: rest => some (Element.P, false, rest)
  | 'S' :: rest => some (Element.S, false, rest)
  | 'I' :: rest => some (Element.I, false, rest)
  | 'b' :: rest => some (Element.B, true, rest)
  | 'c' :: rest => some (Element.C, true, rest)
  | 'n' :: rest => some (Element.N, true, rest)
  | 'o' :: rest => some (Element.O, true, rest)
  | 'p' :: rest => some (Element.P, true, rest)
  | 's' :: rest => some (Element.S, true, rest)
  | '*' :: rest => some (Element.wildcard, false, rest)
  | _ => none

/-- Take characters until a closing bracket. -/
def takeBracketBody? : List Char → Option (List Char × List Char)
  | [] => none
  | ']' :: rest => some ([], rest)
  | c :: rest =>
      match takeBracketBody? rest with
      | none => none
      | some (body, tail) => some (c :: body, tail)

/-- Split leading decimal digits. -/
def takeDigits : List Char → List Char × List Char
  | [] => ([], [])
  | c :: rest =>
      match digit? c with
      | none => ([], c :: rest)
      | some _ =>
          let out := takeDigits rest
          (c :: out.1, out.2)

/-- Interpret a digit list as a natural number. -/
def digitsToNat : List Char → ℕ :=
  List.foldl
    (fun total c =>
      match digit? c with
      | none => total
      | some digit => 10 * total + digit)
    0

/-- Parsed, fully consumed suffix of a bracket atom.

The primary accepted order is `chirality? Hn? charge?`.  For compatibility with existing
stereochemical input, a terminal `charge chirality` form such as `[S+@@]` is also accepted, but it
cannot be followed by hydrogen or any other residue. -/
structure BracketAtomSuffix where
  parity? : Option TetrahedralInputParity := none
  explicitHydrogens : ℕ := 0
  charge : Int := 0
  deriving DecidableEq, Repr

/-- Consume an optional `@` or `@@` chirality token. -/
def takeBracketParity : List Char → Option TetrahedralInputParity × List Char
  | '@' :: '@' :: rest => (some TetrahedralInputParity.clockwise, rest)
  | '@' :: rest => (some TetrahedralInputParity.anticlockwise, rest)
  | rest => (none, rest)

/-- Consume optional bracket hydrogen syntax `H` or `Hn`, where `n` is one decimal digit.

Single-digit counts include `H0`, which is used to state explicitly that no hydrogen is attached.
Leaving a second digit unconsumed makes malformed inputs such as `H22` fail the suffix parser. -/
def takeBracketHydrogen : List Char → Option ℕ × List Char
  | 'H' :: c :: rest =>
      match digit? c with
      | some count => (some count, rest)
      | none => (some 1, c :: rest)
  | ['H'] => (some 1, [])
  | rest => (none, rest)

/-- Consume one exact bracket charge prefix.

Supported spellings are one sign, exactly two equal signs, or a sign followed by a positive decimal
magnitude.  Thus `+`, `++`, `+2`, `-`, `--`, and `-2` preserve their exact integer values.  Zero
magnitudes, longer or mixed sign runs, and doubled-sign-plus-digit forms are rejected by leaving
residue or no successful parse. -/
def parseBracketChargePrefix? : List Char → Option (Int × List Char)
  | '+' :: '+' :: rest => some (2, rest)
  | '+' :: rest =>
      let digitsAndRest := takeDigits rest
      if digitsAndRest.1.isEmpty then
        some (1, rest)
      else
        let magnitude := digitsToNat digitsAndRest.1
        if magnitude = 0 then none else some (Int.ofNat magnitude, digitsAndRest.2)
  | '-' :: '-' :: rest => some (-2, rest)
  | '-' :: rest =>
      let digitsAndRest := takeDigits rest
      if digitsAndRest.1.isEmpty then
        some (-1, rest)
      else
        let magnitude := digitsToNat digitsAndRest.1
        if magnitude = 0 then none else some (-(Int.ofNat magnitude), digitsAndRest.2)
  | _ => none

/-- Parse and completely consume the standard ordered bracket suffix. -/
def parseStandardBracketSuffix? (chars : List Char) : Option BracketAtomSuffix :=
  let parityAndRest := takeBracketParity chars
  let hydrogenAndRest := takeBracketHydrogen parityAndRest.2
  match hydrogenAndRest.2 with
  | [] =>
      some
        { parity? := parityAndRest.1
          explicitHydrogens := hydrogenAndRest.1.getD 0 }
  | rest =>
      match parseBracketChargePrefix? rest with
      | some (charge, []) =>
          some
            { parity? := parityAndRest.1
              explicitHydrogens := hydrogenAndRest.1.getD 0
              charge := charge }
      | _ => none

/-- Parse the deliberately narrow legacy terminal `charge chirality` form. -/
def parseLegacyChargeParitySuffix? (chars : List Char) : Option BracketAtomSuffix :=
  match parseBracketChargePrefix? chars with
  | some (charge, rest) =>
      let parityAndRest := takeBracketParity rest
      match parityAndRest with
      | (some parity, []) => some { parity? := some parity, charge := charge }
      | _ => none
  | none => none

/-- Parse one bracket suffix with complete consumption and no ignored residue. -/
def parseBracketSuffix? (chars : List Char) : Option BracketAtomSuffix :=
  match parseStandardBracketSuffix? chars with
  | some suffix => some suffix
  | none => parseLegacyChargeParitySuffix? chars

/-- Parse a bracket atom body. -/
def parseBracketAtomBody? (body : List Char) : Option AtomSpec :=
  let digitsAndRest := takeDigits body
  let isotope? := if digitsAndRest.1 = [] then none else some (digitsToNat digitsAndRest.1)
  match parseElement? digitsAndRest.2 with
  | none => none
  | some (element, aromatic, rest) =>
      match parseBracketSuffix? rest with
      | none => none
      | some suffix =>
          some
            { element := element
              isotope? := isotope?
              charge := suffix.charge
              explicitHydrogens? := some suffix.explicitHydrogens
              aromatic := aromatic
              tetrahedral? := suffix.parity? }

/-- Parse an atom token. -/
def parseAtomToken? : List Char → Option (AtomSpec × List Char)
  | '[' :: rest =>
      match takeBracketBody? rest with
      | none => none
      | some (body, tail) =>
          match parseBracketAtomBody? body with
          | none => none
          | some atom => some (atom, tail)
  | chars =>
      match parseElement? chars with
      | none => none
      | some (element, aromatic, rest) =>
          some ({ element := element, aromatic := aromatic }, rest)

/-- Parse a bond marker. -/
def parseBondToken? : Char → Option ParsedBondKind
  | '-' => some ParsedBondKind.single
  | '=' => some ParsedBondKind.double
  | '#' => some ParsedBondKind.triple
  | ':' => some ParsedBondKind.aromatic
  | '/' => some ParsedBondKind.up
  | '\\' => some ParsedBondKind.down
  | _ => none

/-- Parse a ring digit token, including `%NN`. -/
def parseRingToken? : List Char → Option (ℕ × List Char)
  | '%' :: a :: b :: rest =>
      match digit? a, digit? b with
      | some tens, some ones => some (10 * tens + ones, rest)
      | _, _ => none
  | c :: rest =>
      match digit? c with
      | some 0 => none
      | some n => some (n, rest)
      | none => none
  | [] => none

/-- Fuelled core of the OpenSMILES-style parser.  Every successful token parse consumes at least one
input character, so `chars.length + 1` fuel is sufficient for the public entry point below. -/
def parseCharsFuel : ℕ → List Char → ParseState → Except ParserError ParseState
  | 0, _, _ => Except.error "parser fuel exhausted"
  | _ + 1, [], state => Except.ok state
  | fuel + 1, '.' :: rest, state =>
      parseCharsFuel fuel rest { state with current? := none, pendingBond? := none }
  | fuel + 1, '(' :: rest, state => do
      let state ← state.pushBranch
      parseCharsFuel fuel rest state
  | fuel + 1, ')' :: rest, state => do
      let state ← state.popBranch
      parseCharsFuel fuel rest state
  | fuel + 1, chars, state =>
      match parseAtomToken? chars with
      | some (atom, rest) => parseCharsFuel fuel rest (state.addAtom atom)
      | none =>
          match chars with
          | [] => Except.ok state
          | c :: rest =>
              match parseBondToken? c with
              | some bond =>
                  parseCharsFuel fuel rest { state with pendingBond? := some bond }
              | none =>
                  match parseRingToken? chars with
                  | some (digit, rest) => do
                      let state ← state.handleRingDigit digit
                      parseCharsFuel fuel rest state
                  | none => Except.error "unrecognized OpenSMILES token"

/-- Recursive OpenSMILES-style parser.  This definition is total and kernel-reducible. -/
def parseChars (chars : List Char) (state : ParseState) : Except ParserError ParseState :=
  parseCharsFuel (chars.length + 1) chars state

/-- Finalize a parser state. -/
def finalizeParseState (state : ParseState) : Except ParserError RawMolecule :=
  if state.branches = [] then
    if state.rings = [] then
      if state.pendingBond? = none then
        let molecule := state.molecule.normalizeUnspecifiedBonds
        if molecule.admissible? then
          Except.ok molecule
        else
          Except.error "parsed molecule contains a self-loop, invalid endpoint, or duplicate edge"
      else
        Except.error "dangling bond marker at end of input"
    else
      Except.error "unclosed ring digit"
  else
    Except.error "unclosed branch"

/-- Token-level syntax state, separate from graph materialization. Branch stack entries record
how many atoms had been seen on opening, so a branch must contain a real atom before closing. -/
structure OpenSMILESSyntaxState where
  currentPresent : Bool := false
  pendingBond : Bool := false
  atomsSeen : ℕ := 0
  branchStarts : List ℕ := []
  deriving DecidableEq, Repr

/-- The innermost branch still requires its first atom. Ring digits and nested branches cannot
stand in for that atom; an initial bond or dot is allowed only when followed by an atom. -/
def OpenSMILESSyntaxState.branchNeedsAtom (state : OpenSMILESSyntaxState) : Bool :=
  state.branchStarts.head? == some state.atomsSeen

/-- Validate structural token placement without interpreting brackets as punctuation. This admits
legacy empty input, branch-dot chains and ring closures across dots, while rejecting discarded bond
markers, empty branches and empty disconnected components. It deliberately adds no atom syntax. -/
def openSMILESSyntaxValidFuel : ℕ → List Char → OpenSMILESSyntaxState → Bool
  | 0, _, _ => false
  | _ + 1, [], state =>
      state.branchStarts.isEmpty && !state.pendingBond &&
        (state.currentPresent || state.atomsSeen == 0)
  | fuel + 1, '.' :: rest, state =>
      state.currentPresent && !state.pendingBond &&
        openSMILESSyntaxValidFuel fuel rest { state with currentPresent := false }
  | fuel + 1, '(' :: rest, state =>
      state.currentPresent && !state.pendingBond && !state.branchNeedsAtom &&
        openSMILESSyntaxValidFuel fuel rest
          { state with branchStarts := state.atomsSeen :: state.branchStarts }
  | fuel + 1, ')' :: rest, state =>
      match state.branchStarts with
      | [] => false
      | openedAt :: remaining =>
          state.currentPresent && !state.pendingBond && decide (openedAt < state.atomsSeen) &&
            openSMILESSyntaxValidFuel fuel rest
              { state with currentPresent := true, branchStarts := remaining }
  | fuel + 1, chars, state =>
      match parseAtomToken? chars with
      | some (_, rest) =>
          openSMILESSyntaxValidFuel fuel rest
            { state with
              currentPresent := true
              pendingBond := false
              atomsSeen := state.atomsSeen + 1 }
      | none =>
          match chars with
          | [] => false
          | c :: rest =>
              match parseBondToken? c with
              | some _ =>
                  state.currentPresent && !state.pendingBond &&
                    openSMILESSyntaxValidFuel fuel rest { state with pendingBond := true }
              | none =>
                  match parseRingToken? chars with
                  | some (_, rest) =>
                      state.currentPresent && !state.branchNeedsAtom &&
                        openSMILESSyntaxValidFuel fuel rest { state with pendingBond := false }
                  | none => false

def openSMILESSyntaxValid (input : String) : Bool :=
  openSMILESSyntaxValidFuel (input.toList.length + 1) input.toList {}

/-- Parse an OpenSMILES-style string into a raw molecule. Syntax admission prevents token
materialization from silently discarding malformed branches or bond markers. The final check binds
source introduction history to the exact returned graph and written-neighbor rows. -/
def parseOpenSMILES (input : String) : Except ParserError RawMolecule :=
  if openSMILESSyntaxValid input then
    match parseChars input.toList {} with
    | .error error => .error error
    | .ok state =>
        match finalizeParseState state with
        | .error error => .error error
        | .ok molecule =>
            if molecule.parserIntroductionValid? then .ok molecule
            else .error "inconsistent parser introduction metadata"
  else .error "malformed OpenSMILES branch, component, or bond token placement"

/-- Reusable bridge from independent grammar, materialization and provenance facts to the public
parser result. Family proofs can use this without unfolding the admission implementation. -/
theorem parseOpenSMILES_eq_ok_of (input : String) (state : ParseState) (molecule : RawMolecule)
    (syntaxValid : openSMILESSyntaxValid input = true)
    (parsed : parseChars input.toList {} = .ok state)
    (finalized : finalizeParseState state = .ok molecule)
    (introductionValid : molecule.parserIntroductionValid? = true) :
    parseOpenSMILES input = .ok molecule := by
  simp [parseOpenSMILES, syntaxValid, parsed, finalized, introductionValid]

/-- Successful public parsing has a total, internally consistent introduction table. This is a
property of the actual checked entry point, not an assumption about arbitrary raw records. -/
theorem parseOpenSMILES_introduction_valid (input : String) (molecule : RawMolecule)
    (observed : parseOpenSMILES input = .ok molecule) :
    molecule.introductionPredecessors.length = molecule.atomCount ∧
      molecule.introductionPredecessorsValid? = true := by
  unfold parseOpenSMILES at observed
  split at observed
  · cases parsed : parseChars input.toList {} with
    | error error => simp [parsed] at observed
    | ok state =>
        simp only [parsed] at observed
        cases finalized : finalizeParseState state with
        | error error => simp [finalized] at observed
        | ok result =>
            simp only [finalized] at observed
            split at observed
            · rename_i valid
              cases observed
              simpa [RawMolecule.parserIntroductionValid?, Bool.and_eq_true] using valid
            · contradiction
  · contradiction

/-! ### Aromaticity, resonance, stereobonds, and tautomers -/

/-- Aromaticity model with executable checks. -/
structure AromaticityModel where
  atomCanBeAromatic : AtomSpec → Bool
  piContribution : AtomSpec → ℕ
  huckelOK : ℕ → Bool

/-- OpenSMILES-style aromaticity model: aromatic atoms must be eligible, and cycle electron counts
must satisfy a `4n+2` check. -/
def openSMILESAromaticityModel : AromaticityModel where
  atomCanBeAromatic := fun atom => !atom.aromatic || atom.element.aromaticEligible
  piContribution := AtomSpec.piElectronContribution
  huckelOK := fun electrons => electrons % 4 = 2

/-- A candidate aromatic cycle supplied by a parser or ring finder. -/
structure AromaticCycle where
  atoms : List ℕ
  deriving DecidableEq, Repr

namespace AromaticCycle

/-- π-electron count for a candidate cycle. -/
def piElectrons (cycle : AromaticCycle) (mol : RawMolecule)
    (model : AromaticityModel := openSMILESAromaticityModel) : ℕ :=
  cycle.atoms.foldl
    (fun total idx =>
      match mol.atomAt? idx with
      | none => total
      | some atom => total + model.piContribution atom)
    0

/-- Executable aromaticity validation for a supplied candidate cycle. -/
def valid (cycle : AromaticCycle) (mol : RawMolecule)
    (model : AromaticityModel := openSMILESAromaticityModel) : Bool :=
  cycle.atoms.length >= 3 &&
    cycle.atoms.all (fun idx =>
      match mol.atomAt? idx with
      | none => false
      | some atom => model.atomCanBeAromatic atom) &&
    model.huckelOK (cycle.piElectrons mol model)

end AromaticCycle

/-- Resonance move categories tracked by the normalizer. -/
inductive ResonanceMoveKind where
  | piBondShift
  | lonePairDonation
  | chargeSeparation
  | aromaticKekuleCollapse
  deriving DecidableEq, Repr

/-- A resonance move over a local atom set. -/
structure ResonanceMove where
  kind : ResonanceMoveKind
  atoms : List ℕ
  deriving DecidableEq, Repr

/-- Bond semantics after resonance normalization. -/
inductive NormalizedBondSemantics where
  | localized (order : BondOrder)
  | aromaticDelocalized
  | tautomeric
  deriving DecidableEq, Repr

/-- Resonance-normalized molecule plus a bond-semantics accessor. -/
structure ResonanceNormalization where
  source : RawMolecule
  normalized : RawMolecule
  moves : List ResonanceMove
  bondSemantics : ℕ → ℕ → Option NormalizedBondSemantics

/-- Normalize resonance-delocalized aromatic bonds without losing the fixed localized input. -/
def resonanceNormalize (mol : RawMolecule) : ResonanceNormalization :=
  let normalized := mol.normalizeUnspecifiedBonds
  { source := mol
    normalized := normalized
    moves :=
      normalized.bonds.filterMap fun bond =>
        if bond.kind = ParsedBondKind.aromatic then
          some { kind := ResonanceMoveKind.aromaticKekuleCollapse, atoms := [bond.source, bond.target] }
        else
          none
    bondSemantics := fun u v =>
      match normalized.bonds.find? fun bond => bond.connects u v with
      | none => none
      | some bond =>
          if bond.kind = ParsedBondKind.aromatic then
            some NormalizedBondSemantics.aromaticDelocalized
          else
            some (NormalizedBondSemantics.localized bond.kind.order) }

/-- Directional single-bond marker used to infer alkene/cumulene stereochemistry. -/
inductive DirectionalBondMarker where
  | up
  | down
  deriving DecidableEq, Repr

namespace DirectionalBondMarker

/-- The opposite side marker.

A directional bond records where its `target` sits relative to its `source`, so the same bond read
from its other endpoint describes the opposite side. -/
def flip : DirectionalBondMarker → DirectionalBondMarker
  | up => down
  | down => up

@[simp] theorem flip_up : flip up = down := rfl

@[simp] theorem flip_down : flip down = up := rfl

@[simp] theorem flip_flip (marker : DirectionalBondMarker) : marker.flip.flip = marker := by
  cases marker <;> rfl

end DirectionalBondMarker

/-- Double-bond stereochemical relation. -/
inductive DoubleBondStereo where
  | E
  | Z
  | unspecified
  deriving DecidableEq, Repr

/-- Parsed stereobond annotation. -/
structure StereobondAnnotation where
  source : ℕ
  target : ℕ
  marker : DirectionalBondMarker
  deriving DecidableEq, Repr

/-- Stereobond semantics extracted from directional parsed bonds. -/
structure StereobondSemantics where
  directionalBonds : List StereobondAnnotation
  tetrahedralAtoms : List (ℕ × TetrahedralInputParity)
  doubleBondAssignments : List (ℕ × ℕ × DoubleBondStereo)
  deriving DecidableEq, Repr

/-- Extract stereochemical input annotations from a raw molecule. -/
def stereobondSemantics (mol : RawMolecule) : StereobondSemantics where
  directionalBonds :=
    mol.bonds.filterMap fun bond =>
      match bond.kind.directional? with
      | some true => some { source := bond.source, target := bond.target, marker := DirectionalBondMarker.up }
      | some false => some { source := bond.source, target := bond.target, marker := DirectionalBondMarker.down }
      | none => none
  tetrahedralAtoms :=
    enumerate mol.atoms |>.filterMap fun indexed =>
      match indexed.2.tetrahedral? with
      | none => none
      | some parity => some (indexed.1, parity)
  doubleBondAssignments :=
    mol.bonds.filterMap fun bond =>
      if bond.kind = ParsedBondKind.double then
        some (bond.source, bond.target, DoubleBondStereo.unspecified)
      else
        none

/-- Lightweight tautomer move categories. -/
inductive TautomerMoveKind where
  | mobileHydrogenTransfer
  | ketoEnol
  | imineEnamine
  | aromaticTautomer
  deriving DecidableEq, Repr

/-- Tautomer move over donor/acceptor sites. -/
structure TautomerMove where
  kind : TautomerMoveKind
  donor : ℕ
  acceptor : ℕ
  deriving DecidableEq, Repr

/-- Fixed-H-aware tautomer normalization object. -/
structure TautomerNormalization where
  fixedMolecule : RawMolecule
  mobileHydrogenDonors : List ℕ
  mobileHydrogenAcceptors : List ℕ
  moves : List TautomerMove
  deriving DecidableEq, Repr

/-- Build all donor/acceptor transfer moves for lightweight tautomer handling. -/
def tautomerMoves (donors acceptors : List ℕ) : List TautomerMove :=
  listBind donors fun donor =>
    acceptors.filterMap fun acceptor =>
      if donor = acceptor then
        none
      else
        some { kind := TautomerMoveKind.mobileHydrogenTransfer, donor := donor, acceptor := acceptor }

/-- Normalize tautomer information by separating fixed-H structure from mobile-H donor/acceptor
metadata. -/
def tautomerNormalize (mol : RawMolecule) : TautomerNormalization :=
  let donors :=
    enumerate mol.atoms |>.filterMap fun indexed =>
      if indexed.2.mobileHydrogenDonor then some indexed.1 else none
  let acceptors :=
    enumerate mol.atoms |>.filterMap fun indexed =>
      if indexed.2.mobileHydrogenAcceptor then some indexed.1 else none
  { fixedMolecule := mol
    mobileHydrogenDonors := donors
    mobileHydrogenAcceptors := acceptors
    moves := tautomerMoves donors acceptors }

/-! ### End-to-end chemistry intake pipeline -/

/-- Output of the production-facing chemistry intake/normalization pipeline. -/
structure ChemistryNormalizationResult where
  parsed : RawMolecule
  graph : MoleculeGraph (Fin parsed.atomCount)
  valenceOK : Prop
  aromaticCycles : List AromaticCycle
  resonance : ResonanceNormalization
  stereobonds : StereobondSemantics
  tautomer : TautomerNormalization

/-- Normalization result admitted to chemistry-authority claims.  Unlike the legacy convenience
record, this wrapper carries kernel proofs of graph admission, the encoded valence-table contract,
and source-backed Rule-2 data for every atom. -/
structure CertifiedChemistryNormalizationResult where
  result : ChemistryNormalizationResult
  admissible : result.parsed.Admissible
  writtenNeighborExact : result.parsed.WrittenNeighborExact
  valenceOK : result.parsed.ValenceOK
  rule2MassesKnown : result.parsed.Rule2MassesKnown

/-- A certified chemistry-normalization result satisfies the complete structural admission
contract consumed by stereochemical perception. -/
theorem CertifiedChemistryNormalizationResult.stereochemicalAdmissible
    (certified : CertifiedChemistryNormalizationResult) :
    certified.result.parsed.StereochemicalAdmissible :=
  ⟨certified.admissible, certified.writtenNeighborExact⟩

/-- Check and package structural, valence, and Rule-2-source obligations of an existing
normalization result. -/
def ChemistryNormalizationResult.certify? (result : ChemistryNormalizationResult) :
    Option CertifiedChemistryNormalizationResult :=
  if result.parsed.introductionPredecessorsValid? then
    if hadmissible : result.parsed.admissible? = true then
      if hneighbors : result.parsed.writtenNeighborExact? = true then
        if hvalence : result.parsed.valenceOK? = true then
          if hmasses : result.parsed.rule2MassesKnown? = true then
            some { result := result
                   admissible := (result.parsed.admissible?_eq_true_iff).mp hadmissible
                   writtenNeighborExact :=
                     (result.parsed.writtenNeighborExact?_eq_true_iff).mp hneighbors
                   valenceOK := (result.parsed.valenceOK?_eq_true_iff).mp hvalence
                   rule2MassesKnown := (result.parsed.rule2MassesKnown?_eq_true_iff).mp hmasses }
          else none
        else none
      else none
    else none
  else none

/-- The executable certified-intake constructor rejects structurally inconsistent introduction
metadata. Manually constructed `CertifiedChemistryNormalizationResult` values do not acquire this
extra guarantee merely from their type; the hypothesis binds this lemma to the checked API. -/
theorem ChemistryNormalizationResult.certify?_introduction_valid
    (result : ChemistryNormalizationResult) (certified : CertifiedChemistryNormalizationResult)
    (observed : result.certify? = some certified) :
    result.parsed.introductionPredecessorsValid? = true := by
  by_cases valid : result.parsed.introductionPredecessorsValid? = true
  · exact valid
  · simp [ChemistryNormalizationResult.certify?, valid] at observed

/-- Build the full semantic bundle from a raw molecule and optional candidate aromatic cycles. -/
def normalizeRawMolecule (mol : RawMolecule) (cycles : List AromaticCycle := []) :
    ChemistryNormalizationResult :=
  let aromatic := mol.normalizeUnspecifiedBonds
  { parsed := aromatic
    graph := aromatic.toMoleculeGraph
    valenceOK := aromatic.ValenceOK
    aromaticCycles := cycles
    resonance := resonanceNormalize aromatic
    stereobonds := stereobondSemantics aromatic
    tautomer := tautomerNormalize aromatic }

/-- Normalize a raw molecule and admit it only when both executable chemistry checks reflect to
kernel propositions. -/
def normalizeRawMoleculeCertified? (mol : RawMolecule) (cycles : List AromaticCycle := []) :
    Option CertifiedChemistryNormalizationResult :=
  (normalizeRawMolecule mol cycles).certify?

/-- Parse and normalize an OpenSMILES-style molecule string. -/
def parseAndNormalizeOpenSMILES (input : String)
    (cycles : List AromaticCycle := []) : Except ParserError ChemistryNormalizationResult := do
  let mol ← parseOpenSMILES input
  Except.ok (normalizeRawMolecule mol cycles)

/-- Authority-facing OpenSMILES intake. Structurally malformed, valence-invalid, wildcard, and
unknown-nuclide inputs cannot reach the certified molecular graph. -/
def parseAndNormalizeOpenSMILESCertified (input : String)
    (cycles : List AromaticCycle := []) :
    Except ParserError CertifiedChemistryNormalizationResult := do
  let result ← parseAndNormalizeOpenSMILES input cycles
  match result.certify? with
  | some certified => Except.ok certified
  | none => Except.error "normalized molecule failed structural, valence, or Rule-2 mass admission"

/-- Benzene parsed from aromatic OpenSMILES validates as a six-π-electron aromatic candidate. -/
example :
    (parseAndNormalizeOpenSMILES "c1ccccc1"
      [{ atoms := [0, 1, 2, 3, 4, 5] }]).isOk = true := by
  decide

/-- The aromaticity model recognizes the supplied benzene cycle as valid. -/
example :
    (match parseAndNormalizeOpenSMILES "c1ccccc1" with
      | Except.ok result => ({ atoms := [0, 1, 2, 3, 4, 5] } : AromaticCycle).valid result.parsed
      | Except.error _ => false) = true := by
  decide

/-- The valence layer infers four hydrogens for methane's bare carbon. -/
example :
    (match parseAndNormalizeOpenSMILES "C" with
      | Except.ok result => result.parsed.implicitHydrogensAt? 0 = some 4
      | Except.error _ => false) = true := by
  decide

/-- The parser preserves tetrahedral input annotations in bracket atoms. -/
example :
    (parseAndNormalizeOpenSMILES "C[C@H](O)c1ccccc1").isOk = true := by
  decide

/-- Bracket `@` input becomes one tetrahedral atom annotation. -/
example :
    (match parseAndNormalizeOpenSMILES "C[C@H](O)c1ccccc1" with
      | Except.ok result => result.stereobonds.tetrahedralAtoms.length = 1
      | Except.error _ => false) = true := by
  decide

/-- Directional alkene stereobond markers are accepted by the parser. -/
example :
    (parseAndNormalizeOpenSMILES "C/C=C\\C").isOk = true := by
  decide

/-- Directional alkene input records two directional stereobond markers. -/
example :
    (match parseAndNormalizeOpenSMILES "C/C=C\\C" with
      | Except.ok result => result.stereobonds.directionalBonds.length = 2
      | Except.error _ => false) = true := by
  decide

/-- A simple amide-like input exposes one mobile-H tautomer transfer move. -/
example :
    (match parseAndNormalizeOpenSMILES "[NH]C=O" with
      | Except.ok result => result.tautomer.moves.length = 1
      | Except.error _ => false) = true := by
  decide

/-! #### Bracket grammar and raw-admission regressions -/

/-- Signed decimal charge magnitudes are preserved exactly. -/
example :
    (match parseOpenSMILES "[13NH2-2]" with
      | Except.ok mol => (mol.atomAt? 0).map AtomSpec.charge = some (-2)
      | Except.error _ => false) = true := by
  decide

/-- Positive decimal charge magnitudes are preserved exactly. -/
example :
    (match parseOpenSMILES "[N+2]" with
      | Except.ok mol => (mol.atomAt? 0).map AtomSpec.charge = some 2
      | Except.error _ => false) = true := by
  decide

/-- Repeated positive signs carry their exact magnitude. -/
example :
    (match parseOpenSMILES "[N++]" with
      | Except.ok mol => (mol.atomAt? 0).map AtomSpec.charge = some 2
      | Except.error _ => false) = true := by
  decide

/-- Repeated negative signs carry their exact magnitude. -/
example :
    (match parseOpenSMILES "[N--]" with
      | Except.ok mol => (mol.atomAt? 0).map AtomSpec.charge = some (-2)
      | Except.error _ => false) = true := by
  decide

/-- Unit signs retain their ordinary unit magnitudes. -/
example :
    (match parseOpenSMILES "[N+]", parseOpenSMILES "[N-]" with
      | Except.ok positive, Except.ok negative =>
          (positive.atomAt? 0).map AtomSpec.charge = some 1 ∧
            (negative.atomAt? 0).map AtomSpec.charge = some (-1)
      | _, _ => false) = true := by
  decide

/-- The standard isotope/chirality/hydrogen/charge order is consumed without losing fields. -/
example :
    (match parseOpenSMILES "[13C@@H2+2]" with
      | Except.ok mol =>
          (mol.atomAt? 0).map
              (fun atom =>
                (atom.isotope?, atom.explicitHydrogens?, atom.charge, atom.tetrahedral?)) =
            some (some 13, some 2, 2, some TetrahedralInputParity.clockwise)
      | Except.error _ => false) = true := by
  decide

/-- The documented terminal charge-before-chirality compatibility form remains supported. -/
example :
    (match parseOpenSMILES "[S+@@]" with
      | Except.ok mol =>
          (mol.atomAt? 0).map (fun atom => (atom.charge, atom.tetrahedral?)) =
            some (1, some TetrahedralInputParity.clockwise)
      | Except.error _ => false) = true := by
  decide

/-- Zero charge magnitudes are rejected rather than reinterpreted as unit charge. -/
example : (parseOpenSMILES "[N-0]").isOk = false := by decide

example : (parseOpenSMILES "[N+0]").isOk = false := by decide

/-- Mixed sign runs are neither truncated nor silently reinterpreted. -/
example : (parseOpenSMILES "[N+-]").isOk = false := by decide

example : (parseOpenSMILES "[N-+]").isOk = false := by decide

/-- The repeated-sign production is exactly doubled; longer runs are invalid residue. -/
example : (parseOpenSMILES "[N+++]").isOk = false := by decide

example : (parseOpenSMILES "[N--2]").isOk = false := by decide

/-- Suffix order is consumed: charge cannot be followed by chirality and hydrogen. -/
example : (parseOpenSMILES "[N+@H]").isOk = false := by decide

example : (parseOpenSMILES "[13N-2H2]").isOk = false := by decide

/-- A hydrogen/isotope-like digit may not appear as an unrecognized suffix before charge. -/
example : (parseOpenSMILES "[N2+]").isOk = false := by decide

/-- Unsupported bracket residue is never silently erased. -/
example : (parseOpenSMILES "[N?]").isOk = false := by decide

/-- Unsupported atom-class syntax is rejected rather than silently erased. -/
example : (parseOpenSMILES "[N:12]").isOk = false := by decide

/-- Unsupported extended chirality classes are rejected as unconsumed residue. -/
example : (parseOpenSMILES "[N@TH1]").isOk = false := by decide

/-- A second hydrogen-count digit remains invalid residue. -/
example : (parseOpenSMILES "[NH22+]").isOk = false := by decide

/-- The parser itself rejects a duplicate ring closure on an already connected tetrahedral
center, before the molecule can reach proof-facing hierarchy construction. -/
example : (parseOpenSMILES "C1(C)(C)(C)C1").isOk = false := by decide

/-- Reusing a ring label across an already written bond cannot create a second record for the same
unordered edge, whether the records have equal or conflicting bond kinds. -/
example : (parseOpenSMILES "C1C1").isOk = false := by decide

example : (parseOpenSMILES "C1=C1").isOk = false := by decide

/-- Multiple ring labels cannot inflate one constitutional edge by repeated occurrences. -/
example : (parseOpenSMILES "C12C12").isOk = false := by decide

/-- An ordinary single-bond ring remains admissible after parser normalization. -/
example :
    (match parseOpenSMILES "C1CCCCC1" with
      | Except.ok mol => mol.admissible?
      | Except.error _ => false) = true := by
  decide

/-- Closing a ring at its opening atom is rejected by the same structural admission boundary. -/
example : (parseOpenSMILES "C11").isOk = false := by decide

/-- Contradictory bond kinds on the two ring markers are rejected during ring resolution. -/
example : (parseOpenSMILES "C=1CCCCC-1").isOk = false := by decide

end
end OneCenter
end TetraStereo
