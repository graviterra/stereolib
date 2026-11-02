import TetraStereo.OneCenter.ChemistrySemantics

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Representation-complete finite chemical input

`RawMolecule` is intentionally parser-shaped and supports only a small element vocabulary.  The
universal authority theorem cannot quantify over that type.  This module provides the independent,
format-neutral semantic input over all 118 currently named elements, arbitrary finite atom and
interaction lists, isotopic labels, charge/radical state, exact rational 3D coordinates, and
configuration-bearing drawing primitives.

This is a representation layer, not yet a chemical-admissibility oracle.  Structural well-formedness
is executable and reflected into Lean; chemical admissibility and IUPAC applicability are separate
future predicates over the structurally admitted object.
-/

/-- A currently named periodic-table element, represented without a 118-constructor maintenance
burden. -/
structure PeriodicElement where
  atomicNumber : ℕ
  positive : 0 < atomicNumber
  atMost118 : atomicNumber ≤ 118
  deriving DecidableEq, Repr

namespace PeriodicElement

/-- Checked constructor for atomic numbers 1 through 118. -/
def ofAtomicNumber? (atomicNumber : ℕ) : Option PeriodicElement :=
  if positive : 0 < atomicNumber then
    if bounded : atomicNumber ≤ 118 then
      some { atomicNumber := atomicNumber, positive := positive, atMost118 := bounded }
    else none
  else none

@[simp] theorem ofAtomicNumber?_isSome (atomicNumber : ℕ) :
    (ofAtomicNumber? atomicNumber).isSome = true ↔
      0 < atomicNumber ∧ atomicNumber ≤ 118 := by
  unfold ofAtomicNumber?
  split
  · split <;> simp_all
  · simp_all

theorem ext {left right : PeriodicElement}
    (atomicNumber : left.atomicNumber = right.atomicNumber) : left = right := by
  cases left
  cases right
  simp_all

end PeriodicElement

namespace Element

/-- Exact embedding of the parser's real elements into the complete periodic-table type.  A
wildcard is unknown chemical identity and therefore cannot cross this authority boundary. -/
def toPeriodic? (element : Element) : Option PeriodicElement :=
  match element with
  | .wildcard => none
  | _ => PeriodicElement.ofAtomicNumber? element.atomicNumber

@[simp] theorem toPeriodic?_isSome (element : Element) :
    element.toPeriodic?.isSome = true ↔ element ≠ .wildcard := by
  cases element <;> decide

end Element

/-- One atom in the format-neutral semantic molecule. `isotopeMassNumber? = none` denotes ordinary
unlabelled isotopic composition under the applicable IUPAC Rule-2 convention. Most elements require
the frozen standard-atomic-weight data when compared with a labelled isotope; P-92.3 explicitly
identifies ordinary `H` with `¹H`. -/
structure SemanticAtom where
  element : PeriodicElement
  isotopeMassNumber? : Option ℕ := none
  formalCharge : Int := 0
  unpairedElectrons : ℕ := 0
  aromaticInput : Bool := false
  deriving DecidableEq, Repr

namespace AtomSpec

/-- Successful parser-element conversion preserves atomic number.  Kept private here so the
parser refinement proof does not depend on a downstream applicability module. -/
private theorem elementToPeriodic?_atomicNumber
    (source : Element) (periodic : PeriodicElement)
    (converted : source.toPeriodic? = some periodic) :
    periodic.atomicNumber = source.atomicNumber := by
  cases source <;>
    simp [Element.toPeriodic?, PeriodicElement.ofAtomicNumber?, Element.atomicNumber] at converted
  all_goals
    subst periodic
    rfl

/-- Parser atom to complete semantic atom. -/
def toSemanticAtom? (atom : AtomSpec) : Option SemanticAtom := do
  let element ← atom.element.toPeriodic?
  some
    { element := element
      isotopeMassNumber? := atom.isotope?
      formalCharge := atom.charge
      aromaticInput := atom.aromatic }

@[simp] theorem toSemanticAtom?_isSome (atom : AtomSpec) :
    atom.toSemanticAtom?.isSome = true ↔ atom.element ≠ .wildcard := by
  cases observed : atom.element.toPeriodic? with
  | none =>
      have unknown : ¬ atom.element ≠ .wildcard := by
        intro known
        have present := (Element.toPeriodic?_isSome atom.element).mpr known
        simp [observed] at present
      simp [AtomSpec.toSemanticAtom?, observed, unknown]
  | some element =>
      have known : atom.element ≠ .wildcard := by
        apply (Element.toPeriodic?_isSome atom.element).mp
        simp [observed]
      simp [AtomSpec.toSemanticAtom?, observed, known]

/-- Successful single-atom conversion preserves exactly the atom data shared with the
constitutional production graph. -/
theorem toSemanticAtom?_exact
    (atom : AtomSpec) (semantic : SemanticAtom)
    (converted : atom.toSemanticAtom? = some semantic) :
    semantic.element.atomicNumber = atom.element.atomicNumber ∧
      semantic.isotopeMassNumber? = atom.isotope? ∧
      semantic.formalCharge = atom.charge ∧
      semantic.unpairedElectrons = 0 ∧
      semantic.aromaticInput = atom.aromatic := by
  cases elementObserved : atom.element.toPeriodic? with
  | none => simp [AtomSpec.toSemanticAtom?, elementObserved] at converted
  | some element =>
      simp [AtomSpec.toSemanticAtom?, elementObserved] at converted
      subst semantic
      have atomicNumberExact : element.atomicNumber = atom.element.atomicNumber :=
        elementToPeriodic?_atomicNumber atom.element element elementObserved
      exact ⟨atomicNumberExact, rfl, rfl, rfl, rfl⟩

end AtomSpec

/-- Bonding/interaction vocabulary broad enough to retain chemistry that must be normalized before
CIP digraph construction.  Pairwise bond order is not imposed on multicenter, delocalized, ionic,
or metallic interactions. -/
inductive SemanticInteractionKind where
  | unspecifiedCovalent
  | covalent (bondOrder : ℕ)
  | aromatic
  | delocalized (electronCount : ℕ)
  | coordinate
  | multicenter (electronCount : ℕ)
  | ionic
  | metallic
  | hydrogenBond
  | other (authorityCode : String)
  deriving DecidableEq, Repr

/-- An arbitrary finite interaction.  Pair bonds have two participants; multicenter and
coordination representations may have more. -/
structure SemanticInteraction where
  participants : List ℕ
  kind : SemanticInteractionKind
  deriving DecidableEq, Repr

namespace SemanticInteraction

def WellFormed (interaction : SemanticInteraction) (atomCount : ℕ) : Prop :=
  2 ≤ interaction.participants.length ∧
    interaction.participants.Nodup ∧
    interaction.participants.all (fun atom => decide (atom < atomCount)) = true

def wellFormed? (interaction : SemanticInteraction) (atomCount : ℕ) : Bool :=
  decide (2 ≤ interaction.participants.length) &&
    decide interaction.participants.Nodup &&
    interaction.participants.all fun atom => decide (atom < atomCount)

@[simp] theorem wellFormed?_eq_true_iff (interaction : SemanticInteraction) (atomCount : ℕ) :
    interaction.wellFormed? atomCount = true ↔ interaction.WellFormed atomCount := by
  simp [wellFormed?, WellFormed, and_assoc]

end SemanticInteraction

/-- A finite molecular entity independent of any serialization format. -/
structure SemanticMolecule where
  atoms : List SemanticAtom
  interactions : List SemanticInteraction
  deriving DecidableEq, Repr

namespace SemanticMolecule

def atomCount (molecule : SemanticMolecule) : ℕ := molecule.atoms.length

def StructurallyWellFormed (molecule : SemanticMolecule) : Prop :=
  molecule.interactions.all
    (fun interaction => interaction.wellFormed? molecule.atomCount) = true

def structurallyWellFormed? (molecule : SemanticMolecule) : Bool :=
  molecule.interactions.all fun interaction => interaction.wellFormed? molecule.atomCount

@[simp] theorem structurallyWellFormed?_eq_true_iff (molecule : SemanticMolecule) :
    molecule.structurallyWellFormed? = true ↔ molecule.StructurallyWellFormed := by
  rfl

end SemanticMolecule

/-- Exact rational coordinate.  Decimal and binary floating-point importers can translate their
stored values without introducing a second rounding inside the proof model. -/
structure CartesianPoint3 where
  x : ℚ
  y : ℚ
  z : ℚ
  deriving DecidableEq, Repr

/-- Exact two-dimensional drawing coordinate. -/
structure CartesianPoint2 where
  x : ℚ
  y : ℚ
  deriving DecidableEq, Repr

/-- Complete coordinates for one conformation. -/
structure SpatialConfiguration where
  positions : List CartesianPoint3
  deriving DecidableEq, Repr

/-- Directional and perspective bond styles from the IUPAC graphical-representation boundary. -/
inductive DiagramBondStyle where
  | plain
  | solidWedge
  | hashedWedge
  | wavy
  | bold
  | directionalUp
  | directionalDown
  deriving DecidableEq, Repr

/-- Scope of a graphical configuration statement. -/
inductive DiagramConfigurationScope where
  | absolute
  | relative (group : ℕ)
  | racemic (group : ℕ)
  | unknown
  deriving DecidableEq, Repr

structure DiagramBond where
  source : ℕ
  target : ℕ
  style : DiagramBondStyle
  scope : DiagramConfigurationScope := .absolute
  deriving DecidableEq, Repr

structure DiagramAtomConfiguration where
  atom : ℕ
  parity : TetrahedralInputParity
  scope : DiagramConfigurationScope := .absolute
  deriving DecidableEq, Repr

structure DiagramConfiguration where
  atomPositions? : Option (List CartesianPoint2) := none
  bonds : List DiagramBond := []
  atomConfigurations : List DiagramAtomConfiguration := []
  deriving DecidableEq, Repr

/-- Full configuration-bearing input.  Either evidence channel may be absent; completeness for a
particular stereogenic unit is stated later as a unit-relative predicate. -/
structure AuthoritativeChemicalInput where
  molecule : SemanticMolecule
  spatial? : Option SpatialConfiguration := none
  diagram? : Option DiagramConfiguration := none
  deriving DecidableEq, Repr

namespace AuthoritativeChemicalInput

def SpatialIndicesWellFormed (input : AuthoritativeChemicalInput) : Prop :=
  match input.spatial? with
  | none => True
  | some spatial => spatial.positions.length = input.molecule.atomCount

def DiagramIndicesWellFormed (input : AuthoritativeChemicalInput) : Prop :=
  match input.diagram? with
  | none => True
  | some diagram =>
      (match diagram.atomPositions? with
       | none => True
       | some positions => positions.length = input.molecule.atomCount) ∧
      diagram.bonds.all (fun bond =>
          decide (bond.source < input.molecule.atomCount) &&
            decide (bond.target < input.molecule.atomCount) &&
              decide (bond.source ≠ bond.target)) = true ∧
      diagram.atomConfigurations.all (fun atomConfiguration =>
        decide (atomConfiguration.atom < input.molecule.atomCount)) = true

def spatialIndicesWellFormed? (input : AuthoritativeChemicalInput) : Bool :=
  match input.spatial? with
  | none => true
  | some spatial => decide (spatial.positions.length = input.molecule.atomCount)

@[simp] theorem spatialIndicesWellFormed?_eq_true_iff (input : AuthoritativeChemicalInput) :
    input.spatialIndicesWellFormed? = true ↔ input.SpatialIndicesWellFormed := by
  cases observed : input.spatial? <;>
    simp [spatialIndicesWellFormed?, SpatialIndicesWellFormed, observed]

def diagramIndicesWellFormed? (input : AuthoritativeChemicalInput) : Bool :=
  match input.diagram? with
  | none => true
  | some diagram =>
      (match diagram.atomPositions? with
       | none => true
       | some positions => decide (positions.length = input.molecule.atomCount)) &&
      diagram.bonds.all (fun bond =>
          decide (bond.source < input.molecule.atomCount) &&
            decide (bond.target < input.molecule.atomCount) &&
              decide (bond.source ≠ bond.target)) &&
      diagram.atomConfigurations.all (fun atomConfiguration =>
        decide (atomConfiguration.atom < input.molecule.atomCount))

@[simp] theorem diagramIndicesWellFormed?_eq_true_iff (input : AuthoritativeChemicalInput) :
    input.diagramIndicesWellFormed? = true ↔ input.DiagramIndicesWellFormed := by
  cases observed : input.diagram? with
  | none => simp [diagramIndicesWellFormed?, DiagramIndicesWellFormed, observed]
  | some diagram =>
      cases positionsObserved : diagram.atomPositions? <;>
        simp [diagramIndicesWellFormed?, DiagramIndicesWellFormed, observed,
          positionsObserved, and_assoc]

def StructurallyWellFormed (input : AuthoritativeChemicalInput) : Prop :=
  input.molecule.StructurallyWellFormed ∧
    input.SpatialIndicesWellFormed ∧ input.DiagramIndicesWellFormed

def structurallyWellFormed? (input : AuthoritativeChemicalInput) : Bool :=
  input.molecule.structurallyWellFormed? &&
    input.spatialIndicesWellFormed? && input.diagramIndicesWellFormed?

@[simp] theorem structurallyWellFormed?_eq_true_iff (input : AuthoritativeChemicalInput) :
    input.structurallyWellFormed? = true ↔ input.StructurallyWellFormed := by
  simp [structurallyWellFormed?, StructurallyWellFormed, and_assoc]

end AuthoritativeChemicalInput

/-- Kernel-admitted format-neutral input.  Chemical admissibility is deliberately not conflated
with this structural certificate. -/
structure CertifiedAuthoritativeChemicalInput where
  input : AuthoritativeChemicalInput
  structurallyWellFormed : input.StructurallyWellFormed

def AuthoritativeChemicalInput.certify?
    (input : AuthoritativeChemicalInput) : Option CertifiedAuthoritativeChemicalInput :=
  if checked : input.structurallyWellFormed? = true then
    some { input := input
           structurallyWellFormed := input.structurallyWellFormed?_eq_true_iff.mp checked }
  else none

/-! ## Exact bridge from the current parser model -/

def RawBond.toSemanticInteraction (bond : RawBond) : SemanticInteraction :=
  { participants := [bond.source, bond.target]
    kind :=
      match bond.kind with
      | .unspecified => .unspecifiedCovalent
      | .single | .up | .down => .covalent 1
      | .double => .covalent 2
      | .triple => .covalent 3
      | .aromatic => .aromatic }

@[simp] theorem RawBond.toSemanticInteraction_wellFormed_iff
    (bond : RawBond) (atomCount : ℕ) :
    (bond.toSemanticInteraction).WellFormed atomCount ↔
      bond.source < atomCount ∧ bond.target < atomCount ∧ bond.source ≠ bond.target := by
  simp [RawBond.toSemanticInteraction, SemanticInteraction.WellFormed]
  tauto

@[simp] theorem RawBond.toSemanticInteraction_wellFormed?_eq_true_iff
    (bond : RawBond) (atomCount : ℕ) :
    (bond.toSemanticInteraction).wellFormed? atomCount = true ↔
      bond.source < atomCount ∧ bond.target < atomCount ∧ bond.source ≠ bond.target := by
  rw [SemanticInteraction.wellFormed?_eq_true_iff,
    RawBond.toSemanticInteraction_wellFormed_iff]

private def semanticAtomList? : List AtomSpec → Option (List SemanticAtom)
  | [] => some []
  | atom :: atoms => do
      let converted ← atom.toSemanticAtom?
      let rest ← semanticAtomList? atoms
      some (converted :: rest)

private theorem semanticAtomList?_length {atoms : List AtomSpec} {semantic : List SemanticAtom}
    (converted : semanticAtomList? atoms = some semantic) :
    semantic.length = atoms.length := by
  induction atoms generalizing semantic with
  | nil =>
      simp [semanticAtomList?] at converted
      subst semantic
      rfl
  | cons atom atoms inductionHypothesis =>
      cases atomObserved : atom.toSemanticAtom? with
      | none => simp [semanticAtomList?, atomObserved] at converted
      | some convertedAtom =>
          cases restObserved : semanticAtomList? atoms with
          | none => simp [semanticAtomList?, atomObserved, restObserved] at converted
          | some convertedRest =>
              simp [semanticAtomList?, atomObserved, restObserved] at converted
              subst semantic
              simp [inductionHypothesis restObserved]

/-- Successful whole-list conversion preserves every list position and performs exactly the
single-atom checked conversion at that position. -/
private theorem semanticAtomList?_listGet?
    {atoms : List AtomSpec} {semantic : List SemanticAtom}
    (converted : semanticAtomList? atoms = some semantic) (index : ℕ) :
    listGet? semantic index = (listGet? atoms index).bind AtomSpec.toSemanticAtom? := by
  induction atoms generalizing semantic index with
  | nil =>
      simp [semanticAtomList?] at converted
      subst semantic
      simp [listGet?]
  | cons atom atoms inductionHypothesis =>
      cases atomObserved : atom.toSemanticAtom? with
      | none => simp [semanticAtomList?, atomObserved] at converted
      | some convertedAtom =>
          cases restObserved : semanticAtomList? atoms with
          | none => simp [semanticAtomList?, atomObserved, restObserved] at converted
          | some convertedRest =>
              simp [semanticAtomList?, atomObserved, restObserved] at converted
              subst semantic
              cases index with
              | zero => simp [listGet?, atomObserved]
              | succ index =>
                  simpa [listGet?] using inductionHypothesis restObserved index

def RawMolecule.semanticAtoms? (molecule : RawMolecule) : Option (List SemanticAtom) :=
  semanticAtomList? molecule.atoms

theorem semanticAtomList?_isSome_iff_no_wildcard : ∀ atoms : List AtomSpec,
    (semanticAtomList? atoms).isSome = true ↔
      ∀ atom, atom ∈ atoms → atom.element ≠ .wildcard
  | [] => by
      simp only [semanticAtomList?, Option.isSome_some]
      simp
  | atom :: atoms => by
      cases observed : atom.toSemanticAtom? with
      | none =>
          have wildcard : atom.element = .wildcard := by
            by_contra known
            have present := (AtomSpec.toSemanticAtom?_isSome atom).mpr known
            simp [observed] at present
          simp [semanticAtomList?, observed, wildcard]
      | some converted =>
          have known : atom.element ≠ .wildcard := by
            apply (AtomSpec.toSemanticAtom?_isSome atom).mp
            simp [observed]
          cases restObserved : semanticAtomList? atoms with
          | none =>
              have tailFails : ¬ ∀ rest, rest ∈ atoms → rest.element ≠ .wildcard := by
                intro tailKnown
                have present :=
                  (semanticAtomList?_isSome_iff_no_wildcard atoms).mpr tailKnown
                simp [restObserved] at present
              simp [semanticAtomList?, observed, restObserved, known, tailFails]
          | some rest =>
              have tailKnown : ∀ item, item ∈ atoms → item.element ≠ .wildcard := by
                apply (semanticAtomList?_isSome_iff_no_wildcard atoms).mp
                simp [restObserved]
              constructor
              · intro _ item membership
                rcases List.mem_cons.mp membership with equality | tailMembership
                · simpa [equality] using known
                · exact tailKnown item tailMembership
              · intro _
                simp [semanticAtomList?, observed, restObserved]

/-- Lossless structural embedding of the current parser object, except that unknown wildcard atom
identity is correctly rejected.  Directional bond evidence is copied separately below. -/
def RawMolecule.toSemanticMolecule? (molecule : RawMolecule) : Option SemanticMolecule := do
  let atoms ← molecule.semanticAtoms?
  some { atoms := atoms, interactions := molecule.bonds.map RawBond.toSemanticInteraction }

/-- Successful parser conversion preserves the finite atom-index type exactly. -/
theorem RawMolecule.toSemanticMolecule?_atomCount
    (molecule : RawMolecule) (semantic : SemanticMolecule)
    (converted : molecule.toSemanticMolecule? = some semantic) :
    semantic.atomCount = molecule.atomCount := by
  cases atomsObserved : semanticAtomList? molecule.atoms with
  | none =>
      simp [RawMolecule.toSemanticMolecule?, RawMolecule.semanticAtoms?, atomsObserved] at converted
  | some atoms =>
      have sameLength : atoms.length = molecule.atoms.length :=
        semanticAtomList?_length atomsObserved
      simp [RawMolecule.toSemanticMolecule?, RawMolecule.semanticAtoms?, atomsObserved] at converted
      subst semantic
      simpa [SemanticMolecule.atomCount, RawMolecule.atomCount] using sameLength

/-- Successful parser conversion is indexwise exact: looking up a semantic atom is the same as
looking up the parser atom at that index and applying the checked single-atom conversion. -/
theorem RawMolecule.toSemanticMolecule?_atomAt?
    (molecule : RawMolecule) (semantic : SemanticMolecule)
    (converted : molecule.toSemanticMolecule? = some semantic) (index : ℕ) :
    listGet? semantic.atoms index =
      (molecule.atomAt? index).bind AtomSpec.toSemanticAtom? := by
  cases atomsObserved : semanticAtomList? molecule.atoms with
  | none =>
      simp [RawMolecule.toSemanticMolecule?, RawMolecule.semanticAtoms?, atomsObserved] at converted
  | some atoms =>
      have indexed := semanticAtomList?_listGet? atomsObserved index
      simp [RawMolecule.toSemanticMolecule?, RawMolecule.semanticAtoms?, atomsObserved] at converted
      subst semantic
      simpa [RawMolecule.atomAt?] using indexed

/-- Successful conversion preserves the interaction list literally: only atom spellings undergo
checked conversion. -/
theorem RawMolecule.toSemanticMolecule?_interactions
    (molecule : RawMolecule) (semantic : SemanticMolecule)
    (converted : molecule.toSemanticMolecule? = some semantic) :
    semantic.interactions = molecule.bonds.map RawBond.toSemanticInteraction := by
  cases atomsObserved : semanticAtomList? molecule.atoms with
  | none =>
      simp [RawMolecule.toSemanticMolecule?, RawMolecule.semanticAtoms?, atomsObserved] at converted
  | some atoms =>
      simp [RawMolecule.toSemanticMolecule?, RawMolecule.semanticAtoms?, atomsObserved] at converted
      subst semantic
      rfl

/-- At every real parser index, successful whole-molecule conversion exposes the exact successful
single-atom conversion stored at the same semantic-list position. -/
theorem RawMolecule.toSemanticMolecule?_atomAtFin
    (molecule : RawMolecule) (semantic : SemanticMolecule)
    (converted : molecule.toSemanticMolecule? = some semantic)
    (atom : Fin molecule.atomCount) :
    let rawIndex : Fin molecule.atoms.length :=
      ⟨atom.val, by simp [RawMolecule.atomCount]⟩
    ∃ sourceAtom : SemanticAtom,
      listGet? semantic.atoms atom.val = some sourceAtom ∧
        (molecule.atoms.get rawIndex).toSemanticAtom? = some sourceAtom := by
  let rawIndex : Fin molecule.atoms.length :=
    ⟨atom.val, by simp [RawMolecule.atomCount]⟩
  have rawLookup : molecule.atomAt? atom.val = some (molecule.atoms.get rawIndex) := by
    simpa [RawMolecule.atomAt?, rawIndex] using
      (listGet?_eq_some_get molecule.atoms rawIndex)
  have indexed := molecule.toSemanticMolecule?_atomAt? semantic converted atom.val
  rw [rawLookup] at indexed
  have countExact := molecule.toSemanticMolecule?_atomCount semantic converted
  let semanticIndex : Fin semantic.atoms.length :=
    ⟨atom.val, by
      change atom.val < semantic.atomCount
      rw [countExact]
      exact atom.isLt⟩
  let sourceAtom := semantic.atoms.get semanticIndex
  have semanticLookup : listGet? semantic.atoms atom.val = some sourceAtom := by
    simpa [semanticIndex, sourceAtom] using
      (listGet?_eq_some_get semantic.atoms semanticIndex)
  exact ⟨sourceAtom, semanticLookup, indexed.symm.trans semanticLookup⟩

/-- The parser bridge preserves and reflects endpoint well-formedness exactly.  This is the first
refinement fact connecting the format-specific admission contract to the universal representation;
raw unordered-edge uniqueness remains an additional parser-side condition. -/
theorem RawMolecule.toSemanticMolecule?_structurallyWellFormed_iff
    (molecule : RawMolecule) (semantic : SemanticMolecule)
    (embedded : molecule.toSemanticMolecule? = some semantic) :
    semantic.StructurallyWellFormed ↔ molecule.WellFormed := by
  cases atomsObserved : semanticAtomList? molecule.atoms with
  | none =>
      simp [RawMolecule.toSemanticMolecule?, RawMolecule.semanticAtoms?, atomsObserved] at embedded
  | some atoms =>
      have sameLength : atoms.length = molecule.atoms.length :=
        semanticAtomList?_length atomsObserved
      simp [RawMolecule.toSemanticMolecule?, RawMolecule.semanticAtoms?, atomsObserved] at embedded
      subst semantic
      simp [SemanticMolecule.StructurallyWellFormed, SemanticMolecule.atomCount,
        RawMolecule.WellFormed, RawMolecule.BondEndpointsOK, RawMolecule.atomCount, sameLength]

@[simp] theorem RawMolecule.toSemanticMolecule?_isSome (molecule : RawMolecule) :
    molecule.toSemanticMolecule?.isSome = true ↔
      ∀ atom, atom ∈ molecule.atoms → atom.element ≠ .wildcard := by
  cases observed : semanticAtomList? molecule.atoms with
  | none =>
      have fails : ¬ ∀ atom, atom ∈ molecule.atoms → atom.element ≠ .wildcard := by
        intro known
        have present := (semanticAtomList?_isSome_iff_no_wildcard molecule.atoms).mpr known
        simp [observed] at present
      simp [RawMolecule.toSemanticMolecule?, RawMolecule.semanticAtoms?, observed, fails]
  | some atoms =>
      have known : ∀ atom, atom ∈ molecule.atoms → atom.element ≠ .wildcard := by
        apply (semanticAtomList?_isSome_iff_no_wildcard molecule.atoms).mp
        simp [observed]
      constructor
      · intro _
        exact known
      · intro _
        simp [RawMolecule.toSemanticMolecule?, RawMolecule.semanticAtoms?, observed]

def RawMolecule.toDiagramConfiguration (molecule : RawMolecule) : DiagramConfiguration :=
  { bonds := molecule.bonds.filterMap fun bond =>
      match bond.kind with
      | .up => some { source := bond.source, target := bond.target, style := .directionalUp }
      | .down => some { source := bond.source, target := bond.target, style := .directionalDown }
      | _ => none
    atomConfigurations := (enumerate molecule.atoms).filterMap fun indexed =>
      indexed.2.tetrahedral?.map fun parity =>
        { atom := indexed.1, parity := parity } }

/-- Format-neutral input produced by the current parser representation. -/
def RawMolecule.toAuthoritativeChemicalInput? (molecule : RawMolecule) :
    Option AuthoritativeChemicalInput := do
  let semantic ← molecule.toSemanticMolecule?
  some { molecule := semantic, diagram? := some molecule.toDiagramConfiguration }

/-- The structural part of an authoritative source is exactly the parser conversion, while
leaving independent evidence channels (in particular three-dimensional coordinates) free to be
attached.  This is the nonvacuous boundary needed to compare diagram and spatial evidence about
the same molecule. -/
def RawMolecule.AuthoritativeStructureAgreement
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput) : Prop :=
  molecule.toSemanticMolecule? = some source.molecule ∧
    source.diagram? = some molecule.toDiagramConfiguration

/-- Public conversion with an independently supplied exact spatial configuration.  It preserves
the same checked semantic molecule and parser diagram as `toAuthoritativeChemicalInput?`; only
the additional spatial evidence channel differs. -/
def RawMolecule.toAuthoritativeChemicalInputWithSpatial?
    (molecule : RawMolecule) (spatial : SpatialConfiguration) :
    Option AuthoritativeChemicalInput := do
  let semantic ← molecule.toSemanticMolecule?
  some {
    molecule := semantic
    spatial? := some spatial
    diagram? := some molecule.toDiagramConfiguration
  }

/-- Successful public ingestion is exact: its semantic molecule is precisely the checked
parser conversion, and its diagram evidence is precisely the directional/parity configuration
materialized from the same raw molecule. -/
theorem RawMolecule.toAuthoritativeChemicalInput?_exact
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : molecule.toAuthoritativeChemicalInput? = some source) :
    molecule.toSemanticMolecule? = some source.molecule ∧
      source.diagram? = some molecule.toDiagramConfiguration := by
  cases semanticObserved : molecule.toSemanticMolecule? with
  | none =>
      simp [RawMolecule.toAuthoritativeChemicalInput?, semanticObserved] at converted
  | some semantic =>
      simp [RawMolecule.toAuthoritativeChemicalInput?, semanticObserved] at converted
      subst source
      exact ⟨rfl, rfl⟩

/-- Successful parser-only ingestion satisfies the evidence-channel-independent structural
agreement relation. -/
theorem RawMolecule.authoritativeStructureAgreement_of_toAuthoritativeChemicalInput?
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : molecule.toAuthoritativeChemicalInput? = some source) :
    molecule.AuthoritativeStructureAgreement source :=
  molecule.toAuthoritativeChemicalInput?_exact source converted

/-- Successful spatially enriched ingestion has exactly the checked parser structure, exact
copied diagram evidence, and exactly the supplied spatial evidence. -/
theorem RawMolecule.toAuthoritativeChemicalInputWithSpatial?_exact
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toAuthoritativeChemicalInputWithSpatial? spatial = some source) :
    molecule.AuthoritativeStructureAgreement source ∧ source.spatial? = some spatial := by
  cases semanticObserved : molecule.toSemanticMolecule? with
  | none =>
      simp [RawMolecule.toAuthoritativeChemicalInputWithSpatial?, semanticObserved] at converted
  | some semantic =>
      simp [RawMolecule.toAuthoritativeChemicalInputWithSpatial?, semanticObserved] at converted
      subst source
      exact ⟨⟨semanticObserved, rfl⟩, rfl⟩

/-- The molecule projection of successful public ingestion is the checked semantic conversion. -/
theorem RawMolecule.toAuthoritativeChemicalInput?_molecule
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : molecule.toAuthoritativeChemicalInput? = some source) :
    molecule.toSemanticMolecule? = some source.molecule :=
  (molecule.toAuthoritativeChemicalInput?_exact source converted).1

/-- The diagram projection of successful public ingestion is exactly the raw parser evidence. -/
theorem RawMolecule.toAuthoritativeChemicalInput?_diagram
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : molecule.toAuthoritativeChemicalInput? = some source) :
    source.diagram? = some molecule.toDiagramConfiguration :=
  (molecule.toAuthoritativeChemicalInput?_exact source converted).2

@[simp] theorem RawMolecule.toAuthoritativeChemicalInput?_isSome (molecule : RawMolecule) :
    molecule.toAuthoritativeChemicalInput?.isSome = true ↔
      ∀ atom, atom ∈ molecule.atoms → atom.element ≠ .wildcard := by
  cases observed : molecule.toSemanticMolecule? with
  | none =>
      have fails : ¬ ∀ atom, atom ∈ molecule.atoms → atom.element ≠ .wildcard := by
        intro known
        have present := (RawMolecule.toSemanticMolecule?_isSome molecule).mpr known
        simp [observed] at present
      simp [RawMolecule.toAuthoritativeChemicalInput?, observed, fails]
  | some semantic =>
      have known : ∀ atom, atom ∈ molecule.atoms → atom.element ≠ .wildcard := by
        apply (RawMolecule.toSemanticMolecule?_isSome molecule).mp
        simp [observed]
      constructor
      · intro _
        exact known
      · intro _
        simp [RawMolecule.toAuthoritativeChemicalInput?, observed]

end TetraStereo.OneCenter
