import TetraStereo.OneCenter.P94MolecularRingCarrier

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace P94ConformationUnit

/-!
# Executable molecular applicability for P-94 coordinate rings

The coordinate classifiers must not accept a side ledger detached from the molecular graph.
This module reflects the finite `Bonded`, `ConsecutivelyBonded`, `CyclicallyBonded`, and ring-kind
`ValidFor` predicates into code-generatable Boolean checks.  It covers precisely the four ring
kinds consumed by the coordinate plane algorithms; other P-94 unit kinds remain outside this
selector rather than being silently approximated.
-/

/-- Executable undirected molecular adjacency. -/
def bonded? (molecule : RawMolecule) (left right : Nat) : Bool :=
  molecule.bonds.any fun bond => bond.connects left right

@[simp] theorem bonded?_eq_true_iff (molecule : RawMolecule) (left right : Nat) :
    bonded? molecule left right = true ↔ Bonded molecule left right := by
  simp [bonded?, Bonded]

/-- Executable adjacency check for every consecutive pair in a traversal. -/
def consecutivelyBonded? (molecule : RawMolecule) (atoms : List Nat) : Bool :=
  (atoms.zip atoms.tail).all fun pair => bonded? molecule pair.1 pair.2

@[simp] theorem consecutivelyBonded?_eq_true_iff
    (molecule : RawMolecule) (atoms : List Nat) :
    consecutivelyBonded? molecule atoms = true ↔
      ConsecutivelyBonded molecule atoms := by
  simp [consecutivelyBonded?, ConsecutivelyBonded]

/-- Executable closed-traversal adjacency, including the final-to-first edge. -/
def cyclicallyBonded? (molecule : RawMolecule) (atoms : List Nat) : Bool :=
  consecutivelyBonded? molecule atoms &&
    match atoms.head?, atoms.reverse.head? with
    | some first, some last => bonded? molecule last first
    | _, _ => false

@[simp] theorem cyclicallyBonded?_eq_true_iff
    (molecule : RawMolecule) (atoms : List Nat) :
    cyclicallyBonded? molecule atoms = true ↔ CyclicallyBonded molecule atoms := by
  cases firstComputed : atoms.head? with
  | none =>
      simp [cyclicallyBonded?, CyclicallyBonded, firstComputed]
  | some first =>
      cases lastComputed : atoms.reverse.head? with
      | none =>
          simp [cyclicallyBonded?, CyclicallyBonded, firstComputed, lastComputed]
      | some last =>
          simp [cyclicallyBonded?, CyclicallyBonded, firstComputed, lastComputed]

/-- The unit kinds whose `ValidFor` obligations are consumed by exact coordinate-ring selection. -/
def SupportedCoordinateRingKind : P94ConformationUnitKind → Prop
  | .fiveMemberedRing | .sixMemberedRing | .crownRing | .eightMemberedTubRing => True
  | _ => False

/-- Complete finite molecular admission for coordinate envelope, six-ring, crown, and tub units. -/
def ringValidFor? (unit : P94ConformationUnit) (molecule : RawMolecule) : Bool :=
  decide unit.atoms.Nodup &&
    unit.atoms.all (fun atom => decide (atom < molecule.atomCount)) &&
      match unit.kind with
      | .fiveMemberedRing =>
          decide (unit.torsionParticipants? = none) &&
            decide (unit.atoms.length = 5) && cyclicallyBonded? molecule unit.atoms
      | .sixMemberedRing =>
          decide (unit.torsionParticipants? = none) &&
            decide (unit.atoms.length = 6) && cyclicallyBonded? molecule unit.atoms
      | .crownRing =>
          decide (unit.torsionParticipants? = none) &&
            decide (8 ≤ unit.atoms.length) && decide (Even unit.atoms.length) &&
              cyclicallyBonded? molecule unit.atoms
      | .eightMemberedTubRing =>
          decide (unit.torsionParticipants? = none) &&
            decide (unit.atoms.length = 8) && cyclicallyBonded? molecule unit.atoms
      | _ => false

/-- Exact reflection of molecular validity on the supported coordinate-ring kinds. -/
@[simp] theorem ringValidFor?_eq_true_iff
    (unit : P94ConformationUnit) (molecule : RawMolecule) :
    ringValidFor? unit molecule = true ↔
      unit.ValidFor molecule ∧ SupportedCoordinateRingKind unit.kind := by
  cases kind : unit.kind <;>
    simp [ringValidFor?, ValidFor, SupportedCoordinateRingKind, kind] <;> tauto

end P94ConformationUnit

end TetraStereo.OneCenter
