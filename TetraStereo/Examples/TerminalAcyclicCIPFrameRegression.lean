import TetraStereo.OneCenter.DeclarativeCIPOccurrenceRules456

set_option autoImplicit false

namespace TetraStereo.Examples.TerminalAcyclicCIPFrameRegression

open OneCenter
open OneCenter.DeclarativeCIP
open OneCenter.DeclarativeCIP.ProductionOccurrenceRules456

/-! A concrete, chemically admitted inhabitant of the structural comparator-completeness class. -/

private def center : AtomSpec :=
  { AtomSpec.aliphatic Element.C with tetrahedral? := some .clockwise }

/-- Tetrahedral bromochlorofluoroiodomethane skeleton: the center is directly bonded to four
terminal, constitutionally distinct halogen ligands. -/
private def molecule : RawMolecule where
  atoms := [center, AtomSpec.aliphatic Element.F, AtomSpec.aliphatic Element.Cl,
    AtomSpec.aliphatic Element.Br, AtomSpec.aliphatic Element.I]
  bonds :=
    [ { source := 0, target := 1, kind := .single },
      { source := 0, target := 2, kind := .single },
      { source := 0, target := 3, kind := .single },
      { source := 0, target := 4, kind := .single } ]

private def node : RawMolecule.CanonicalBranchNode :=
  { atom := 0, parent := 0, history := [0], provenance := .realAtom }

private def root (atom : Nat) : CanonicalRerootCursor :=
  { node := RawMolecule.canonicalRoot 0 atom, previous? := some node }

private def roots : List CanonicalRerootCursor := [root 1, root 2, root 3, root 4]

theorem frame_generated : occurrenceLigandFrame? molecule node = some roots := by decide

theorem frame_length : roots.length = 4 := by decide

theorem molecule_admissible : molecule.Admissible := by
  simp [RawMolecule.Admissible, RawMolecule.WellFormed, RawMolecule.BondEndpointsOK,
    RawMolecule.BondRecordsUnique, RawBond.edgeKey, molecule, RawMolecule.atomCount]

private theorem listGet?_some_lt {alpha : Type} :
    ∀ (values : List alpha) (idx : Nat) (value : alpha),
      listGet? values idx = some value → idx < values.length
  | [], _, _, computed => by simp [listGet?] at computed
  | _ :: _, 0, _, _ => by simp
  | _ :: values, idx + 1, value, computed => by
      exact Nat.succ_lt_succ (listGet?_some_lt values idx value (by
        simpa [listGet?] using computed))

theorem molecule_valence_ok : molecule.ValenceOK := by
  intro idx atom atomEq
  have bound : idx < 5 := by
    exact listGet?_some_lt molecule.atoms idx atom (by
      simpa [RawMolecule.atomAt?] using atomEq)
  interval_cases idx
  all_goals
    simp [RawMolecule.atomAt?, listGet?, molecule, center, AtomSpec.aliphatic] at atomEq
  all_goals subst atom
  all_goals
    simp [RawMolecule.atomAt?, listGet?, RawMolecule.usedValenceAt,
      RawMolecule.incidentBondOrderSum, AtomSpec.allowedValences,
      AtomSpec.explicitHydrogens, ParsedBondKind.order,
      Element.allowedValences, molecule, center, AtomSpec.aliphatic]

/-- The example frame contains no comparator-success fields.  All support facts are computed from
the admitted molecule, exact generated roots, and empty local auxiliary state. -/
def frame : TerminalAcyclicCIPFrame (mol := molecule) [] 6 node roots where
  spec := center
  parity := .clockwise
  admissible := molecule_admissible
  valence_ok := molecule_valence_ok
  atom_spec := by decide
  tetrahedral := by decide
  ligand_frame := frame_generated
  roots_length := frame_length
  terminal := by
    intro cursor member
    simp [roots] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide
  acyclic := by
    intro cursor member
    simp [roots] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide
  rule1a_supported := by
    intro cursor member
    simp [roots] at member
    rcases member with rfl | rfl | rfl | rfl <;>
      simp [root, RawMolecule.canonicalRoot, RawMolecule.canonicalRule1aLabel?]
  descriptor_silent := by
    intro cursor _member
    simp [OccurrenceAuxState.factAt?]

/-- The structural frame theorem, rather than a stored sixteen-call certificate, proves all
directed production comparisons exist. -/
theorem all_directed_pairs_succeed
    {left right : CanonicalRerootCursor} (leftMem : left ∈ roots) (rightMem : right ∈ roots) :
    ∃ decision, compareOccurrenceBranches? molecule [] 6 left right = some decision :=
  frame.comparison_exists leftMem rightMem

/-- Concrete use of the two-success theorem: F < Cl and Cl < Br force an actual F < Br endpoint
call on the production comparator. -/
theorem fluorine_chlorine_bromine_two_success_endpoint :
    ∃ endpoint,
      compareOccurrenceBranches? molecule [] 6 (root 1) (root 3) = some endpoint ∧
        endpoint.ordering = Ordering.lt := by
  exact frame.endpoint_of_two_success
    (left := root 1) (middle := root 2) (right := root 3)
    (leftMiddle := { ordering := .lt }) (middleRight := { ordering := .lt })
    (composed := .lt)
    (by simp [roots]) (by simp [roots]) (by simp [roots])
    (by decide) (by decide) (by decide)

end TetraStereo.Examples.TerminalAcyclicCIPFrameRegression
