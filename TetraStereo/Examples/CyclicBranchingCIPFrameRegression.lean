import TetraStereo.OneCenter.DeclarativeCIPOccurrenceRules456

/-!
# Cyclic branching CIP-frame regression

The tetrahedral center belongs to a carbon triangle.  Its two ring-ligand cursors traverse the
opposite carbon and terminate at canonical ring-duplicate occurrences.  Because the common
incoming center is cyclic, the legacy conflict gate cannot demand that it simultaneously be
acyclic, and every production comparison in the exact frame succeeds.
-/

set_option autoImplicit false

namespace TetraStereo.Examples.CyclicBranchingCIPFrameRegression

open OneCenter
open OneCenter.DeclarativeCIP
open OneCenter.DeclarativeCIP.ProductionOccurrenceRules456
open OneCenter.ProductionCIPRerootComparatorLaws

private def center : AtomSpec :=
  { AtomSpec.aliphatic Element.C with tetrahedral? := some .clockwise }

private def carbon : AtomSpec := AtomSpec.aliphatic Element.C

private def molecule : RawMolecule where
  atoms := [center, carbon, carbon, AtomSpec.aliphatic Element.F,
    AtomSpec.aliphatic Element.Cl]
  bonds :=
    [ { source := 0, target := 1, kind := .single },
      { source := 1, target := 2, kind := .single },
      { source := 2, target := 0, kind := .single },
      { source := 0, target := 3, kind := .single },
      { source := 0, target := 4, kind := .single } ]

private def node : RawMolecule.CanonicalBranchNode :=
  { atom := 0, parent := 0, history := [0], provenance := .realAtom }

private def root (atom : Nat) : CanonicalRerootCursor :=
  { node := RawMolecule.canonicalRoot 0 atom, previous? := some node }

private def child (rootAtom childAtom : Nat) : CanonicalRerootCursor :=
  { node :=
      { atom := childAtom, parent := rootAtom, history := [childAtom, rootAtom, 0],
        provenance := .realAtom }
    previous? := some (root rootAtom).node }

private def ringClose (rootAtom childAtom : Nat) : CanonicalRerootCursor :=
  { node :=
      { atom := 0, parent := childAtom, history := [0, childAtom, rootAtom, 0],
        provenance := .ringDuplicate 0 }
    previous? := some (child rootAtom childAtom).node }

private def roots : List CanonicalRerootCursor := [root 1, root 2, root 3, root 4]

private def supportedRingRoot (rootAtom childAtom : Nat)
    (rootLabel : ∃ label, molecule.canonicalRule1aLabel? (root rootAtom).node = some label)
    (childLabel : ∃ label,
      molecule.canonicalRule1aLabel? (child rootAtom childAtom).node = some label)
    (closeLabel : ∃ label,
      molecule.canonicalRule1aLabel? (ringClose rootAtom childAtom).node = some label)
    (rootChildren : (root rootAtom).children molecule = [child rootAtom childAtom])
    (childChildren : (child rootAtom childAtom).children molecule =
      [ringClose rootAtom childAtom])
    (closeTerminal : cursorTerminal molecule (ringClose rootAtom childAtom) = true) :
    BranchingCursorSupport molecule 2 (root rootAtom) :=
  .branch 1 (root rootAtom) [child rootAtom childAtom] rootLabel rootChildren (by simp) (by
    intro candidate member
    simp at member
    subst candidate
    exact .branch 0 (child rootAtom childAtom) [ringClose rootAtom childAtom]
      childLabel childChildren (by simp) (by
        intro close closeMember
        simp at closeMember
        subst close
        exact .terminal 0 (ringClose rootAtom childAtom) closeLabel closeTerminal))

private def support1 : BranchingCursorSupport molecule 2 (root 1) := by
  apply supportedRingRoot 1 2
  all_goals first | decide | simp [root, child, ringClose, RawMolecule.canonicalRoot,
    RawMolecule.canonicalRule1aLabel?]

private def support2 : BranchingCursorSupport molecule 2 (root 2) := by
  apply supportedRingRoot 2 1
  all_goals first | decide | simp [root, child, ringClose, RawMolecule.canonicalRoot,
    RawMolecule.canonicalRule1aLabel?]

private def support3 : BranchingCursorSupport molecule 2 (root 3) := by
  apply BranchingCursorSupport.terminal
  · simp [root, RawMolecule.canonicalRoot, RawMolecule.canonicalRule1aLabel?]
  · decide

private def support4 : BranchingCursorSupport molecule 2 (root 4) := by
  apply BranchingCursorSupport.terminal
  · simp [root, RawMolecule.canonicalRoot, RawMolecule.canonicalRule1aLabel?]
  · decide

theorem frame_generated : occurrenceLigandFrame? molecule node = some roots := by decide

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
    simp [RawMolecule.atomAt?, listGet?, molecule, center, carbon, AtomSpec.aliphatic] at atomEq
  all_goals subst atom
  all_goals
    simp [RawMolecule.atomAt?, listGet?, RawMolecule.usedValenceAt,
      RawMolecule.incidentBondOrderSum, AtomSpec.allowedValences,
      AtomSpec.explicitHydrogens, ParsedBondKind.order,
      Element.allowedValences, molecule, center, carbon, AtomSpec.aliphatic]

def frame : CyclicIncomingDescriptorBranchingCIPFrame
    (mol := molecule) [] 2 node roots where
  spec := center
  parity := .clockwise
  admissible := molecule_admissible
  valence_ok := molecule_valence_ok
  atom_spec := by decide
  tetrahedral := by decide
  ligand_frame := frame_generated
  roots_length := by decide
  frontier_envelope := by decide
  support := by
    intro cursor member
    simp [roots] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact support1
    · exact support2
    · exact support3
    · exact support4
  center_cyclic := by decide
  incoming_frame := by
    intro cursor member
    simp [roots] at member
    rcases member with rfl | rfl | rfl | rfl <;> rfl
  rule4b_arity := 0
  rule4b_arity_le := by decide
  rule4b_uniform := by
    intro cursor member
    simp [roots] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide

theorem ring_is_genuinely_traversed :
    molecule.atomLiesInCycle 2 node.atom = true ∧
    molecule.atomLiesInCycle 2 (root 1).node.atom = true ∧
    molecule.atomLiesInCycle 2 (root 2).node.atom = true ∧
    (child 1 2).children molecule = [ringClose 1 2] ∧
    (child 2 1).children molecule = [ringClose 2 1] := by decide

theorem all_directed_pairs_succeed
    {left right : CanonicalRerootCursor} (leftMem : left ∈ roots) (rightMem : right ∈ roots) :
    ∃ decision, compareOccurrenceBranches? molecule [] 2 left right = some decision :=
  frame.comparison_exists leftMem rightMem

theorem cyclic_two_success_endpoint :
    ∃ endpoint,
      compareOccurrenceBranches? molecule [] 2 (root 1) (root 3) = some endpoint ∧
        endpoint.ordering = Ordering.lt := by
  exact frame.endpoint_of_two_success
    (left := root 1) (middle := root 2) (right := root 3)
    (leftMiddle := { ordering := .eq }) (middleRight := { ordering := .lt })
    (composed := .lt)
    (by simp [roots]) (by simp [roots]) (by simp [roots])
    (by decide) (by decide) (by decide)

end TetraStereo.Examples.CyclicBranchingCIPFrameRegression
