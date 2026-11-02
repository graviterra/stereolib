import TetraStereo.OneCenter.DeclarativeCIPOccurrenceRules456

/-!
# Branching acyclic CIP-frame regression

All four ligand roots are carbon atoms with two forward children: a halogen and an explicit
hydrogen.  Production child ranking must therefore execute a genuine sibling comparison before
the second-sphere ligand frames can be compared.
-/

set_option autoImplicit false

namespace TetraStereo.Examples.BranchingAcyclicCIPFrameRegression

open OneCenter
open OneCenter.DeclarativeCIP
open OneCenter.DeclarativeCIP.ProductionOccurrenceRules456
open OneCenter.ProductionCIPRerootComparatorLaws
open OneCenter.ProductionCIPBranchingOccurrenceComparatorCompleteness

private def center : AtomSpec :=
  { AtomSpec.aliphatic Element.C with tetrahedral? := some .clockwise }

private def carbon : AtomSpec := AtomSpec.aliphatic Element.C

private def molecule : RawMolecule where
  atoms := [center,
    carbon, AtomSpec.aliphatic Element.F, AtomSpec.aliphatic Element.H,
    carbon, AtomSpec.aliphatic Element.Cl, AtomSpec.aliphatic Element.H,
    carbon, AtomSpec.aliphatic Element.Br, AtomSpec.aliphatic Element.H,
    carbon, AtomSpec.aliphatic Element.I, AtomSpec.aliphatic Element.H]
  bonds :=
    [ { source := 0, target := 1, kind := .single },
      { source := 1, target := 2, kind := .single },
      { source := 1, target := 3, kind := .single },
      { source := 0, target := 4, kind := .single },
      { source := 4, target := 5, kind := .single },
      { source := 4, target := 6, kind := .single },
      { source := 0, target := 7, kind := .single },
      { source := 7, target := 8, kind := .single },
      { source := 7, target := 9, kind := .single },
      { source := 0, target := 10, kind := .single },
      { source := 10, target := 11, kind := .single },
      { source := 10, target := 12, kind := .single } ]

private def node : RawMolecule.CanonicalBranchNode :=
  { atom := 0, parent := 0, history := [0], provenance := .realAtom }

private def root (atom : Nat) : CanonicalRerootCursor :=
  { node := RawMolecule.canonicalRoot 0 atom, previous? := some node }

private def child (rootAtom childAtom : Nat) : CanonicalRerootCursor :=
  { node :=
      { atom := childAtom, parent := rootAtom, history := [childAtom, rootAtom, 0],
        provenance := .realAtom }
    previous? := some (root rootAtom).node }

private def roots : List CanonicalRerootCursor := [root 1, root 4, root 7, root 10]

private def supportedRoot (rootAtom firstChild secondChild : Nat)
    (rootLabel : ∃ label, molecule.canonicalRule1aLabel? (root rootAtom).node = some label)
    (firstLabel : ∃ label,
      molecule.canonicalRule1aLabel? (child rootAtom firstChild).node = some label)
    (secondLabel : ∃ label,
      molecule.canonicalRule1aLabel? (child rootAtom secondChild).node = some label)
    (children : (root rootAtom).children molecule =
      [child rootAtom firstChild, child rootAtom secondChild])
    (firstTerminal : cursorTerminal molecule (child rootAtom firstChild) = true)
    (secondTerminal : cursorTerminal molecule (child rootAtom secondChild) = true)
    (rootAcyclic : molecule.atomLiesInCycle 1 (root rootAtom).node.atom = false)
    (firstAcyclic : molecule.atomLiesInCycle 1 (child rootAtom firstChild).node.atom = false)
    (secondAcyclic : molecule.atomLiesInCycle 1 (child rootAtom secondChild).node.atom = false) :
    AcyclicBranchingCursorSupport molecule 1 (root rootAtom) :=
  { branching := .branch 0 (root rootAtom)
      [child rootAtom firstChild, child rootAtom secondChild] rootLabel children (by simp) (by
        intro candidate member
        simp at member
        rcases member with rfl | rfl
        · exact .terminal 0 (child rootAtom firstChild) firstLabel firstTerminal
        · exact .terminal 0 (child rootAtom secondChild) secondLabel secondTerminal)
    acyclic := .branch (root rootAtom)
      [child rootAtom firstChild, child rootAtom secondChild] rootAcyclic children (by
        intro candidate member
        simp at member
        rcases member with rfl | rfl
        · exact .terminal (child rootAtom firstChild) firstAcyclic firstTerminal
        · exact .terminal (child rootAtom secondChild) secondAcyclic secondTerminal) }

private def support1 : AcyclicBranchingCursorSupport molecule 1 (root 1) := by
  apply supportedRoot 1 2 3
  all_goals first | decide | simp [root, child, RawMolecule.canonicalRoot,
    RawMolecule.canonicalRule1aLabel?]

private def support4 : AcyclicBranchingCursorSupport molecule 1 (root 4) := by
  apply supportedRoot 4 5 6
  all_goals first | decide | simp [root, child, RawMolecule.canonicalRoot,
    RawMolecule.canonicalRule1aLabel?]

private def support7 : AcyclicBranchingCursorSupport molecule 1 (root 7) := by
  apply supportedRoot 7 8 9
  all_goals first | decide | simp [root, child, RawMolecule.canonicalRoot,
    RawMolecule.canonicalRule1aLabel?]

private def support10 : AcyclicBranchingCursorSupport molecule 1 (root 10) := by
  apply supportedRoot 10 11 12
  all_goals first | decide | simp [root, child, RawMolecule.canonicalRoot,
    RawMolecule.canonicalRule1aLabel?]

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
  have bound : idx < 13 := by
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

def frame : BranchingAcyclicCIPFrame (mol := molecule) 1 node roots where
  spec := center
  parity := .clockwise
  admissible := molecule_admissible
  valence_ok := molecule_valence_ok
  atom_spec := by decide
  tetrahedral := by decide
  ligand_frame := frame_generated
  roots_length := frame_length
  frontier_envelope := by decide
  support := by
    intro cursor member
    simp [roots] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact support1
    · exact support4
    · exact support7
    · exact support10

theorem roots_have_two_forward_children :
    (root 1).children molecule = [child 1 2, child 1 3] ∧
    (root 4).children molecule = [child 4 5, child 4 6] ∧
    (root 7).children molecule = [child 7 8, child 7 9] ∧
    (root 10).children molecule = [child 10 11, child 10 12] := by decide

theorem all_directed_pairs_succeed
    {left right : CanonicalRerootCursor} (leftMem : left ∈ roots) (rightMem : right ∈ roots) :
    ∃ decision, compareOccurrenceBranches? molecule [] 1 left right = some decision :=
  frame.comparison_exists leftMem rightMem

theorem branched_second_sphere_two_success_endpoint :
    ∃ endpoint,
      compareOccurrenceBranches? molecule [] 1 (root 1) (root 7) = some endpoint ∧
        endpoint.ordering = Ordering.lt := by
  exact frame.endpoint_of_two_success
    (left := root 1) (middle := root 4) (right := root 7)
    (leftMiddle := { ordering := .lt }) (middleRight := { ordering := .lt })
    (composed := .lt)
    (by simp [roots]) (by simp [roots]) (by simp [roots])
    (by decide) (by decide) (by decide)

end TetraStereo.Examples.BranchingAcyclicCIPFrameRegression
