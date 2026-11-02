import TetraStereo.OneCenter.DeclarativeCIPOccurrenceRules456

/-!
# Linear acyclic CIP-frame regression

This example forces the production comparator past four identical first-sphere
carbon atoms.  Their unique forward children are F, Cl, Br, and I, so successful
comparison and endpoint closure genuinely use the recursively proved linear-chain
case rather than the terminal-root theorem.
-/

set_option autoImplicit false

namespace TetraStereo.Examples.LinearAcyclicCIPFrameRegression

open OneCenter
open OneCenter.DeclarativeCIP
open OneCenter.DeclarativeCIP.ProductionOccurrenceRules456
open OneCenter.ProductionCIPRerootComparatorLaws
open OneCenter.ProductionCIPLinearOccurrenceComparatorCompleteness

private def center : AtomSpec :=
  { AtomSpec.aliphatic Element.C with tetrahedral? := some .clockwise }

private def carbon : AtomSpec := AtomSpec.aliphatic Element.C

private def molecule : RawMolecule where
  atoms := [center, carbon, AtomSpec.aliphatic Element.F,
    carbon, AtomSpec.aliphatic Element.Cl,
    carbon, AtomSpec.aliphatic Element.Br,
    carbon, AtomSpec.aliphatic Element.I]
  bonds :=
    [ { source := 0, target := 1, kind := .single },
      { source := 1, target := 2, kind := .single },
      { source := 0, target := 3, kind := .single },
      { source := 3, target := 4, kind := .single },
      { source := 0, target := 5, kind := .single },
      { source := 5, target := 6, kind := .single },
      { source := 0, target := 7, kind := .single },
      { source := 7, target := 8, kind := .single } ]

private def node : RawMolecule.CanonicalBranchNode :=
  { atom := 0, parent := 0, history := [0], provenance := .realAtom }

private def root (atom : Nat) : CanonicalRerootCursor :=
  { node := RawMolecule.canonicalRoot 0 atom, previous? := some node }

private def child (rootAtom childAtom : Nat) : CanonicalRerootCursor :=
  { node :=
      { atom := childAtom, parent := rootAtom, history := [childAtom, rootAtom, 0],
        provenance := .realAtom }
    previous? := some (root rootAtom).node }

private def roots : List CanonicalRerootCursor := [root 1, root 3, root 5, root 7]

private def supportedRoot (rootAtom childAtom : Nat)
    (rootLabel : ∃ label, molecule.canonicalRule1aLabel? (root rootAtom).node = some label)
    (childLabel : ∃ label,
      molecule.canonicalRule1aLabel? (child rootAtom childAtom).node = some label)
    (children : (root rootAtom).children molecule = [child rootAtom childAtom])
    (childTerminal : cursorTerminal molecule (child rootAtom childAtom) = true)
    (rootAcyclic : molecule.atomLiesInCycle 2 (root rootAtom).node.atom = false)
    (childAcyclic : molecule.atomLiesInCycle 2 (child rootAtom childAtom).node.atom = false) :
    AcyclicLinearCursorSupport molecule 2 (root rootAtom) :=
  { linear := .step 1 (root rootAtom) (child rootAtom childAtom) rootLabel children
      (.terminal 1 (child rootAtom childAtom) childLabel childTerminal)
    acyclic := .step (root rootAtom) (child rootAtom childAtom) rootAcyclic children
      (.terminal (child rootAtom childAtom) childAcyclic childTerminal) }

private def support1 : AcyclicLinearCursorSupport molecule 2 (root 1) := by
  apply supportedRoot 1 2
  all_goals first | decide | simp [root, child, RawMolecule.canonicalRoot,
    RawMolecule.canonicalRule1aLabel?]

private def support3 : AcyclicLinearCursorSupport molecule 2 (root 3) := by
  apply supportedRoot 3 4
  all_goals first | decide | simp [root, child, RawMolecule.canonicalRoot,
    RawMolecule.canonicalRule1aLabel?]

private def support5 : AcyclicLinearCursorSupport molecule 2 (root 5) := by
  apply supportedRoot 5 6
  all_goals first | decide | simp [root, child, RawMolecule.canonicalRoot,
    RawMolecule.canonicalRule1aLabel?]

private def support7 : AcyclicLinearCursorSupport molecule 2 (root 7) := by
  apply supportedRoot 7 8
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
  have bound : idx < 9 := by
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

def frame : LinearAcyclicCIPFrame (mol := molecule) 2 node roots where
  spec := center
  parity := .clockwise
  admissible := molecule_admissible
  valence_ok := molecule_valence_ok
  atom_spec := by decide
  tetrahedral := by decide
  ligand_frame := frame_generated
  roots_length := frame_length
  support := by
    intro cursor member
    simp [roots] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact support1
    · exact support3
    · exact support5
    · exact support7

theorem roots_are_genuinely_nonterminal :
    cursorTerminal molecule (root 1) = false ∧
    cursorTerminal molecule (root 3) = false ∧
    cursorTerminal molecule (root 5) = false ∧
    cursorTerminal molecule (root 7) = false := by decide

theorem all_directed_pairs_succeed
    {left right : CanonicalRerootCursor} (leftMem : left ∈ roots) (rightMem : right ∈ roots) :
    ∃ decision, compareOccurrenceBranches? molecule [] 2 left right = some decision :=
  frame.comparison_exists leftMem rightMem

theorem second_sphere_chain_two_success_endpoint :
    ∃ endpoint,
      compareOccurrenceBranches? molecule [] 2 (root 1) (root 5) = some endpoint ∧
        endpoint.ordering = Ordering.lt := by
  exact frame.endpoint_of_two_success
    (left := root 1) (middle := root 3) (right := root 5)
    (leftMiddle := { ordering := .lt }) (middleRight := { ordering := .lt })
    (composed := .lt)
    (by simp [roots]) (by simp [roots]) (by simp [roots])
    (by decide) (by decide) (by decide)

end TetraStereo.Examples.LinearAcyclicCIPFrameRegression
