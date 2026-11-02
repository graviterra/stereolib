import TetraStereo.OneCenter.DeclarativeCIPOccurrenceRules456
import TetraStereo.OneCenter.CIPBlueBookConformance

/-!
# Descriptor-bearing branching CIP-frame regression

All four constitutionally identical carbon branches have two forward children (F and H).  Root
auxiliary facts keep Rule-4b arity uniformly one and force the production comparison through to a
genuine pseudoasymmetric Rule-5 decision.
-/

set_option autoImplicit false

namespace TetraStereo.Examples.DescriptorBranchingCIPFrameRegression

open OneCenter
open OneCenter.DeclarativeCIP
open OneCenter.DeclarativeCIP.ProductionOccurrenceRules456
open OneCenter.ProductionCIPRerootComparatorLaws
open OneCenter.ProductionCIPDescriptorBranchingCompleteness

private def center : AtomSpec :=
  { AtomSpec.aliphatic Element.C with tetrahedral? := some .clockwise }

private def carbon : AtomSpec := AtomSpec.aliphatic Element.C

private def molecule : RawMolecule where
  atoms := [center,
    carbon, AtomSpec.aliphatic Element.F, AtomSpec.aliphatic Element.H,
    carbon, AtomSpec.aliphatic Element.F, AtomSpec.aliphatic Element.H,
    carbon, AtomSpec.aliphatic Element.F, AtomSpec.aliphatic Element.H,
    carbon, AtomSpec.aliphatic Element.F, AtomSpec.aliphatic Element.H]
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

private def fact (atom : Nat) (descriptor : RS) : OccurrenceAuxFact :=
  { key := canonicalOccurrenceKey (root atom).node
    atom := atom
    descriptor := descriptor
    uppercase := true }

private def state : OccurrenceAuxState :=
  [fact 1 .S, fact 4 .S, fact 7 .R, fact 10 .R]

private def childFact (rootAtom childAtom : Nat) (descriptor : RS) : OccurrenceAuxFact :=
  { key := canonicalOccurrenceKey (child rootAtom childAtom).node
    atom := childAtom
    descriptor := descriptor
    uppercase := true }

/-- A reachable P-92.5.2.1 criterion-(c)(i) state: the left ligand selects one `R` reference at
its root, while the right ligand first encounters an equal `R/S` population and selects two. -/
private def oneReferenceVersusTwoState : OccurrenceAuxState :=
  [fact 1 .R, childFact 7 8 .R, childFact 7 9 .S]

private def supportedRoot (rootAtom firstChild secondChild : Nat)
    (rootLabel : ∃ label, molecule.canonicalRule1aLabel? (root rootAtom).node = some label)
    (firstLabel : ∃ label,
      molecule.canonicalRule1aLabel? (child rootAtom firstChild).node = some label)
    (secondLabel : ∃ label,
      molecule.canonicalRule1aLabel? (child rootAtom secondChild).node = some label)
    (children : (root rootAtom).children molecule =
      [child rootAtom firstChild, child rootAtom secondChild])
    (firstTerminal : cursorTerminal molecule (child rootAtom firstChild) = true)
    (secondTerminal : cursorTerminal molecule (child rootAtom secondChild) = true) :
    BranchingCursorSupport molecule 1 (root rootAtom) :=
  .branch 0 (root rootAtom) [child rootAtom firstChild, child rootAtom secondChild]
    rootLabel children (by simp) (by
      intro candidate member
      simp at member
      rcases member with rfl | rfl
      · exact .terminal 0 (child rootAtom firstChild) firstLabel firstTerminal
      · exact .terminal 0 (child rootAtom secondChild) secondLabel secondTerminal)

private def support1 : BranchingCursorSupport molecule 1 (root 1) := by
  apply supportedRoot 1 2 3
  all_goals first | decide | simp [root, child, RawMolecule.canonicalRoot,
    RawMolecule.canonicalRule1aLabel?]

private def support4 : BranchingCursorSupport molecule 1 (root 4) := by
  apply supportedRoot 4 5 6
  all_goals first | decide | simp [root, child, RawMolecule.canonicalRoot,
    RawMolecule.canonicalRule1aLabel?]

private def support7 : BranchingCursorSupport molecule 1 (root 7) := by
  apply supportedRoot 7 8 9
  all_goals first | decide | simp [root, child, RawMolecule.canonicalRoot,
    RawMolecule.canonicalRule1aLabel?]

private def support10 : BranchingCursorSupport molecule 1 (root 10) := by
  apply supportedRoot 10 11 12
  all_goals first | decide | simp [root, child, RawMolecule.canonicalRoot,
    RawMolecule.canonicalRule1aLabel?]

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

def frame : DescriptorBranchingCIPFrame (mol := molecule) state 1 node roots where
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
    · exact support4
    · exact support7
    · exact support10
  gate_neutral := by
    intro cursor member
    apply RootRelativeGateNeutral.atomAcyclic
    simp [roots] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide
  rule4b_arity := 1
  rule4b_arity_le := by decide
  rule4b_uniform := by
    intro cursor member
    simp [roots] at member
    rcases member with rfl | rfl | rfl | rfl <;>
      decide

theorem all_directed_pairs_succeed
    {left right : CanonicalRerootCursor} (leftMem : left ∈ roots) (rightMem : right ∈ roots) :
    ∃ decision, compareOccurrenceBranches? molecule state 1 left right = some decision :=
  frame.comparison_exists leftMem rightMem

theorem rule5_genuinely_decides :
    compareCursorBranchAt molecule 1 .rule2 (root 1) (root 7) = some .eq ∧
    compareOccurrenceDescriptorAtTiedRoot? molecule state 1 .rule4a
      (root 1) (root 7) = some .eq ∧
    compareOccurrenceRule4b? molecule state 1 (root 1) (root 7) = some .eq ∧
    compareOccurrenceRule5? molecule state 1 (root 1) (root 7) =
      some { ordering := .lt, pseudo := true } ∧
    compareOccurrenceBranches? molecule state 1 (root 1) (root 7) =
      some { ordering := .lt, pseudo := true } := by decide

theorem rule4b_one_reference_over_two_is_reachable_and_conformant :
    occurrenceRule4bReferences molecule oneReferenceVersusTwoState 2 [root 1] = [.R] ∧
    occurrenceRule4bReferences molecule oneReferenceVersusTwoState 2 [root 7] = [.R, .S] ∧
    compareOccurrenceRule4b? molecule oneReferenceVersusTwoState 2 (root 1) (root 7) =
      some (BlueBookP92.rule4bReferenceCountDecision .one .two) := by
  have leftReferences :
      occurrenceRule4bReferences molecule oneReferenceVersusTwoState 2 [root 1] = [.R] := by
    decide
  have rightReferences :
      occurrenceRule4bReferences molecule oneReferenceVersusTwoState 2 [root 7] = [.R, .S] := by
    decide
  exact ⟨leftReferences, rightReferences,
    compareOccurrenceRule4b?_one_reference_over_two molecule oneReferenceVersusTwoState 2
      (root 1) (root 7) .R .R .S leftReferences rightReferences⟩

theorem descriptor_branching_two_success_endpoint :
    ∃ endpoint,
      compareOccurrenceBranches? molecule state 1 (root 1) (root 7) = some endpoint ∧
        endpoint.ordering = Ordering.lt := by
  exact frame.endpoint_of_two_success
    (left := root 1) (middle := root 4) (right := root 7)
    (leftMiddle := { ordering := .eq })
    (middleRight := { ordering := .lt, pseudo := true })
    (composed := .lt)
    (by simp [roots]) (by simp [roots]) (by simp [roots])
    (by decide) (by decide) (by decide)

end TetraStereo.Examples.DescriptorBranchingCIPFrameRegression
