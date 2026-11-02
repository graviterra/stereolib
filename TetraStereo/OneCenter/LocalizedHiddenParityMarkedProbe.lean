import TetraStereo.OneCenter.DeclarativeCIPOccurrenceRules456
import TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCompletion
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 0

/-!
An executable probe of the accepted 15-atom cage in the existing RawMolecule Rule-6 runtime.
The RawMolecule below is a finite adapter of the accepted localized graph.  Its auxiliary
occurrence state is explicitly empty; no theorem here identifies it with the localized evaluator's
generated state.
-/

namespace TetraStereo.OneCenter.LocalizedHiddenParityMarkedProbe

open TetraStereo.OneCenter
open TetraStereo.OneCenter.DeclarativeCIP
open TetraStereo.OneCenter.DeclarativeCIP.ProductionOccurrenceRules456
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCompletion

private def atom (element : Element) : AtomSpec := AtomSpec.aliphatic element
private def bond (source target : Nat) : RawBond :=
  { source := source, target := target, kind := .single }

/-- Atom order is exactly the accepted cage order 0 through 14. -/
def cageRaw : RawMolecule :=
  { atoms := [.C, .H, .Cl, .C, .H, .O, .O, .O, .C, .C, .H, .O, .O, .O, .C].map atom
    bonds := [bond 0 1, bond 0 2, bond 0 3, bond 0 9,
      bond 3 5, bond 3 6, bond 3 7, bond 4 8, bond 5 8, bond 6 8, bond 7 8,
      bond 9 11, bond 9 12, bond 9 13, bond 10 14, bond 11 14, bond 12 14,
      bond 13 14]
    neighborOrder := [[1, 2, 3, 9], [0], [0], [0, 5, 6, 7], [8], [3, 8], [3, 8], [3, 8],
      [4, 5, 6, 7], [0, 11, 12, 13], [14], [9, 14], [9, 14], [9, 14], [10, 11, 12, 13]] }

theorem cageRaw_atomCount : cageRaw.atomCount = 15 := rfl

theorem cageRaw_atomLabels_match_literal :
    cageRaw.atoms.map AtomSpec.element =
      [.C, .H, .Cl, .C, .H, .O, .O, .O, .C, .C, .H, .O, .O, .O, .C] := by
  decide +kernel

theorem cageRaw_edges_match_literal :
    cageRaw.bonds.map RawBond.edgeKey =
      [(0, 1), (0, 2), (0, 3), (0, 9), (3, 5), (3, 6), (3, 7), (4, 8), (5, 8), (6, 8),
       (7, 8), (9, 11), (9, 12), (9, 13), (10, 14), (11, 14), (12, 14), (13, 14)] := by
  decide +kernel

private abbrev acceptedGraph :=
  TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCompletion.graph

/-- Finite, kernel-checked atom-number correspondence to the accepted localized graph. -/
theorem cageRaw_atomNumbers_match_accepted :
    ∀ i : Fin 15,
      (cageRaw.atomAt? i.val).map (fun spec => spec.element.atomicNumber) =
        some (acceptedGraph.atomZ i) := by
  intro i
  fin_cases i <;> decide +kernel

/-- The adapter and accepted graph both retain zero formal charge at every atom. -/
theorem cageRaw_charges_match_accepted :
    ∀ i : Fin 15,
      (cageRaw.atomAt? i.val).map AtomSpec.charge = some (acceptedGraph.formalCharge i) := by
  intro i
  fin_cases i <;> decide +kernel

/-- The parser adapter's exact Rule-2 mass keys agree with the accepted graph's keys. -/
theorem cageRaw_isotopes_match_accepted :
    ∀ i : Fin 15,
      (cageRaw.atomAt? i.val).map
          (fun spec => RawMolecule.rule2MassPico? spec.element spec.isotope?) =
        some (some (acceptedGraph.atomMass i)) := by
  intro i
  fin_cases i <;> decide +kernel

/-- Every ordered pair has exactly the accepted bond order in the raw adapter. -/
theorem cageRaw_bondOrders_match_accepted :
    ∀ u v : Fin 15, cageRaw.bondOrder u.val v.val = acceptedGraph.bond u v := by
  intro u v
  fin_cases u <;> fin_cases v <;> decide +kernel

theorem accepted_interactions_are_single_bonds :
    cageSource.molecule.interactions.all
      (fun interaction => decide (interaction.kind = .covalent 1)) = true := by
  decide +kernel

def nearA : RawMolecule.CanonicalBranchNode :=
  { atom := 3, parent := 0, history := [3, 0], provenance := .realAtom }

def farA (o : Nat) : RawMolecule.CanonicalBranchNode :=
  { atom := 8, parent := o, history := [8, o, 3, 0], provenance := .realAtom }

def root0 : RawMolecule.CanonicalBranchNode :=
  { atom := 0, parent := 0, history := [0], provenance := .realAtom }

def nearBridgeOxygen (o : Nat) : RawMolecule.CanonicalBranchNode :=
  { atom := o, parent := 3, history := [o, 3, 0], provenance := .realAtom }

theorem nearA_is_canonical_child_of_root0 : nearA ∈ cageRaw.canonicalChildren root0 := by
  decide +kernel

theorem bridgeOxygen_is_canonical_child (o : Nat) (h : o ∈ [5, 6, 7]) :
    nearBridgeOxygen o ∈ cageRaw.canonicalChildren nearA := by
  have ho : o = 5 ∨ o = 6 ∨ o = 7 := by simpa using h
  rcases ho with ho | ho | ho
  · subst o
    decide +kernel
  · subst o
    decide +kernel
  · subst o
    decide +kernel

theorem farA_is_canonical_child_of_bridgeOxygen (o : Nat) (h : o ∈ [5, 6, 7]) :
    farA o ∈ cageRaw.canonicalChildren (nearBridgeOxygen o) := by
  have ho : o = 5 ∨ o = 6 ∨ o = 7 := by simpa using h
  rcases ho with ho | ho | ho
  · subst o
    decide +kernel
  · subst o
    decide +kernel
  · subst o
    decide +kernel

def emptyOrdinaryAux : OccurrenceAuxState := []

def frame? (node : RawMolecule.CanonicalBranchNode) : Option (List CanonicalRerootCursor) :=
  occurrenceLigandFrame? cageRaw node

def tracked? (node : RawMolecule.CanonicalBranchNode) (mark : Nat) : Option Rule6TrackedRanking := do
  let roots ← frame? node
  let ligands := roots.map fun cursor => cursor.node.atom
  let referencePosition := ligands.idxOf mark
  if referencePosition >= ligands.length then none else
    rankOccurrencePositionsThroughRule6Tracked? (mol := cageRaw) emptyOrdinaryAux
      16 roots ligands [0, 1, 2, 3] referencePosition

def frameAtoms? (node : RawMolecule.CanonicalBranchNode) : Option (List Nat) :=
  (frame? node).map fun roots => roots.map fun cursor => cursor.node.atom

theorem nearA_frameAtoms : frameAtoms? nearA = some [0, 5, 6, 7] := by
  decide +kernel

theorem farA5_frameAtoms : frameAtoms? (farA 5) = some [5, 4, 6, 7] := by
  decide +kernel

theorem farA6_frameAtoms : frameAtoms? (farA 6) = some [6, 4, 5, 7] := by
  decide +kernel

theorem farA7_frameAtoms : frameAtoms? (farA 7) = some [7, 4, 5, 6] := by
  decide +kernel

/-- Kernel-reduced output of the actual tracked call at the near occurrence. -/
theorem near_mark5_tracked_output : tracked? nearA 5 =
    some { positions := [1, 2, 3, 0], unique := false, pseudoComparisons := 1 } := by
  decide +kernel

/-- The diagonal far visit retains the unmarked-branch tie. -/
theorem far_o5_mark5_tracked_output : tracked? (farA 5) 5 =
    some { positions := [0, 2, 3, 1], unique := false, pseudoComparisons := 0 } := by
  decide +kernel

/-- An off-diagonal mark yields a strict actual ranking at the far visit. -/
theorem far_o5_mark6_tracked_output : tracked? (farA 5) 6 =
    some { positions := [0, 2, 3, 1], unique := true, pseudoComparisons := 1 } := by
  decide +kernel

/-! These are the literal runtime observations.  They are intentionally kept as `#eval` evidence
until the outputs are small enough to pin with kernel-reduction lemmas. -/
#print axioms occurrenceLigandFrame?
#print axioms compareOccurrenceBranchesThroughRule6At?
#print axioms rankOccurrencePositionsThroughRule6Tracked?
#print axioms frame?
#print axioms tracked?

#eval frame? nearA
#eval frame? (farA 5)
#eval frame? (farA 6)
#eval frame? (farA 7)
#eval tracked? nearA 5
#eval tracked? (farA 5) 5
#eval tracked? (farA 5) 6
#eval tracked? (farA 5) 7
#eval tracked? (farA 6) 5
#eval tracked? (farA 6) 6
#eval tracked? (farA 6) 7
#eval tracked? (farA 7) 5
#eval tracked? (farA 7) 6
#eval tracked? (farA 7) 7

end TetraStereo.OneCenter.LocalizedHiddenParityMarkedProbe

assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityMarkedProbe.cageRaw_atomNumbers_match_accepted
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityMarkedProbe.cageRaw_charges_match_accepted
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityMarkedProbe.cageRaw_isotopes_match_accepted
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityMarkedProbe.cageRaw_bondOrders_match_accepted
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityMarkedProbe.accepted_interactions_are_single_bonds
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityMarkedProbe.nearA_is_canonical_child_of_root0
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityMarkedProbe.bridgeOxygen_is_canonical_child
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityMarkedProbe.farA_is_canonical_child_of_bridgeOxygen
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityMarkedProbe.nearA_frameAtoms
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityMarkedProbe.farA5_frameAtoms
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityMarkedProbe.farA6_frameAtoms
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityMarkedProbe.farA7_frameAtoms
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityMarkedProbe.near_mark5_tracked_output
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityMarkedProbe.far_o5_mark5_tracked_output
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityMarkedProbe.far_o5_mark6_tracked_output
