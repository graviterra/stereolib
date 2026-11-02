/-
  ParentRule1aSeparationDiagnostic

  Structural diagnostic for a supplied cut of a finite single-bonded graph.
  The two branch keys are computed by the actual buildOfficialRuleMajorKey compiler,
  using the node-level child function rerootCutChildren defined in this module.
  The keys tie under Rule 1a and are separated by the implemented total-distance
  Hanson 2018 proposed Rule 1b observation.

  The graph has 17 vertices. C2 and C3 each carry Cl, H and CH3 besides their shared
  neighbor C0. C0 has TWO hydrogen neighbors, so it is not an auxiliary tetrahedral
  stereocenter. The supplied cut is not connected here by a proof to a certified
  occurrence carrier or to the SMILES reroot pipeline. This fixture consequently
  does not refute Hanson's statement about eligible auxiliary centers, establish
  BB2013 correspondence, or demonstrate a changed molecular descriptor.

  The Rule-1a-only auxiliary-center statement is in the Hanson 2018 preprint.
  BB2013 Rule 1b explicitly concerns duplicate atom nodes; this fixture has only
  real nodes. Its total-distance separation therefore establishes an observation
  of the implemented profile, without supplying a BB2013 justification for it.
  All theorem statements below concern only the concrete supplied-cut computation.
-/

import TetraStereo.OneCenter.OfficialRuleMajorKey
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo
namespace OneCenter
namespace ParentRule1aSeparationDiagnostic

/-- Atom type: seventeen named vertices, indexed `0 .. 16`. -/
abbrev Atom := Fin 17

/-- Original final center C2: Cl, H, CH3, and the middle carbon C0. -/
def center : Atom := 0

/-- Middle carbon C0, the reroot target. -/
def middle : Atom := 1

/-- Outward carbon C3, constitutionally identical to C2 (Cl, H, CH3). -/
def outward : Atom := 2

/-- Unordered skeleton bonds, all single.  C2 (0) is bonded to C0 (1), Cl (3), H (4), and the
methyl carbon 5; methyl 5 to 6/7/8; C0 (1) to C3 (2) and H 15/16; C3 (2) to Cl 9, H 10, methyl 11;
methyl 11 to 12/13/14. -/
def canonicalBonds : List (Atom × Atom) :=
  [ (0, 1), (0, 3), (0, 4), (0, 5), (5, 6), (5, 7), (5, 8)
  , (1, 2), (1, 15), (1, 16), (2, 9), (2, 10), (2, 11)
  , (11, 12), (11, 13), (11, 14) ]

/-- Bond order: `1` exactly on the canonical single bonds, `0` otherwise. -/
def bond (u v : Atom) : ℕ :=
  if canonicalBonds.contains (u, v) || canonicalBonds.contains (v, u) then 1 else 0

/-- Atomic numbers: carbons 0,1,2,5,11; chlorines 3,9; hydrogen elsewhere. -/
def atomZ (a : Atom) : ℕ :=
  if a = 3 ∨ a = 9 then 17
  else if a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 5 ∨ a = 11 then 6
  else 1

/-- The concrete finite molecular graph.  All masses and charges are zero, so Rule 2 never fires. -/
def molecule : MoleculeGraph Atom where
  atomZ := atomZ
  atomMass := fun _ => 0
  bond := bond
  bond_symm := by decide
  bond_self := by decide

/-- Node-level transcription of the implemented reroot cut.

For this single-bonded acyclic fixture every graph child is a zero-copy `extend`, so the official
children of a real node are its neighbors minus its parent (that is `MoleculeGraph.officialCIPChildren`).
The reroot cursor additionally cuts the *previous* coordinate, which is `middle` for both cursors
under test:

* parent arm  — root C2 with previous C0: C0 is an outward child of C2, removed here;
* outward arm — root C3 with previous C0: C0 is C3's parent, already excluded as the parent frame.

The filter therefore removes `middle` (and the parent frame) from the finitely enumerated neighbors. -/
def rerootCutChildren (node : OfficialCIPNode Atom) : List (OfficialCIPNode Atom) :=
  if node.isDuplicateLeaf then
    []
  else
    match node.current? with
    | none => []
    | some current =>
        ((List.finRange 17).filter (fun n =>
          decide (0 < bond current n) && !decide (node.parent? = some n) && !decide (n = middle))).map
          (fun n => node.extend n 0)

/-- The parent arm root: C2, rooted at the original final center (Rule-1b distance 0). -/
def parentArmRoot : OfficialCIPNode Atom :=
  OfficialCIPNode.root center

/-- The C0 occurrence on the C2-rooted carrier. -/
def middleNode : OfficialCIPNode Atom :=
  (OfficialCIPNode.root center).extend middle 0

/-- The outward arm root: C3 reached through C0 (Rule-1b distance 2). -/
def outwardArmRoot : OfficialCIPNode Atom :=
  middleNode.extend outward 0

def clOnC2 : OfficialCIPNode Atom := parentArmRoot.extend 3 0
def hOnC2 : OfficialCIPNode Atom := parentArmRoot.extend 4 0
def meOnC2 : OfficialCIPNode Atom := parentArmRoot.extend 5 0
def h6 : OfficialCIPNode Atom := meOnC2.extend 6 0
def h7 : OfficialCIPNode Atom := meOnC2.extend 7 0
def h8 : OfficialCIPNode Atom := meOnC2.extend 8 0

def clOnC3 : OfficialCIPNode Atom := outwardArmRoot.extend 9 0
def hOnC3 : OfficialCIPNode Atom := outwardArmRoot.extend 10 0
def meOnC3 : OfficialCIPNode Atom := outwardArmRoot.extend 11 0
def h12 : OfficialCIPNode Atom := meOnC3.extend 12 0
def h13 : OfficialCIPNode Atom := meOnC3.extend 13 0
def h14 : OfficialCIPNode Atom := meOnC3.extend 14 0

/-- Every node the two branches actually generate. -/
def branchNodes : List (OfficialCIPNode Atom) :=
  [parentArmRoot, clOnC2, hOnC2, meOnC2, h6, h7, h8,
   outwardArmRoot, clOnC3, hOnC3, meOnC3, h12, h13, h14]

/-- Fuel far beyond the branch depth (≤ 4), so both keys compile completely. -/
def fuel : ℕ := 18

/-- Parent-arm key built by the real rule-major compiler over the reroot-cut enumeration. -/
def parentKey : Option (OfficialRuleMajorKey Atom) :=
  molecule.buildOfficialRuleMajorKey rerootCutChildren fuel parentArmRoot

/-- Outward-arm key built by the real rule-major compiler over the reroot-cut enumeration. -/
def outwardKey : Option (OfficialRuleMajorKey Atom) :=
  molecule.buildOfficialRuleMajorKey rerootCutChildren fuel outwardArmRoot

theorem parentKey_isSome : parentKey.isSome = true := by
  decide

theorem outwardKey_isSome : outwardKey.isSome = true := by
  decide

/-- The extracted parent-arm key. -/
def parentArmKey : OfficialRuleMajorKey Atom :=
  parentKey.get parentKey_isSome

/-- The extracted outward-arm key. -/
def outwardArmKey : OfficialRuleMajorKey Atom :=
  outwardKey.get outwardKey_isSome

/-! ## The fixture is duplicate-free and single-bonded -/

/-- Every positive bond is a single bond, so no multiple-bond duplicate nodes arise. -/
theorem simpleBonded : molecule.SimpleBonded := by
  -- `SimpleBonded` is an opaque `def`, so typeclass search cannot synthesize
  -- `Decidable molecule.SimpleBonded` directly.  Unfold to the finite `∀`/`→` form, whose
  -- `Decidable` instance is found by `Fintype` enumeration, then evaluate it.
  unfold MoleculeGraph.SimpleBonded MoleculeGraph.Adj
  decide

/-- Every node actually generated on either branch is a real atom: there are no duplicate or
placeholder nodes, so the 2013 duplicate-only Rule 1b has no node to act on in this scenario. -/
theorem all_branch_nodes_realAtom :
    ∀ node ∈ branchNodes,
      node.provenance = OfficialCIPNodeProvenance.realAtom := by
  have hall : branchNodes.all
      (fun node => decide (node.provenance = OfficialCIPNodeProvenance.realAtom)) = true := by
    decide
  intro node hnode
  exact of_decide_eq_true ((List.all_eq_true.mp hall) node hnode)

/-! ## The reroot cut is realized on the actual builders -/

/-- The reroot cut drops the previous coordinate C0 from the parent arm: its children are exactly
Cl (3), H (4), and the methyl carbon (5). -/
theorem parentArm_children :
    (rerootCutChildren parentArmRoot).map (fun n => n.current?) =
      [some (3 : Atom), some (4 : Atom), some (5 : Atom)] := by
  decide

/-- The outward arm has the constitutionally identical children Cl (9), H (10), methyl carbon (11). -/
theorem outwardArm_children :
    (rerootCutChildren outwardArmRoot).map (fun n => n.current?) =
      [some (9 : Atom), some (10 : Atom), some (11 : Atom)] := by
  decide

/-- The two branch roots carry the same stored history shapes under the original C2 rooting:
`[C2]` versus `[C3, C0, C2]`. -/
theorem parentArmRoot_history : parentArmRoot.history = [center] := rfl

theorem outwardArmRoot_history : outwardArmRoot.history = [outward, middle, center] := rfl

/-- Total Rule-1b observations of the two branch roots: the parent arm is the original root
(sphere 0) and the outward arm is at sphere 2. -/
theorem parentArmRoot_rule1bDistance :
    parentArmRoot.rule1bRootDistance = 0 := by
  decide

theorem outwardArmRoot_rule1bDistance :
    outwardArmRoot.rule1bRootDistance = 2 := by
  decide

/-! ## Rule 1a ties; Rule 1b separates -/

/-- Both compiled keys are complete. -/
theorem parentArmKey_complete : parentArmKey.complete = true := by
  decide

theorem outwardArmKey_complete : outwardArmKey.complete = true := by
  decide

/-- Both branch roots retain the same Rule-1a root observation: atomic number 6. -/
theorem parentRoot_rule1a_head : parentArmKey.rule1a.head? = some [([], 6)] := by
  decide

theorem outwardRoot_rule1a_head : outwardArmKey.rule1a.head? = some [([], 6)] := by
  decide

/-- The Rule-1b root observations are the stored root distances 0 and 2. -/
theorem parentRoot_rule1b_head : parentArmKey.rule1b.head? = some [([], 0)] := by
  decide

theorem outwardRoot_rule1b_head : outwardArmKey.rule1b.head? = some [([], 2)] := by
  decide

/-- **Rule 1a ties**: the two compiled Rule-1a projections are literally equal.  Atomic-number
comparison alone cannot separate the root-facing ligand from the outward arm. -/
theorem rule1a_projections_equal : parentArmKey.rule1a = outwardArmKey.rule1a := by
  decide

theorem rule1a_ties :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      parentArmKey.rule1a outwardArmKey.rule1a = Ordering.eq := by
  decide

/-- **Rule 1b separates**: the nearer stored root distance wins, ranking the parent arm higher. -/
theorem rule1b_separates :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b
      parentArmKey.rule1b outwardArmKey.rule1b = Ordering.gt := by
  decide

/-- The total rule-major comparator ranks the parent arm over the outward arm. -/
theorem full_compare_parent_wins :
    OfficialRuleMajorKey.compare parentArmKey outwardArmKey = Ordering.gt := by
  decide

/-- The safe comparator (which requires completeness) returns the same decision. -/
theorem safe_compare_parent_wins :
    OfficialRuleMajorKey.compare? parentArmKey outwardArmKey = some Ordering.gt := by
  decide

/-- The rule-tagged trace is Rule 1a tie, Rule 1b `gt`, Rule 2 tie. -/
theorem trace_outcome_parent_wins :
    cipTraceOutcome (OfficialRuleMajorKey.compareTrace parentArmKey outwardArmKey) = Ordering.gt := by
  decide

/-- The supplied-cut computation ties under Rule 1a and ranks the parent arm above the
outward arm under the implemented total Rule 1b (distances 0 and 2). The middle atom has two
hydrogens, so this statement makes no claim about eligible auxiliary stereocenters. -/
theorem rule1a_does_not_separate_parent_arm :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        parentArmKey.rule1a outwardArmKey.rule1a = Ordering.eq ∧
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b
        parentArmKey.rule1b outwardArmKey.rule1b = Ordering.gt ∧
      OfficialRuleMajorKey.compare parentArmKey outwardArmKey = Ordering.gt := by
  decide

end ParentRule1aSeparationDiagnostic
end OneCenter
end TetraStereo

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.ParentRule1aSeparationDiagnostic.simpleBonded
assert_kernel_only TetraStereo.OneCenter.ParentRule1aSeparationDiagnostic.all_branch_nodes_realAtom
assert_kernel_only TetraStereo.OneCenter.ParentRule1aSeparationDiagnostic.parentArm_children
assert_kernel_only TetraStereo.OneCenter.ParentRule1aSeparationDiagnostic.outwardArm_children
assert_kernel_only TetraStereo.OneCenter.ParentRule1aSeparationDiagnostic.parentArmRoot_history
assert_kernel_only TetraStereo.OneCenter.ParentRule1aSeparationDiagnostic.outwardArmRoot_history
assert_kernel_only TetraStereo.OneCenter.ParentRule1aSeparationDiagnostic.parentArmRoot_rule1bDistance
assert_kernel_only TetraStereo.OneCenter.ParentRule1aSeparationDiagnostic.outwardArmRoot_rule1bDistance
assert_kernel_only TetraStereo.OneCenter.ParentRule1aSeparationDiagnostic.parentKey_isSome
assert_kernel_only TetraStereo.OneCenter.ParentRule1aSeparationDiagnostic.outwardKey_isSome
assert_kernel_only TetraStereo.OneCenter.ParentRule1aSeparationDiagnostic.parentArmKey_complete
assert_kernel_only TetraStereo.OneCenter.ParentRule1aSeparationDiagnostic.outwardArmKey_complete
assert_kernel_only TetraStereo.OneCenter.ParentRule1aSeparationDiagnostic.parentRoot_rule1a_head
assert_kernel_only TetraStereo.OneCenter.ParentRule1aSeparationDiagnostic.outwardRoot_rule1a_head
assert_kernel_only TetraStereo.OneCenter.ParentRule1aSeparationDiagnostic.parentRoot_rule1b_head
assert_kernel_only TetraStereo.OneCenter.ParentRule1aSeparationDiagnostic.outwardRoot_rule1b_head
assert_kernel_only TetraStereo.OneCenter.ParentRule1aSeparationDiagnostic.rule1a_projections_equal
assert_kernel_only TetraStereo.OneCenter.ParentRule1aSeparationDiagnostic.rule1a_ties
assert_kernel_only TetraStereo.OneCenter.ParentRule1aSeparationDiagnostic.rule1b_separates
assert_kernel_only TetraStereo.OneCenter.ParentRule1aSeparationDiagnostic.full_compare_parent_wins
assert_kernel_only TetraStereo.OneCenter.ParentRule1aSeparationDiagnostic.safe_compare_parent_wins
assert_kernel_only TetraStereo.OneCenter.ParentRule1aSeparationDiagnostic.trace_outcome_parent_wins
assert_kernel_only TetraStereo.OneCenter.ParentRule1aSeparationDiagnostic.rule1a_does_not_separate_parent_arm
