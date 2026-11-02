import TetraStereo.OneCenter.ChemistrySemantics
import TetraStereo.OneCenter.OpenSMILESIntroductionAppend
import TetraStereo.OneCenter.OpenSMILESSyntaxContinuation

set_option autoImplicit false

namespace TetraStereo.UniversalProof.GeneralParserStateBridge

open TetraStereo.OneCenter









inductive FamilyAtom where
  | hydrogen
  | carbon
  | taggedCarbon (parity : TetrahedralInputParity)
  | fluorine
  | bromine
  deriving DecidableEq, Repr

def atomSpec : FamilyAtom → AtomSpec
  | .hydrogen => { element := .H, explicitHydrogens? := some 0 }
  | .carbon => { element := .C, explicitHydrogens? := some 0 }
  | .taggedCarbon parity =>
      { element := .C, explicitHydrogens? := some 0, tetrahedral? := some parity }
  | .fluorine => { element := .F, explicitHydrogens? := some 0 }
  | .bromine => { element := .Br, explicitHydrogens? := some 0 }

def atomChars : FamilyAtom → List Char
  | .hydrogen => ['[', 'H', ']']
  | .carbon => ['[', 'C', ']']
  | .taggedCarbon .anticlockwise => ['[', 'C', '@', ']']
  | .taggedCarbon .clockwise => ['[', 'C', '@', '@', ']']
  | .fluorine => ['[', 'F', ']']
  | .bromine => ['[', 'B', 'r', ']']

theorem family_atom_explicit_hydrogens_zero (kind : FamilyAtom) :
    (atomSpec kind).explicitHydrogens? = some 0 := by
  cases kind <;> rfl

theorem tagged_carbon_parity (parity : TetrahedralInputParity) :
    (atomSpec (.taggedCarbon parity)).tetrahedral? = some parity := rfl

/-- Actual bracket-token consumption, uniform in every remaining character stream. -/
theorem parse_family_atom_token (kind : FamilyAtom) (tail : List Char) :
    parseAtomToken? (atomChars kind ++ tail) = some (atomSpec kind, tail) := by
  cases kind with
  | hydrogen => rfl
  | carbon => rfl
  | taggedCarbon parity => cases parity <;> rfl
  | fluorine => rfl
  | bromine => rfl

/-- One actual parser recursion consumes one complete bracket token, not one character. -/
theorem parse_family_atom_step (kind : FamilyAtom) (fuel : ℕ)
    (tail : List Char) (state : ParseState) :
    parseCharsFuel (fuel + 1) (atomChars kind ++ tail) state =
      parseCharsFuel fuel tail (state.addAtom (atomSpec kind)) := by
  cases kind with
  | hydrogen => rfl
  | carbon => rfl
  | taggedCarbon parity => cases parity <;> rfl
  | fluorine => rfl
  | bromine => rfl

def pendingSingle (state : ParseState) : ParseState :=
  { state with pendingBond? := some .single }

/-- Independent explicit-single atom append and written-index update. There is no parser call,
ParseState.addAtom/addBond call, or successful-parse field in this construction. -/
def attachSingle (state : ParseState) (parent : ℕ) (atom : AtomSpec) : ParseState :=
  let index := state.atoms.length
  let appended := state.order ++ [[]]
  let parentUpdated := appended.set parent (appended.getD parent [] ++ [index])
  { state with
    atoms := state.atoms ++ [atom]
    bonds := state.bonds ++ [{ source := parent, target := index, kind := .single }]
    current? := some index
    pendingBond? := none
    order := parentUpdated.set index (parentUpdated.getD index [] ++ [parent])
    introductionPredecessors :=
      if state.introductionPredecessors.length = state.atoms.length then
        state.introductionPredecessors ++ [some parent]
      else state.introductionPredecessors }

/-- Actual core addAtom agrees with independently defined append/index records. -/
theorem addAtom_after_explicit_single (state : ParseState) (parent : ℕ) (atom : AtomSpec)
    (current : state.current? = some parent) :
    (pendingSingle state).addAtom atom = attachSingle state parent atom := by
  simp only [pendingSingle, ParseState.addAtom, ParseState.nextAtomId, current,
    ParseState.addBond, attachSingle, ParseState.noteOrder]


theorem parse_single_bond_step (fuel : ℕ) (tail : List Char) (state : ParseState) :
    parseCharsFuel (fuel + 1) ('-' :: tail) state =
      parseCharsFuel fuel tail (pendingSingle state) := rfl

/-- Derived actual two-token continuation, with no assumed parser return state. -/
theorem parse_single_family_atom_step (kind : FamilyAtom) (fuel : ℕ)
    (tail : List Char) (state : ParseState) (parent : ℕ)
    (current : state.current? = some parent) :
    parseCharsFuel (fuel + 2) ('-' :: (atomChars kind ++ tail)) state =
      parseCharsFuel fuel tail (attachSingle state parent (atomSpec kind)) := by
  change parseCharsFuel ((fuel + 1) + 1) ('-' :: (atomChars kind ++ tail)) state = _
  rw [parse_single_bond_step, parse_family_atom_step,
    addAtom_after_explicit_single state parent (atomSpec kind) current]

/-- General actual branch opening, uniform in continuation/fuel and older stack. -/
theorem parse_open_branch_step (fuel : ℕ) (tail : List Char) (state : ParseState)
    (parent : ℕ) (current : state.current? = some parent) :
    parseCharsFuel (fuel + 1) ('(' :: tail) state =
      parseCharsFuel fuel tail { state with branches := parent :: state.branches } := by
  simp only [parseCharsFuel, ParseState.pushBranch, current]
  all_goals rfl

/-- General actual branch closing; the required stack fact is raw state structure. -/
theorem parse_close_branch_step (fuel : ℕ) (tail : List Char) (state : ParseState)
    (parent : ℕ) (rest : List ℕ) (stack : state.branches = parent :: rest) :
    parseCharsFuel (fuel + 1) (')' :: tail) state =
      parseCharsFuel fuel tail { state with current? := some parent, branches := rest } := by
  simp only [parseCharsFuel, ParseState.popBranch, stack]
  all_goals rfl

/-- The independently appended branch atom is retained while current/stack restore to its parent. -/
def singleBranchResult (state : ParseState) (parent : ℕ) (atom : AtomSpec) : ParseState :=
  { attachSingle state parent atom with current? := some parent, branches := state.branches }

/-- Four actual tokens '( - bracketAtom )' are consumed for ANY continuation/fuel. The appended
atom, bond and written rows are explicit data, including an arbitrary input parity when tagged. -/
theorem parse_single_branch_continuation (kind : FamilyAtom) (fuel : ℕ)
    (tail : List Char) (state : ParseState) (parent : ℕ)
    (current : state.current? = some parent) :
    parseCharsFuel (fuel + 4) ('(' :: '-' :: (atomChars kind ++ ')' :: tail)) state =
      parseCharsFuel fuel tail (singleBranchResult state parent (atomSpec kind)) := by
  change parseCharsFuel (((fuel + 1) + 2) + 1)
    ('(' :: '-' :: (atomChars kind ++ ')' :: tail)) state = _
  rw [parse_open_branch_step _ _ state parent current]
  rw [parse_single_family_atom_step kind (fuel + 1) (')' :: tail)
    { state with branches := parent :: state.branches } parent current]
  rw [parse_close_branch_step _ _ _ parent state.branches rfl]
  all_goals rfl

/-- Append-state projections useful to independent closed-record prefix invariants. -/
theorem attachSingle_atoms (state : ParseState) (parent : ℕ) (atom : AtomSpec) :
    (attachSingle state parent atom).atoms = state.atoms ++ [atom] := rfl

theorem attachSingle_bonds (state : ParseState) (parent : ℕ) (atom : AtomSpec) :
    (attachSingle state parent atom).bonds =
      state.bonds ++ [{ source := parent, target := state.atoms.length, kind := .single }] := rfl

theorem attachSingle_current (state : ParseState) (parent : ℕ) (atom : AtomSpec) :
    (attachSingle state parent atom).current? = some state.atoms.length := rfl

theorem singleBranchResult_current (state : ParseState) (parent : ℕ) (atom : AtomSpec) :
    (singleBranchResult state parent atom).current? = some parent := rfl

/-- Explicit-single tokens and one-atom branch tokens, separated from parser state data. -/
def singleChars (kind : FamilyAtom) : List Char := '-' :: atomChars kind

def branchChars (kind : FamilyAtom) : List Char :=
  '(' :: '-' :: (atomChars kind ++ [')'])

theorem parse_single_chars_step (kind : FamilyAtom) (fuel : ℕ)
    (tail : List Char) (state : ParseState) (parent : ℕ)
    (current : state.current? = some parent) :
    parseCharsFuel (fuel + 2) (singleChars kind ++ tail) state =
      parseCharsFuel fuel tail (attachSingle state parent (atomSpec kind)) := by
  simpa only [singleChars, List.cons_append] using
    parse_single_family_atom_step kind fuel tail state parent current

theorem parse_branch_chars_step (kind : FamilyAtom) (fuel : ℕ)
    (tail : List Char) (state : ParseState) (parent : ℕ)
    (current : state.current? = some parent) :
    parseCharsFuel (fuel + 4) (branchChars kind ++ tail) state =
      parseCharsFuel fuel tail (singleBranchResult state parent (atomSpec kind)) := by
  simpa only [branchChars, List.cons_append, List.append_assoc, List.nil_append] using
    parse_single_branch_continuation kind fuel tail state parent current

/-- A tagged C(H,F,Br) branch has fourteen parser tokens, independently of '@' versus '@@'. -/
def pendantChars (parity : TetrahedralInputParity) : List Char :=
  '(' :: (singleChars (.taggedCarbon parity) ++ branchChars .hydrogen ++
    branchChars .fluorine ++ singleChars .bromine ++ [')'])

/-- Independent atom/bond/written-index records for the whole pendant branch. Every append
uses raw record updates; this definition contains no parser, addAtom, or addBond call. -/
def pendantBranchResult (state : ParseState) (parent : ℕ)
    (parity : TetrahedralInputParity) : ParseState :=
  let opened := { state with branches := parent :: state.branches }
  let tagIndex := state.atoms.length
  let tagged := attachSingle opened parent (atomSpec (.taggedCarbon parity))
  let hydrogen := singleBranchResult tagged tagIndex (atomSpec .hydrogen)
  let fluorine := singleBranchResult hydrogen tagIndex (atomSpec .fluorine)
  let bromine := attachSingle fluorine tagIndex (atomSpec .bromine)
  { bromine with current? := some parent, branches := state.branches }

theorem parse_pendant_branch_continuation (parity : TetrahedralInputParity)
    (fuel : ℕ) (tail : List Char) (state : ParseState) (parent : ℕ)
    (current : state.current? = some parent) :
    parseCharsFuel (fuel + 14) (pendantChars parity ++ tail) state =
      parseCharsFuel fuel tail (pendantBranchResult state parent parity) := by
  let opened : ParseState := { state with branches := parent :: state.branches }
  let tagIndex := state.atoms.length
  let tagged := attachSingle opened parent (atomSpec (.taggedCarbon parity))
  let hydrogen := singleBranchResult tagged tagIndex (atomSpec .hydrogen)
  let fluorine := singleBranchResult hydrogen tagIndex (atomSpec .fluorine)
  let bromine := attachSingle fluorine tagIndex (atomSpec .bromine)
  simp only [pendantChars, List.cons_append, List.append_assoc, List.nil_append]
  rw [parse_open_branch_step (fuel + 13) _ state parent current]
  change parseCharsFuel ((fuel + 11) + 2)
    (singleChars (.taggedCarbon parity) ++ _) opened = _
  rw [parse_single_chars_step (.taggedCarbon parity) (fuel + 11) _ opened parent current]
  change parseCharsFuel ((fuel + 7) + 4) (branchChars .hydrogen ++ _) tagged = _
  rw [parse_branch_chars_step .hydrogen (fuel + 7) _ tagged tagIndex rfl]
  change parseCharsFuel ((fuel + 3) + 4) (branchChars .fluorine ++ _) hydrogen = _
  rw [parse_branch_chars_step .fluorine (fuel + 3) _ hydrogen tagIndex rfl]
  change parseCharsFuel ((fuel + 1) + 2) (singleChars .bromine ++ _) fluorine = _
  rw [parse_single_chars_step .bromine (fuel + 1) _ fluorine tagIndex rfl]
  change parseCharsFuel (fuel + 1) (')' :: tail) bromine = _
  rw [parse_close_branch_step fuel tail bromine parent state.branches rfl]
  all_goals rfl

theorem pendantBranchResult_current (state : ParseState) (parent : ℕ)
    (parity : TetrahedralInputParity) :
    (pendantBranchResult state parent parity).current? = some parent := rfl

theorem pendantBranchResult_branches (state : ParseState) (parent : ℕ)
    (parity : TetrahedralInputParity) :
    (pendantBranchResult state parent parity).branches = state.branches := rfl

/-- One backbone C(-H)(-C@/@@(-H)(-F)-Br) block: twenty actual parser tokens. -/
def blockChars (parity : TetrahedralInputParity) : List Char :=
  singleChars .carbon ++ branchChars .hydrogen ++ pendantChars parity

def blockResult (state : ParseState) (parent : ℕ)
    (parity : TetrahedralInputParity) : ParseState :=
  let backbone := attachSingle state parent (atomSpec .carbon)
  let hydrogen := singleBranchResult backbone state.atoms.length (atomSpec .hydrogen)
  pendantBranchResult hydrogen state.atoms.length parity

/-- General reusable block transition for ANY prefix, continuation, old branch stack, fuel
and input parity. The only hypothesis says which already constructed atom is current. -/
theorem parse_block_continuation (parity : TetrahedralInputParity)
    (fuel : ℕ) (tail : List Char) (state : ParseState) (parent : ℕ)
    (current : state.current? = some parent) :
    parseCharsFuel (fuel + 20) (blockChars parity ++ tail) state =
      parseCharsFuel fuel tail (blockResult state parent parity) := by
  let backbone := attachSingle state parent (atomSpec .carbon)
  let hydrogen := singleBranchResult backbone state.atoms.length (atomSpec .hydrogen)
  simp only [blockChars, List.append_assoc]
  change parseCharsFuel ((fuel + 18) + 2) (singleChars .carbon ++ _) state = _
  rw [parse_single_chars_step .carbon (fuel + 18) _ state parent current]
  change parseCharsFuel ((fuel + 14) + 4) (branchChars .hydrogen ++ _) backbone = _
  rw [parse_branch_chars_step .hydrogen (fuel + 14) _ backbone state.atoms.length rfl]
  change parseCharsFuel (fuel + 14) (pendantChars parity ++ tail) hydrogen = _
  rw [parse_pendant_branch_continuation parity fuel tail hydrogen state.atoms.length rfl]
  all_goals rfl

theorem blockResult_current (state : ParseState) (parent : ℕ)
    (parity : TetrahedralInputParity) :
    (blockResult state parent parity).current? = some state.atoms.length := rfl

theorem blockResult_branches (state : ParseState) (parent : ℕ)
    (parity : TetrahedralInputParity) :
    (blockResult state parent parity).branches = state.branches := rfl

theorem blockResult_atom_count (state : ParseState) (parent : ℕ)
    (parity : TetrahedralInputParity) :
    (blockResult state parent parity).atoms.length = state.atoms.length + 6 := by
  simp only [blockResult, pendantBranchResult, singleBranchResult, attachSingle,
    List.length_append, List.length_singleton]

theorem blockResult_bond_count (state : ParseState) (parent : ℕ)
    (parity : TetrahedralInputParity) :
    (blockResult state parent parity).bonds.length = state.bonds.length + 6 := by
  simp only [blockResult, pendantBranchResult, singleBranchResult, attachSingle,
    List.length_append, List.length_singleton]

/-- An arbitrary list supplies every pendant's actual input parity independently. -/
def blocksChars : List TetrahedralInputParity → List Char
  | [] => []
  | parity :: rest => blockChars parity ++ blocksChars rest

/-- Independent chronological raw append construction. There are no parser calls in this
prefix state: each next backbone index is the old physical atom-list length. -/
def blocksResult : List TetrahedralInputParity → ParseState → ℕ → ParseState
  | [], state, _ => state
  | parity :: rest, state, parent =>
      blocksResult rest (blockResult state parent parity) state.atoms.length

/-- Actual arbitrary-size parser continuation, derived by induction over independent parity
data. It accepts no successful parse, output-state equality, or desired annotation premise. -/
theorem parse_blocks_continuation (parities : List TetrahedralInputParity)
    (fuel : ℕ) (tail : List Char) (state : ParseState) (parent : ℕ)
    (current : state.current? = some parent) :
    parseCharsFuel (fuel + 20 * parities.length) (blocksChars parities ++ tail) state =
      parseCharsFuel fuel tail (blocksResult parities state parent) := by
  induction parities generalizing fuel state parent with
  | nil => rfl
  | cons parity rest ih =>
      have budget : fuel + 20 * (rest.length + 1) = (fuel + 20 * rest.length) + 20 := by
        omega
      simp only [blocksChars, blocksResult, List.length_cons, List.append_assoc]
      rw [budget, parse_block_continuation parity (fuel + 20 * rest.length)
        (blocksChars rest ++ tail) state parent current]
      exact ih fuel (blockResult state parent parity) state.atoms.length rfl

theorem blocksResult_atom_count (parities : List TetrahedralInputParity)
    (state : ParseState) (parent : ℕ) :
    (blocksResult parities state parent).atoms.length =
      state.atoms.length + 6 * parities.length := by
  induction parities generalizing state parent with
  | nil => rfl
  | cons parity rest ih =>
      rw [blocksResult, ih, blockResult_atom_count]
      change state.atoms.length + 6 + 6 * rest.length =
        state.atoms.length + 6 * (rest.length + 1)
      omega

theorem blocksResult_bond_count (parities : List TetrahedralInputParity)
    (state : ParseState) (parent : ℕ) :
    (blocksResult parities state parent).bonds.length =
      state.bonds.length + 6 * parities.length := by
  induction parities generalizing state parent with
  | nil => rfl
  | cons parity rest ih =>
      rw [blocksResult, ih, blockResult_bond_count]
      change state.bonds.length + 6 + 6 * rest.length =
        state.bonds.length + 6 * (rest.length + 1)
      omega

theorem blocksResult_branches (parities : List TetrahedralInputParity)
    (state : ParseState) (parent : ℕ) :
    (blocksResult parities state parent).branches = state.branches := by
  induction parities generalizing state parent with
  | nil => rfl
  | cons parity rest ih =>
      rw [blocksResult, ih, blockResult_branches]

/-- Chronological edges always point from an older atom to a distinct fresh child. Unique child
indices suffice for unordered edge uniqueness; no pairwise bond-segment case split is needed. -/
structure ChronologicalRecords (atoms : List AtomSpec) (bonds : List RawBond) : Prop where
  forward : ∀ bond, bond ∈ bonds → bond.source < bond.target
  bounded : ∀ bond, bond ∈ bonds → bond.target < atoms.length
  targets : (bonds.map RawBond.target).Nodup

abbrev Chronological (state : ParseState) : Prop :=
  ChronologicalRecords state.atoms state.bonds

theorem chronological_admissible (state : ParseState) (physical : Chronological state) :
    state.molecule.Admissible := by
  constructor
  · intro bond membership
    have forward := physical.forward bond membership
    have bounded := physical.bounded bond membership
    change bond.source < state.atoms.length ∧ bond.target < state.atoms.length ∧
      bond.source ≠ bond.target
    omega
  · have projected : (state.bonds.map RawBond.edgeKey).map Prod.snd =
        state.bonds.map RawBond.target := by
      rw [List.map_map]
      apply List.map_congr_left
      intro bond membership
      change max bond.source bond.target = bond.target
      exact max_eq_right (Nat.le_of_lt (physical.forward bond membership))
    change (state.bonds.map RawBond.edgeKey).Nodup
    apply List.Nodup.of_map Prod.snd
    rw [projected]
    exact physical.targets

/-- General admission preservation from physical old records and one valid parent index. -/
theorem attachSingle_chronological (state : ParseState) (parent : ℕ) (atom : AtomSpec)
    (physical : Chronological state) (parentBound : parent < state.atoms.length) :
    Chronological (attachSingle state parent atom) := by
  constructor
  · intro bond membership
    change bond ∈ state.bonds ++ [{ source := parent, target := state.atoms.length, kind := .single }] at membership
    rcases List.mem_append.mp membership with old | fresh
    · exact physical.forward bond old
    · have equality := List.mem_singleton.mp fresh
      subst bond
      exact parentBound
  · intro bond membership
    change bond ∈ state.bonds ++ [{ source := parent, target := state.atoms.length, kind := .single }] at membership
    change bond.target < (state.atoms ++ [atom]).length
    simp only [List.length_append, List.length_singleton]
    rcases List.mem_append.mp membership with old | fresh
    · have bounded := physical.bounded bond old
      omega
    · have equality := List.mem_singleton.mp fresh
      subst bond
      change state.atoms.length < state.atoms.length + 1
      omega
  · change ((state.bonds ++ [({ source := parent, target := state.atoms.length, kind := .single } : RawBond)]).map RawBond.target).Nodup
    rw [List.map_append]
    change (state.bonds.map RawBond.target ++ [state.atoms.length]).Nodup
    apply List.nodup_append.mpr
    refine ⟨physical.targets, by simp, ?_⟩
    intro old oldMember fresh freshMember
    rcases List.mem_map.mp oldMember with ⟨bond, membership, rfl⟩
    have equality := List.mem_singleton.mp freshMember
    subst fresh
    exact Nat.ne_of_lt (physical.bounded bond membership)

theorem singleBranchResult_chronological (state : ParseState) (parent : ℕ)
    (atom : AtomSpec) (physical : Chronological state)
    (parentBound : parent < state.atoms.length) :
    Chronological (singleBranchResult state parent atom) :=
  attachSingle_chronological state parent atom physical parentBound

theorem pendantBranchResult_chronological (state : ParseState) (parent : ℕ)
    (parity : TetrahedralInputParity) (physical : Chronological state)
    (parentBound : parent < state.atoms.length) :
    Chronological (pendantBranchResult state parent parity) := by
  let opened : ParseState := { state with branches := parent :: state.branches }
  let tagIndex := state.atoms.length
  let tagged := attachSingle opened parent (atomSpec (.taggedCarbon parity))
  let hydrogen := singleBranchResult tagged tagIndex (atomSpec .hydrogen)
  let fluorine := singleBranchResult hydrogen tagIndex (atomSpec .fluorine)
  let bromine := attachSingle fluorine tagIndex (atomSpec .bromine)
  have taggedPhysical : Chronological tagged :=
    attachSingle_chronological opened parent _ physical parentBound
  have taggedBound : tagIndex < tagged.atoms.length := by
    change state.atoms.length < (state.atoms ++ [atomSpec (.taggedCarbon parity)]).length
    simp only [List.length_append, List.length_singleton]
    omega
  have hydrogenPhysical : Chronological hydrogen :=
    singleBranchResult_chronological tagged tagIndex _ taggedPhysical taggedBound
  have hydrogenBound : tagIndex < hydrogen.atoms.length := by
    change tagIndex < (tagged.atoms ++ [atomSpec .hydrogen]).length
    simp only [List.length_append, List.length_singleton]
    omega
  have fluorinePhysical : Chronological fluorine :=
    singleBranchResult_chronological hydrogen tagIndex _ hydrogenPhysical hydrogenBound
  have fluorineBound : tagIndex < fluorine.atoms.length := by
    change tagIndex < (hydrogen.atoms ++ [atomSpec .fluorine]).length
    simp only [List.length_append, List.length_singleton]
    omega
  have brominePhysical : Chronological bromine :=
    attachSingle_chronological fluorine tagIndex _ fluorinePhysical fluorineBound
  exact brominePhysical

theorem blockResult_chronological (state : ParseState) (parent : ℕ)
    (parity : TetrahedralInputParity) (physical : Chronological state)
    (parentBound : parent < state.atoms.length) :
    Chronological (blockResult state parent parity) := by
  let backbone := attachSingle state parent (atomSpec .carbon)
  let hydrogen := singleBranchResult backbone state.atoms.length (atomSpec .hydrogen)
  have backbonePhysical : Chronological backbone :=
    attachSingle_chronological state parent _ physical parentBound
  have backboneBound : state.atoms.length < backbone.atoms.length := by
    change state.atoms.length < (state.atoms ++ [atomSpec .carbon]).length
    simp only [List.length_append, List.length_singleton]
    omega
  have hydrogenPhysical : Chronological hydrogen :=
    singleBranchResult_chronological backbone state.atoms.length _ backbonePhysical backboneBound
  have hydrogenBound : state.atoms.length < hydrogen.atoms.length := by
    change state.atoms.length < (backbone.atoms ++ [atomSpec .hydrogen]).length
    simp only [List.length_append, List.length_singleton]
    omega
  exact pendantBranchResult_chronological hydrogen state.atoms.length parity
    hydrogenPhysical hydrogenBound

theorem blocksResult_chronological (parities : List TetrahedralInputParity)
    (state : ParseState) (parent : ℕ) (physical : Chronological state)
    (parentBound : parent < state.atoms.length) :
    Chronological (blocksResult parities state parent) := by
  induction parities generalizing state parent with
  | nil => exact physical
  | cons parity rest ih =>
      apply ih (blockResult state parent parity) state.atoms.length
      · exact blockResult_chronological state parent parity physical parentBound
      · rw [blockResult_atom_count]
        omega

/-- The raw explicit-single update preserves actual source-introduction records. -/
theorem attachSingle_introduction (state : ParseState) (parent : Nat) (atom : AtomSpec)
    (valid : OpenSMILESIntroductionAppend.Valid state) (bound : parent < state.atoms.length) :
    OpenSMILESIntroductionAppend.Valid (attachSingle state parent atom) :=
  OpenSMILESIntroductionAppend.append_valid state parent atom valid bound

theorem singleBranchResult_introduction (state : ParseState) (parent : ℕ)
    (atom : AtomSpec) (physical : OpenSMILESIntroductionAppend.Valid state)
    (parentBound : parent < state.atoms.length) :
    OpenSMILESIntroductionAppend.Valid (singleBranchResult state parent atom) :=
  attachSingle_introduction state parent atom physical parentBound

theorem pendantBranchResult_introduction (state : ParseState) (parent : ℕ)
    (parity : TetrahedralInputParity) (physical : OpenSMILESIntroductionAppend.Valid state)
    (parentBound : parent < state.atoms.length) :
    OpenSMILESIntroductionAppend.Valid (pendantBranchResult state parent parity) := by
  let opened : ParseState := { state with branches := parent :: state.branches }
  let tagIndex := state.atoms.length
  let tagged := attachSingle opened parent (atomSpec (.taggedCarbon parity))
  let hydrogen := singleBranchResult tagged tagIndex (atomSpec .hydrogen)
  let fluorine := singleBranchResult hydrogen tagIndex (atomSpec .fluorine)
  let bromine := attachSingle fluorine tagIndex (atomSpec .bromine)
  have taggedPhysical : OpenSMILESIntroductionAppend.Valid tagged :=
    attachSingle_introduction opened parent _ physical parentBound
  have taggedBound : tagIndex < tagged.atoms.length := by
    change state.atoms.length < (state.atoms ++ [atomSpec (.taggedCarbon parity)]).length
    simp only [List.length_append, List.length_singleton]
    omega
  have hydrogenPhysical : OpenSMILESIntroductionAppend.Valid hydrogen :=
    singleBranchResult_introduction tagged tagIndex _ taggedPhysical taggedBound
  have hydrogenBound : tagIndex < hydrogen.atoms.length := by
    change tagIndex < (tagged.atoms ++ [atomSpec .hydrogen]).length
    simp only [List.length_append, List.length_singleton]
    omega
  have fluorinePhysical : OpenSMILESIntroductionAppend.Valid fluorine :=
    singleBranchResult_introduction hydrogen tagIndex _ hydrogenPhysical hydrogenBound
  have fluorineBound : tagIndex < fluorine.atoms.length := by
    change tagIndex < (hydrogen.atoms ++ [atomSpec .fluorine]).length
    simp only [List.length_append, List.length_singleton]
    omega
  have brominePhysical : OpenSMILESIntroductionAppend.Valid bromine :=
    attachSingle_introduction fluorine tagIndex _ fluorinePhysical fluorineBound
  exact brominePhysical

theorem blockResult_introduction (state : ParseState) (parent : ℕ)
    (parity : TetrahedralInputParity) (physical : OpenSMILESIntroductionAppend.Valid state)
    (parentBound : parent < state.atoms.length) :
    OpenSMILESIntroductionAppend.Valid (blockResult state parent parity) := by
  let backbone := attachSingle state parent (atomSpec .carbon)
  let hydrogen := singleBranchResult backbone state.atoms.length (atomSpec .hydrogen)
  have backbonePhysical : OpenSMILESIntroductionAppend.Valid backbone :=
    attachSingle_introduction state parent _ physical parentBound
  have backboneBound : state.atoms.length < backbone.atoms.length := by
    change state.atoms.length < (state.atoms ++ [atomSpec .carbon]).length
    simp only [List.length_append, List.length_singleton]
    omega
  have hydrogenPhysical : OpenSMILESIntroductionAppend.Valid hydrogen :=
    singleBranchResult_introduction backbone state.atoms.length _ backbonePhysical backboneBound
  have hydrogenBound : state.atoms.length < hydrogen.atoms.length := by
    change state.atoms.length < (backbone.atoms ++ [atomSpec .hydrogen]).length
    simp only [List.length_append, List.length_singleton]
    omega
  exact pendantBranchResult_introduction hydrogen state.atoms.length parity
    hydrogenPhysical hydrogenBound

theorem blocksResult_introduction (parities : List TetrahedralInputParity)
    (state : ParseState) (parent : ℕ) (physical : OpenSMILESIntroductionAppend.Valid state)
    (parentBound : parent < state.atoms.length) :
    OpenSMILESIntroductionAppend.Valid (blocksResult parities state parent) := by
  induction parities generalizing state parent with
  | nil => exact physical
  | cons parity rest ih =>
      apply ih (blockResult state parent parity) state.atoms.length
      · exact blockResult_introduction state parent parity physical parentBound
      · rw [blockResult_atom_count]
        omega

def initialHydrogenState : ParseState :=
  { atoms := [atomSpec .hydrogen], current? := some 0, order := [[]],
    introductionPredecessors := [none] }

/-- Current-index construction uses only independent raw append states. -/
def blocksParent : List TetrahedralInputParity → ParseState → ℕ → ℕ
  | [], _, parent => parent
  | parity :: rest, state, parent =>
      blocksParent rest (blockResult state parent parity) state.atoms.length

theorem blocksResult_current (parities : List TetrahedralInputParity)
    (state : ParseState) (parent : ℕ) (current : state.current? = some parent) :
    (blocksResult parities state parent).current? =
      some (blocksParent parities state parent) := by
  induction parities generalizing state parent with
  | nil => exact current
  | cons parity rest ih =>
      exact ih (blockResult state parent parity) state.atoms.length rfl

theorem blocksParent_bounded (parities : List TetrahedralInputParity)
    (state : ParseState) (parent : ℕ) (parentBound : parent < state.atoms.length) :
    blocksParent parities state parent < (blocksResult parities state parent).atoms.length := by
  induction parities generalizing state parent with
  | nil => exact parentBound
  | cons parity rest ih =>
      apply ih (blockResult state parent parity) state.atoms.length
      rw [blockResult_atom_count]
      omega

def familyChars (parities : List TetrahedralInputParity) : List Char :=
  atomChars .hydrogen ++ blocksChars parities ++ singleChars .hydrogen

def familyString (parities : List TetrahedralInputParity) : String :=
  String.ofList (familyChars parities)

def familyState (parities : List TetrahedralInputParity) : ParseState :=
  let constructed := blocksResult parities initialHydrogenState 0
  let parent := blocksParent parities initialHydrogenState 0
  attachSingle constructed parent (atomSpec .hydrogen)

/-- Raw molecule data are built independently of the parser. The prefix consists of raw
append/index records, and the final hydrogen is an explicit raw append with two written updates. -/
def familyRaw (parities : List TetrahedralInputParity) : RawMolecule :=
  let constructed := blocksResult parities initialHydrogenState 0
  let parent := blocksParent parities initialHydrogenState 0
  let index := constructed.atoms.length
  let appended := constructed.order ++ [[]]
  let parentUpdated := appended.set parent (appended.getD parent [] ++ [index])
  { atoms := constructed.atoms ++ [atomSpec .hydrogen]
    bonds := constructed.bonds ++ [{ source := parent, target := index, kind := .single }]
    neighborOrder := parentUpdated.set index (parentUpdated.getD index [] ++ [parent])
    introductionPredecessors :=
      if constructed.introductionPredecessors.length = constructed.atoms.length then
        constructed.introductionPredecessors ++ [some parent]
      else constructed.introductionPredecessors }

theorem familyState_molecule (parities : List TetrahedralInputParity) :
    (familyState parities).molecule = familyRaw parities := rfl

theorem familyState_chronological (parities : List TetrahedralInputParity) :
    Chronological (familyState parities) := by
  have initial : Chronological initialHydrogenState := by
    constructor
    · intro bond membership; cases membership
    · intro bond membership; cases membership
    · exact List.nodup_nil
  have initialBound : 0 < initialHydrogenState.atoms.length := by decide
  exact attachSingle_chronological _ _ _
    (blocksResult_chronological parities initialHydrogenState 0 initial initialBound)
    (blocksParent_bounded parities initialHydrogenState 0 initialBound)

/-- Every independently constructed family state has total source history, including all roots. -/
theorem familyState_introduction (parities : List TetrahedralInputParity) :
    OpenSMILESIntroductionAppend.Valid (familyState parities) := by
  have initial : OpenSMILESIntroductionAppend.Valid initialHydrogenState := by
    refine ⟨rfl, rfl, ?_⟩
    intro index predecessor observed
    cases index <;> simp [initialHydrogenState] at observed
  have initialBound : 0 < initialHydrogenState.atoms.length := by decide
  exact attachSingle_introduction _ _ _
    (blocksResult_introduction parities initialHydrogenState 0 initial initialBound)
    (blocksParent_bounded parities initialHydrogenState 0 initialBound)

theorem familyRaw_introduction_valid (parities : List TetrahedralInputParity) :
    (familyRaw parities).parserIntroductionValid? = true := by
  rw [← familyState_molecule]
  exact OpenSMILESIntroductionAppend.Valid.parserIntroductionValid _
    (familyState_introduction parities)

theorem familyRaw_admissible (parities : List TetrahedralInputParity) :
    (familyRaw parities).Admissible := by
  rw [← familyState_molecule]
  exact chronological_admissible _ (familyState_chronological parities)

theorem familyRaw_atom_count (parities : List TetrahedralInputParity) :
    (familyRaw parities).atomCount = 6 * parities.length + 2 := by
  change ((blocksResult parities initialHydrogenState 0).atoms ++
    [atomSpec .hydrogen]).length = _
  rw [List.length_append, List.length_singleton]
  rw [blocksResult_atom_count]
  change 1 + 6 * parities.length + 1 = _
  omega

theorem familyRaw_bond_count (parities : List TetrahedralInputParity) :
    (familyRaw parities).bonds.length = 6 * parities.length + 1 := by
  change ((blocksResult parities initialHydrogenState 0).bonds ++ [_]).length = _
  rw [List.length_append, List.length_singleton]
  rw [blocksResult_bond_count]
  change 0 + 6 * parities.length + 1 = _
  omega

/-- The family parser consumes the initial H, all blocks, and the final '-H', for every parity
list and arbitrary spare fuel. The independent raw append state is proved as the actual result. -/
theorem parse_family_chars_fuel (parities : List TetrahedralInputParity) (spare : ℕ) :
    parseCharsFuel (spare + 20 * parities.length + 4) (familyChars parities) {} =
      Except.ok (familyState parities) := by
  simp only [familyChars, List.append_assoc]
  rw [parse_family_atom_step .hydrogen (spare + 20 * parities.length + 3)]
  change parseCharsFuel (spare + 20 * parities.length + 3)
    (blocksChars parities ++ singleChars .hydrogen) initialHydrogenState = _
  have budget : spare + 20 * parities.length + 3 =
      (spare + 3) + 20 * parities.length := by omega
  rw [budget, parse_blocks_continuation parities (spare + 3)
    (singleChars .hydrogen) initialHydrogenState 0 rfl]
  have current := blocksResult_current parities initialHydrogenState 0 rfl
  change parseCharsFuel ((spare + 1) + 2) (singleChars .hydrogen ++ [])
    (blocksResult parities initialHydrogenState 0) = _
  rw [parse_single_chars_step .hydrogen (spare + 1) []
    (blocksResult parities initialHydrogenState 0)
    (blocksParent parities initialHydrogenState 0) current]
  all_goals rfl

theorem block_chars_token_budget (parity : TetrahedralInputParity) :
    20 ≤ (blockChars parity).length := by
  cases parity <;> decide

theorem blocks_chars_token_budget (parities : List TetrahedralInputParity) :
    20 * parities.length ≤ (blocksChars parities).length := by
  induction parities with
  | nil => decide
  | cons parity rest ih =>
      simp only [blocksChars, List.length_append, List.length_cons]
      have budget := block_chars_token_budget parity
      omega

theorem family_chars_token_budget (parities : List TetrahedralInputParity) :
    20 * parities.length + 4 ≤ (familyChars parities).length + 1 := by
  have budget := blocks_chars_token_budget parities
  change 20 * parities.length + 4 ≤
    (atomChars .hydrogen ++ blocksChars parities ++ singleChars .hydrogen).length + 1
  simp only [List.length_append]
  change 20 * parities.length + 4 ≤ 3 + (blocksChars parities).length + 4 + 1
  omega

/-- The actual public character-based fuel is derived from string length, never supplied. -/
theorem parse_family_chars (parities : List TetrahedralInputParity) :
    parseChars (familyChars parities) {} = Except.ok (familyState parities) := by
  have budget := family_chars_token_budget parities
  let spare := (familyChars parities).length + 1 - (20 * parities.length + 4)
  have fuel : (familyChars parities).length + 1 =
      spare + 20 * parities.length + 4 := by dsimp [spare]; omega
  unfold parseChars
  rw [fuel]
  exact parse_family_chars_fuel parities spare

theorem blockResult_rings (state : ParseState) (parent : ℕ)
    (parity : TetrahedralInputParity) :
    (blockResult state parent parity).rings = state.rings := rfl

theorem blocksResult_rings (parities : List TetrahedralInputParity)
    (state : ParseState) (parent : ℕ) :
    (blocksResult parities state parent).rings = state.rings := by
  induction parities generalizing state parent with
  | nil => rfl
  | cons parity rest ih => rw [blocksResult, ih, blockResult_rings]

theorem familyState_branches (parities : List TetrahedralInputParity) :
    (familyState parities).branches = [] := by
  change (blocksResult parities initialHydrogenState 0).branches = []
  rw [blocksResult_branches]
  rfl

theorem familyState_rings (parities : List TetrahedralInputParity) :
    (familyState parities).rings = [] := by
  change (blocksResult parities initialHydrogenState 0).rings = []
  rw [blocksResult_rings]
  rfl

theorem familyState_pending (parities : List TetrahedralInputParity) :
    (familyState parities).pendingBond? = none := rfl

def AllSingle (state : ParseState) : Prop :=
  ∀ bond, bond ∈ state.bonds → bond.kind = .single

theorem attachSingle_all_single (state : ParseState) (parent : ℕ) (atom : AtomSpec)
    (single : AllSingle state) : AllSingle (attachSingle state parent atom) := by
  intro bond membership
  change bond ∈ state.bonds ++ [{ source := parent, target := state.atoms.length, kind := .single }] at membership
  rcases List.mem_append.mp membership with old | fresh
  · exact single bond old
  · have equality := List.mem_singleton.mp fresh
    subst bond
    rfl

theorem blockResult_all_single (state : ParseState) (parent : ℕ)
    (parity : TetrahedralInputParity) (single : AllSingle state) :
    AllSingle (blockResult state parent parity) := by
  intro bond membership
  simp only [blockResult, pendantBranchResult, singleBranchResult, attachSingle,
    List.mem_append, List.mem_singleton] at membership
  rcases membership with ((((((old | fresh) | fresh) | fresh) | fresh) | fresh) | fresh)
  · exact single bond old
  all_goals subst bond
  all_goals rfl

theorem blocksResult_all_single (parities : List TetrahedralInputParity)
    (state : ParseState) (parent : ℕ) (single : AllSingle state) :
    AllSingle (blocksResult parities state parent) := by
  induction parities generalizing state parent with
  | nil => exact single
  | cons parity rest ih =>
      exact ih (blockResult state parent parity) state.atoms.length
        (blockResult_all_single state parent parity single)

theorem familyRaw_all_single (parities : List TetrahedralInputParity) :
    ∀ bond, bond ∈ (familyRaw parities).bonds → bond.kind = .single := by
  have initial : AllSingle initialHydrogenState := by
    intro bond membership
    cases membership
  rw [← familyState_molecule]
  change AllSingle (familyState parities)
  exact attachSingle_all_single (blocksResult parities initialHydrogenState 0)
    (blocksParent parities initialHydrogenState 0) (atomSpec .hydrogen)
    (blocksResult_all_single parities initialHydrogenState 0 initial)

theorem normalize_eq_of_all_single (molecule : RawMolecule)
    (single : ∀ bond, bond ∈ molecule.bonds → bond.kind = .single) :
    molecule.normalizeUnspecifiedBonds = molecule := by
  have bonds : molecule.bonds.map molecule.normalizeUnspecifiedBond = molecule.bonds := by
    calc
      molecule.bonds.map molecule.normalizeUnspecifiedBond = molecule.bonds.map id := by
        apply List.map_congr_left
        intro bond membership
        change molecule.normalizeUnspecifiedBond bond = bond
        simp only [RawMolecule.normalizeUnspecifiedBond, single bond membership]
      _ = molecule.bonds := List.map_id _
  unfold RawMolecule.normalizeUnspecifiedBonds
  rw [bonds]

theorem familyRaw_normalize_eq (parities : List TetrahedralInputParity) :
    (familyRaw parities).normalizeUnspecifiedBonds = familyRaw parities :=
  normalize_eq_of_all_single _ (familyRaw_all_single parities)

/-- Grammar state at an atom boundary, with the exact branch-opening counters. -/
def familySyntaxState (count : Nat) (branches : List Nat := []) : OpenSMILESSyntaxState :=
  { currentPresent := true, pendingBond := false, atomsSeen := count, branchStarts := branches }

theorem syntax_family_atom_step (kind : FamilyAtom) (fuel : Nat)
    (tail : List Char) (state : OpenSMILESSyntaxState) :
    openSMILESSyntaxValidFuel (fuel + 1) (atomChars kind ++ tail) state =
      openSMILESSyntaxValidFuel fuel tail state.afterAtom := by
  cases kind with
  | hydrogen => rfl
  | carbon => rfl
  | taggedCarbon parity => cases parity <;> rfl
  | fluorine => rfl
  | bromine => rfl

theorem syntax_single_chars_step (kind : FamilyAtom) (fuel : Nat)
    (tail : List Char) (count : Nat) (branches : List Nat) :
    openSMILESSyntaxValidFuel (fuel + 2) (singleChars kind ++ tail)
      (familySyntaxState count branches) =
      openSMILESSyntaxValidFuel fuel tail (familySyntaxState (count + 1) branches) := by
  change openSMILESSyntaxValidFuel (fuel + 1) (atomChars kind ++ tail)
    { familySyntaxState count branches with pendingBond := true } = _
  rw [syntax_family_atom_step]
  rfl

theorem syntax_open_branch_step (fuel : Nat) (tail : List Char)
    (count : Nat) (branches : List Nat) (ready : branches.head? ≠ some count) :
    openSMILESSyntaxValidFuel (fuel + 1) ('(' :: tail) (familySyntaxState count branches) =
      openSMILESSyntaxValidFuel fuel tail (familySyntaxState count (count :: branches)) := by
  change (!(branches.head? == some count) &&
    openSMILESSyntaxValidFuel fuel tail (familySyntaxState count (count :: branches))) = _
  have different : (branches.head? == some count) = false := by simp [ready]
  rw [different]
  rfl

theorem syntax_close_branch_step (fuel : Nat) (tail : List Char)
    (count opened : Nat) (branches : List Nat) (nonempty : opened < count) :
    openSMILESSyntaxValidFuel (fuel + 1) (')' :: tail)
      (familySyntaxState count (opened :: branches)) =
      openSMILESSyntaxValidFuel fuel tail (familySyntaxState count branches) := by
  change (decide (opened < count) &&
    openSMILESSyntaxValidFuel fuel tail (familySyntaxState count branches)) = _
  rw [show decide (opened < count) = true from decide_eq_true nonempty]
  rfl

theorem syntax_branch_chars_step (kind : FamilyAtom) (fuel : Nat)
    (tail : List Char) (count : Nat) (branches : List Nat)
    (ready : branches.head? ≠ some count) :
    openSMILESSyntaxValidFuel (fuel + 4) (branchChars kind ++ tail)
      (familySyntaxState count branches) =
      openSMILESSyntaxValidFuel fuel tail (familySyntaxState (count + 1) branches) := by
  simp only [branchChars, List.cons_append, List.append_assoc, List.nil_append]
  change openSMILESSyntaxValidFuel ((fuel + 3) + 1)
    ('(' :: (singleChars kind ++ ')' :: tail)) (familySyntaxState count branches) = _
  rw [syntax_open_branch_step _ _ count branches ready]
  change openSMILESSyntaxValidFuel ((fuel + 1) + 2)
    (singleChars kind ++ ')' :: tail) (familySyntaxState count (count :: branches)) = _
  rw [syntax_single_chars_step, syntax_close_branch_step fuel tail (count + 1) count branches
    (Nat.lt_succ_self count)]

theorem syntax_pendant_continuation (parity : TetrahedralInputParity) (fuel : Nat)
    (tail : List Char) (count : Nat) (branches : List Nat)
    (ready : branches.head? ≠ some count) :
    openSMILESSyntaxValidFuel (fuel + 14) (pendantChars parity ++ tail)
      (familySyntaxState count branches) =
      openSMILESSyntaxValidFuel fuel tail (familySyntaxState (count + 4) branches) := by
  simp only [pendantChars, List.cons_append, List.append_assoc, List.nil_append]
  rw [syntax_open_branch_step (fuel + 13) _ count branches ready]
  change openSMILESSyntaxValidFuel ((fuel + 11) + 2)
    (singleChars (.taggedCarbon parity) ++ _) (familySyntaxState count (count :: branches)) = _
  rw [syntax_single_chars_step]
  change openSMILESSyntaxValidFuel ((fuel + 7) + 4)
    (branchChars .hydrogen ++ _) (familySyntaxState (count + 1) (count :: branches)) = _
  rw [syntax_branch_chars_step .hydrogen (fuel + 7) _ (count + 1) (count :: branches)
    (by simp)]
  change openSMILESSyntaxValidFuel ((fuel + 3) + 4)
    (branchChars .fluorine ++ _) (familySyntaxState (count + 2) (count :: branches)) = _
  rw [syntax_branch_chars_step .fluorine (fuel + 3) _ (count + 2) (count :: branches)
    (by simp)]
  change openSMILESSyntaxValidFuel ((fuel + 1) + 2)
    (singleChars .bromine ++ _) (familySyntaxState (count + 3) (count :: branches)) = _
  rw [syntax_single_chars_step]
  change openSMILESSyntaxValidFuel (fuel + 1) (')' :: tail)
    (familySyntaxState (count + 4) (count :: branches)) = _
  rw [syntax_close_branch_step fuel tail (count + 4) count branches (by omega)]

theorem syntax_block_continuation (parity : TetrahedralInputParity) (fuel : Nat)
    (tail : List Char) (count : Nat) :
    openSMILESSyntaxValidFuel (fuel + 20) (blockChars parity ++ tail)
      (familySyntaxState count) =
      openSMILESSyntaxValidFuel fuel tail (familySyntaxState (count + 6)) := by
  simp only [blockChars, List.append_assoc]
  change openSMILESSyntaxValidFuel ((fuel + 18) + 2) (singleChars .carbon ++ _)
    (familySyntaxState count) = _
  rw [syntax_single_chars_step]
  change openSMILESSyntaxValidFuel ((fuel + 14) + 4) (branchChars .hydrogen ++ _)
    (familySyntaxState (count + 1)) = _
  rw [syntax_branch_chars_step .hydrogen (fuel + 14) _ (count + 1) [] (by simp)]
  change openSMILESSyntaxValidFuel (fuel + 14) (pendantChars parity ++ tail)
    (familySyntaxState (count + 2)) = _
  rw [syntax_pendant_continuation parity fuel tail (count + 2) [] (by simp)]

theorem syntax_blocks_continuation (parities : List TetrahedralInputParity) (fuel : Nat)
    (tail : List Char) (count : Nat) :
    openSMILESSyntaxValidFuel (fuel + 20 * parities.length) (blocksChars parities ++ tail)
      (familySyntaxState count) =
      openSMILESSyntaxValidFuel fuel tail (familySyntaxState (count + 6 * parities.length)) := by
  induction parities generalizing count with
  | nil => rfl
  | cons parity rest ih =>
      simp only [blocksChars, List.length_cons, List.append_assoc]
      rw [show fuel + 20 * (rest.length + 1) = (fuel + 20 * rest.length) + 20 by omega,
        syntax_block_continuation, ih]
      congr 2
      omega

theorem syntax_family_chars_fuel (parities : List TetrahedralInputParity) (spare : Nat) :
    openSMILESSyntaxValidFuel (spare + 20 * parities.length + 4) (familyChars parities) {} = true := by
  simp only [familyChars, List.append_assoc]
  rw [syntax_family_atom_step .hydrogen (spare + 20 * parities.length + 3)]
  change openSMILESSyntaxValidFuel (spare + 20 * parities.length + 3)
    (blocksChars parities ++ singleChars .hydrogen) (familySyntaxState 1) = _
  rw [show spare + 20 * parities.length + 3 = (spare + 3) + 20 * parities.length by omega,
    syntax_blocks_continuation]
  change openSMILESSyntaxValidFuel ((spare + 1) + 2) (singleChars .hydrogen ++ [])
    (familySyntaxState (1 + 6 * parities.length)) = _
  rw [syntax_single_chars_step]
  rfl

theorem family_syntax_valid (parities : List TetrahedralInputParity) :
    openSMILESSyntaxValid (familyString parities) = true := by
  have budget := family_chars_token_budget parities
  let spare := (familyChars parities).length + 1 - (20 * parities.length + 4)
  have fuel : (familyChars parities).length + 1 = spare + 20 * parities.length + 4 := by
    dsimp [spare]
    omega
  unfold openSMILESSyntaxValid familyString
  rw [String.toList_ofList, fuel]
  exact syntax_family_chars_fuel parities spare

/-- Public parsing for every finite parity list, with both new guards derived from the actual
source grammar and independent chronological records. No successful parse is a caller premise. -/
theorem parse_family_string_normalized (parities : List TetrahedralInputParity) :
    parseOpenSMILES (familyString parities) =
      Except.ok (familyRaw parities).normalizeUnspecifiedBonds := by
  have admitted : (familyRaw parities).admissible? = true :=
    (RawMolecule.admissible?_eq_true_iff _).mpr (familyRaw_admissible parities)
  have finalized : finalizeParseState (familyState parities) = .ok (familyRaw parities) := by
    unfold finalizeParseState
    rw [familyState_branches, familyState_rings, familyState_pending]
    rw [if_pos rfl, if_pos rfl, if_pos rfl, familyState_molecule]
    rw [familyRaw_normalize_eq]
    exact if_pos admitted
  rw [familyRaw_normalize_eq]
  apply parseOpenSMILES_eq_ok_of _ (familyState parities) _
    (family_syntax_valid parities) _ finalized (familyRaw_introduction_valid parities)
  simpa only [familyString, String.toList_ofList] using parse_family_chars parities

/-- Whole actual public family parser: arbitrary size and arbitrary parity, independent
physical raw records, internally derived fuel/admission/normalization, and no success premise. -/
theorem parse_family_string (parities : List TetrahedralInputParity) :
    parseOpenSMILES (familyString parities) = Except.ok (familyRaw parities) := by
  rw [parse_family_string_normalized, familyRaw_normalize_eq]

/-- Fixed-size interface for every n and arbitrary Fin n parity data. Positive families are
instances; n=0 is the valid two-hydrogen parser family, not the canonical physical n=0 fixture. -/
theorem parse_family_ofFn (n : ℕ) (parity : Fin n → TetrahedralInputParity) :
    parseOpenSMILES (familyString (List.ofFn parity)) = Except.ok (familyRaw (List.ofFn parity)) ∧
      (familyRaw (List.ofFn parity)).atomCount = 6 * n + 2 ∧
      (familyRaw (List.ofFn parity)).bonds.length = 6 * n + 1 ∧
      (familyRaw (List.ofFn parity)).Admissible := by
  refine ⟨parse_family_string _, ?_, ?_, familyRaw_admissible _⟩
  · simpa only [List.length_ofFn] using familyRaw_atom_count (List.ofFn parity)
  · simpa only [List.length_ofFn] using familyRaw_bond_count (List.ofFn parity)

end TetraStereo.UniversalProof.GeneralParserStateBridge
