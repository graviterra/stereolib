import TetraStereo.UniversalProof.NativeAttachSingleWrittenAppendJoinProofs.NativeAttachSingleWrittenAppendJoin
import TetraStereo.UniversalProof.NativeBracketAtomSpecContinuationsProofs.NativeBracketAtomSpecContinuations
import TetraStereo.UniversalProof.SecondSphereFamilyPhysicalInstantiation

set_option autoImplicit false

namespace TetraStereo.UniversalProof.SecondSphereNativeBlockParser

open TetraStereo.OneCenter
open TetraStereo.UniversalProof.GeneralParserStateBridge
open TetraStereo.UniversalProof.GeneralWrittenNeighborBridge
open TetraStereo.UniversalProof.ChronologicalRawAdmissionRecoveryProofs.ChronologicalRawAdmissionRecovery
open TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords
open TetraStereo.UniversalProof.NativeAttachSingleWrittenAppendJoinProofs
open TetraStereo.UniversalProof.NativeBracketAtomSpecContinuationsProofs.NativeBracketAtomSpecContinuations






def singleRoleChars (parity : TetrahedralInputParity) (role : FamilyRole) : List Char :=
  '-' :: roleChars parity role

def branchRoleChars (parity : TetrahedralInputParity) (role : FamilyRole) : List Char :=
  '(' :: '-' :: (roleChars parity role ++ [')'])

theorem parse_single_role (parity : TetrahedralInputParity) (role : FamilyRole)
    (fuel : Nat) (tail : List Char) (state : ParseState) (parent : Nat)
    (current : state.current? = some parent) :
    parseCharsFuel (fuel + 2) (singleRoleChars parity role ++ tail) state =
      parseCharsFuel fuel tail (attachSingle state parent (roleAtom parity role)) := by
  simpa only [singleRoleChars, List.cons_append] using
    native_role_single_step parity role fuel tail state parent current

theorem parse_branch_role (parity : TetrahedralInputParity) (role : FamilyRole)
    (fuel : Nat) (tail : List Char) (state : ParseState) (parent : Nat)
    (current : state.current? = some parent) :
    parseCharsFuel (fuel + 4) (branchRoleChars parity role ++ tail) state =
      parseCharsFuel fuel tail (singleBranchResult state parent (roleAtom parity role)) := by
  simpa only [branchRoleChars, List.cons_append, List.append_assoc,
    List.singleton_append] using native_role_branch_continuation parity role fuel tail state parent current

/-- Actual chronological token sequence. Bridge branch restores the block backbone. -/
def nativeBlockChars (parity : TetrahedralInputParity) : List Char :=
  singleRoleChars parity .backboneCarbon ++ branchRoleChars parity .backboneHydrogen ++
    ('(' :: (singleRoleChars parity .bridgeCarbon ++
      branchRoleChars parity .bridgeHydrogenA ++ branchRoleChars parity .bridgeHydrogenB ++
      singleRoleChars parity .tagCarbon ++ branchRoleChars parity .tagHydrogen ++
      branchRoleChars parity .fluorine ++ singleRoleChars parity .methylCarbon ++
      branchRoleChars parity .methylHydrogenA ++ branchRoleChars parity .methylHydrogenB ++
      singleRoleChars parity .methylHydrogenC ++ [')']))

/-- Native raw record updates in exactly543 allocation order; no parser is called here. -/
def nativeBlockResult (state : ParseState) (parent : Nat)
    (parity : TetrahedralInputParity) : ParseState :=
  let base := state.atoms.length
  let s1 := attachSingle state (parent) (roleAtom parity .backboneCarbon)
  let s2 := singleBranchResult s1 (base) (roleAtom parity .backboneHydrogen)
  let opened : ParseState := { s2 with branches := base :: state.branches }
  let s3 := attachSingle opened (base) (roleAtom parity .bridgeCarbon)
  let s4 := singleBranchResult s3 (base + 2) (roleAtom parity .bridgeHydrogenA)
  let s5 := singleBranchResult s4 (base + 2) (roleAtom parity .bridgeHydrogenB)
  let s6 := attachSingle s5 (base + 2) (roleAtom parity .tagCarbon)
  let s7 := singleBranchResult s6 (base + 5) (roleAtom parity .tagHydrogen)
  let s8 := singleBranchResult s7 (base + 5) (roleAtom parity .fluorine)
  let s9 := attachSingle s8 (base + 5) (roleAtom parity .methylCarbon)
  let s10 := singleBranchResult s9 (base + 8) (roleAtom parity .methylHydrogenA)
  let s11 := singleBranchResult s10 (base + 8) (roleAtom parity .methylHydrogenB)
  let s12 := attachSingle s11 (base + 8) (roleAtom parity .methylHydrogenC)
  { s12 with current? := some base, branches := state.branches }

/-- Actual arbitrary-state and arbitrary-tail continuation; twelve atom/single pairs and
 eight open/close pairs consume exactly40 parser recursions. -/
theorem parse_native_block (parity : TetrahedralInputParity) (fuel : Nat)
    (tail : List Char) (state : ParseState) (parent : Nat)
    (current : state.current? = some parent) :
    parseCharsFuel (fuel + 40) (nativeBlockChars parity ++ tail) state =
      parseCharsFuel fuel tail (nativeBlockResult state parent parity) := by
  let base := state.atoms.length
  let s1 := attachSingle state (parent) (roleAtom parity .backboneCarbon)
  let s2 := singleBranchResult s1 (base) (roleAtom parity .backboneHydrogen)
  let opened : ParseState := { s2 with branches := base :: state.branches }
  let s3 := attachSingle opened (base) (roleAtom parity .bridgeCarbon)
  let s4 := singleBranchResult s3 (base + 2) (roleAtom parity .bridgeHydrogenA)
  let s5 := singleBranchResult s4 (base + 2) (roleAtom parity .bridgeHydrogenB)
  let s6 := attachSingle s5 (base + 2) (roleAtom parity .tagCarbon)
  let s7 := singleBranchResult s6 (base + 5) (roleAtom parity .tagHydrogen)
  let s8 := singleBranchResult s7 (base + 5) (roleAtom parity .fluorine)
  let s9 := attachSingle s8 (base + 5) (roleAtom parity .methylCarbon)
  let s10 := singleBranchResult s9 (base + 8) (roleAtom parity .methylHydrogenA)
  let s11 := singleBranchResult s10 (base + 8) (roleAtom parity .methylHydrogenB)
  let s12 := attachSingle s11 (base + 8) (roleAtom parity .methylHydrogenC)
  have c1 : s1.atoms.length = base + 1 := by
    change (state.atoms ++ [_]).length = base + 1
    simp only [List.length_append, List.length_singleton, base]
  have c2 : s2.atoms.length = base + 2 := by
    change (s1.atoms ++ [_]).length = base + 2
    simp only [List.length_append, List.length_singleton, c1]
  have c3 : s3.atoms.length = base + 3 := by
    change (s2.atoms ++ [_]).length = base + 3
    simp only [List.length_append, List.length_singleton, c2]
  have c4 : s4.atoms.length = base + 4 := by
    change (s3.atoms ++ [_]).length = base + 4
    simp only [List.length_append, List.length_singleton, c3]
  have c5 : s5.atoms.length = base + 5 := by
    change (s4.atoms ++ [_]).length = base + 5
    simp only [List.length_append, List.length_singleton, c4]
  have c6 : s6.atoms.length = base + 6 := by
    change (s5.atoms ++ [_]).length = base + 6
    simp only [List.length_append, List.length_singleton, c5]
  have c7 : s7.atoms.length = base + 7 := by
    change (s6.atoms ++ [_]).length = base + 7
    simp only [List.length_append, List.length_singleton, c6]
  have c8 : s8.atoms.length = base + 8 := by
    change (s7.atoms ++ [_]).length = base + 8
    simp only [List.length_append, List.length_singleton, c7]
  simp only [nativeBlockChars, List.append_assoc]
  change parseCharsFuel ((fuel + 38) + 2) (singleRoleChars parity .backboneCarbon ++ _) state = _
  rw [parse_single_role parity .backboneCarbon (fuel + 38) _ state (parent) current]
  change parseCharsFuel ((fuel + 34) + 4) (branchRoleChars parity .backboneHydrogen ++ _) s1 = _
  rw [parse_branch_role parity .backboneHydrogen (fuel + 34) _ s1 (base) rfl]
  change parseCharsFuel ((fuel + 33) + 1) ('(' :: _) s2 = _
  rw [parse_open_branch_step (fuel + 33) _ s2 base rfl]
  change parseCharsFuel ((fuel + 31) + 2) (singleRoleChars parity .bridgeCarbon ++ _) opened = _
  rw [parse_single_role parity .bridgeCarbon (fuel + 31) _ opened (base) rfl]
  change parseCharsFuel ((fuel + 27) + 4) (branchRoleChars parity .bridgeHydrogenA ++ _) s3 = _
  rw [parse_branch_role parity .bridgeHydrogenA (fuel + 27) _ s3 (base + 2) (by change some s2.atoms.length = some (base + 2); rw [c2])]
  change parseCharsFuel ((fuel + 23) + 4) (branchRoleChars parity .bridgeHydrogenB ++ _) s4 = _
  rw [parse_branch_role parity .bridgeHydrogenB (fuel + 23) _ s4 (base + 2) rfl]
  let afterTag := branchRoleChars parity .tagHydrogen ++
    branchRoleChars parity .fluorine ++ singleRoleChars parity .methylCarbon ++
    branchRoleChars parity .methylHydrogenA ++ branchRoleChars parity .methylHydrogenB ++
    singleRoleChars parity .methylHydrogenC ++ [')']
  change parseCharsFuel (fuel + 23)
    ('-' :: ((roleChars parity .tagCarbon ++ afterTag) ++ tail)) s5 = _
  have charsEq : ('-' :: ((roleChars parity .tagCarbon ++ afterTag) ++ tail)) =
      singleRoleChars parity .tagCarbon ++ (afterTag ++ tail) := by
    change ('-' :: ((roleChars parity .tagCarbon ++ afterTag) ++ tail)) =
      ('-' :: (roleChars parity .tagCarbon ++ (afterTag ++ tail)))
    exact congrArg (fun chars : List Char => '-' :: chars)
      (List.append_assoc (roleChars parity .tagCarbon) afterTag tail)
  rw [charsEq]
  change parseCharsFuel ((fuel + 21) + 2)
    (singleRoleChars parity .tagCarbon ++ (afterTag ++ tail)) s5 = _
  rw [parse_single_role parity .tagCarbon (fuel + 21) _ s5 (base + 2) rfl]
  change parseCharsFuel ((fuel + 17) + 4) (branchRoleChars parity .tagHydrogen ++ _) s6 = _
  rw [parse_branch_role parity .tagHydrogen (fuel + 17) _ s6 (base + 5) (by change some s5.atoms.length = some (base + 5); rw [c5])]
  change parseCharsFuel ((fuel + 13) + 4) (branchRoleChars parity .fluorine ++ _) s7 = _
  rw [parse_branch_role parity .fluorine (fuel + 13) _ s7 (base + 5) rfl]
  change parseCharsFuel ((fuel + 11) + 2) (singleRoleChars parity .methylCarbon ++ _) s8 = _
  rw [parse_single_role parity .methylCarbon (fuel + 11) _ s8 (base + 5) rfl]
  change parseCharsFuel ((fuel + 7) + 4) (branchRoleChars parity .methylHydrogenA ++ _) s9 = _
  rw [parse_branch_role parity .methylHydrogenA (fuel + 7) _ s9 (base + 8) (by change some s8.atoms.length = some (base + 8); rw [c8])]
  change parseCharsFuel ((fuel + 3) + 4) (branchRoleChars parity .methylHydrogenB ++ _) s10 = _
  rw [parse_branch_role parity .methylHydrogenB (fuel + 3) _ s10 (base + 8) rfl]
  change parseCharsFuel ((fuel + 1) + 2) (singleRoleChars parity .methylHydrogenC ++ _) s11 = _
  rw [parse_single_role parity .methylHydrogenC (fuel + 1) _ s11 (base + 8) rfl]
  change parseCharsFuel (fuel + 1) (')' :: tail) s12 = _
  rw [parse_close_branch_step fuel tail s12 base state.branches rfl]
  rfl

private theorem fresh_transport (state : ParseState) (raw : RawMolecule)
    (parent : Nat) (atom : AtomSpec) (same : state.molecule = raw)
    (rows : state.order.length = state.atoms.length) (bound : parent < raw.atomCount) :
    (attachSingle state parent atom).molecule = appendFreshChild raw ⟨parent, bound⟩ atom := by
  have nativeBound : parent < state.atoms.length := by
    change parent < state.molecule.atomCount
    rw [same]
    exact bound
  have joined := native_attachSingle_appendFreshChild state parent atom rows nativeBound
  exact joined.trans (by cases same; rfl)

/- Reduce branch record projections once with an arbitrary state, rather than repeatedly
unfolding the entire nested block history during each row/molecule type conversion. -/
private theorem branch_rows (state : ParseState) (parent : Nat) (atom : AtomSpec)
    (rows : state.order.length = state.atoms.length) :
    (singleBranchResult state parent atom).order.length =
      (singleBranchResult state parent atom).atoms.length := by
  change (attachSingle state parent atom).order.length =
    (attachSingle state parent atom).atoms.length
  exact attachSingle_row_count state parent atom rows

private theorem branch_fresh_transport (state : ParseState) (raw : RawMolecule)
    (parent : Nat) (atom : AtomSpec) (same : state.molecule = raw)
    (rows : state.order.length = state.atoms.length) (bound : parent < raw.atomCount) :
    (singleBranchResult state parent atom).molecule =
      appendFreshChild raw ⟨parent, bound⟩ atom := by
  change (attachSingle state parent atom).molecule = _
  exact fresh_transport state raw parent atom same rows bound

private theorem restore_molecule (state : ParseState) (current : Option Nat) (branches : List Nat) :
    ({ state with current? := current, branches := branches } : ParseState).molecule =
      state.molecule := rfl

set_option maxHeartbeats 4000000 in
/-- Full actual raw equality, including the complete written table. Only independent
 old row completeness and a real external parent are consumed. -/
theorem native_block_molecule (state : ParseState) (parent : Fin state.molecule.atomCount)
    (parity : TetrahedralInputParity) (rows : state.order.length = state.atoms.length) :
    (nativeBlockResult state parent.val parity).molecule =
      blockAppend state.molecule state.atoms.length rfl parent parity := by
  let external := parent
  let parent := external.val
  let base := state.atoms.length
  let s1 := attachSingle state (parent) (roleAtom parity .backboneCarbon)
  let s2 := singleBranchResult s1 (base) (roleAtom parity .backboneHydrogen)
  let opened : ParseState := { s2 with branches := base :: state.branches }
  let s3 := attachSingle opened (base) (roleAtom parity .bridgeCarbon)
  let s4 := singleBranchResult s3 (base + 2) (roleAtom parity .bridgeHydrogenA)
  let s5 := singleBranchResult s4 (base + 2) (roleAtom parity .bridgeHydrogenB)
  let s6 := attachSingle s5 (base + 2) (roleAtom parity .tagCarbon)
  let s7 := singleBranchResult s6 (base + 5) (roleAtom parity .tagHydrogen)
  let s8 := singleBranchResult s7 (base + 5) (roleAtom parity .fluorine)
  let s9 := attachSingle s8 (base + 5) (roleAtom parity .methylCarbon)
  let s10 := singleBranchResult s9 (base + 8) (roleAtom parity .methylHydrogenA)
  let s11 := singleBranchResult s10 (base + 8) (roleAtom parity .methylHydrogenB)
  let s12 := attachSingle s11 (base + 8) (roleAtom parity .methylHydrogenC)
  let r1 := appendFreshChild state.molecule external (roleAtom parity .backboneCarbon)
  have rc1 : r1.atomCount = base + 1 := by
    change (appendFreshChild state.molecule _ _).atomCount = _
    rw [appendFreshChild_atomCount]
    rfl
  have rows1 : s1.order.length = s1.atoms.length :=
    attachSingle_row_count state (parent) (roleAtom parity .backboneCarbon) rows
  have eq1 : s1.molecule = r1 :=
    fresh_transport state state.molecule (parent) (roleAtom parity .backboneCarbon) (by rfl) rows external.isLt
  let r2 := appendFreshChild r1 ⟨base, by omega⟩ (roleAtom parity .backboneHydrogen)
  have rc2 : r2.atomCount = base + 2 := by
    change (appendFreshChild r1 _ _).atomCount = _
    rw [appendFreshChild_atomCount, rc1]
  have rows2 : s2.order.length = s2.atoms.length :=
    branch_rows s1 (base) (roleAtom parity .backboneHydrogen) rows1
  have eq2 : s2.molecule = r2 :=
    branch_fresh_transport s1 r1 (base) (roleAtom parity .backboneHydrogen) eq1 rows1 (by omega)
  let r3 := appendFreshChild r2 ⟨base, by omega⟩ (roleAtom parity .bridgeCarbon)
  have rc3 : r3.atomCount = base + 3 := by
    change (appendFreshChild r2 _ _).atomCount = _
    rw [appendFreshChild_atomCount, rc2]
  have rows3 : s3.order.length = s3.atoms.length :=
    attachSingle_row_count opened (base) (roleAtom parity .bridgeCarbon) rows2
  have eq3 : s3.molecule = r3 :=
    fresh_transport opened r2 (base) (roleAtom parity .bridgeCarbon) eq2 rows2 (by omega)
  let r4 := appendFreshChild r3 ⟨base + 2, by omega⟩ (roleAtom parity .bridgeHydrogenA)
  have rc4 : r4.atomCount = base + 4 := by
    change (appendFreshChild r3 _ _).atomCount = _
    rw [appendFreshChild_atomCount, rc3]
  have rows4 : s4.order.length = s4.atoms.length :=
    branch_rows s3 (base + 2) (roleAtom parity .bridgeHydrogenA) rows3
  have eq4 : s4.molecule = r4 :=
    branch_fresh_transport s3 r3 (base + 2) (roleAtom parity .bridgeHydrogenA) eq3 rows3 (by omega)
  let r5 := appendFreshChild r4 ⟨base + 2, by omega⟩ (roleAtom parity .bridgeHydrogenB)
  have rc5 : r5.atomCount = base + 5 := by
    change (appendFreshChild r4 _ _).atomCount = _
    rw [appendFreshChild_atomCount, rc4]
  have rows5 : s5.order.length = s5.atoms.length :=
    branch_rows s4 (base + 2) (roleAtom parity .bridgeHydrogenB) rows4
  have eq5 : s5.molecule = r5 :=
    branch_fresh_transport s4 r4 (base + 2) (roleAtom parity .bridgeHydrogenB) eq4 rows4 (by omega)
  let r6 := appendFreshChild r5 ⟨base + 2, by omega⟩ (roleAtom parity .tagCarbon)
  have rc6 : r6.atomCount = base + 6 := by
    change (appendFreshChild r5 _ _).atomCount = _
    rw [appendFreshChild_atomCount, rc5]
  have rows6 : s6.order.length = s6.atoms.length :=
    attachSingle_row_count s5 (base + 2) (roleAtom parity .tagCarbon) rows5
  have eq6 : s6.molecule = r6 :=
    fresh_transport s5 r5 (base + 2) (roleAtom parity .tagCarbon) eq5 rows5 (by omega)
  let r7 := appendFreshChild r6 ⟨base + 5, by omega⟩ (roleAtom parity .tagHydrogen)
  have rc7 : r7.atomCount = base + 7 := by
    change (appendFreshChild r6 _ _).atomCount = _
    rw [appendFreshChild_atomCount, rc6]
  have rows7 : s7.order.length = s7.atoms.length :=
    branch_rows s6 (base + 5) (roleAtom parity .tagHydrogen) rows6
  have eq7 : s7.molecule = r7 :=
    branch_fresh_transport s6 r6 (base + 5) (roleAtom parity .tagHydrogen) eq6 rows6 (by omega)
  let r8 := appendFreshChild r7 ⟨base + 5, by omega⟩ (roleAtom parity .fluorine)
  have rc8 : r8.atomCount = base + 8 := by
    change (appendFreshChild r7 _ _).atomCount = _
    rw [appendFreshChild_atomCount, rc7]
  have rows8 : s8.order.length = s8.atoms.length :=
    branch_rows s7 (base + 5) (roleAtom parity .fluorine) rows7
  have eq8 : s8.molecule = r8 :=
    branch_fresh_transport s7 r7 (base + 5) (roleAtom parity .fluorine) eq7 rows7 (by omega)
  let r9 := appendFreshChild r8 ⟨base + 5, by omega⟩ (roleAtom parity .methylCarbon)
  have rc9 : r9.atomCount = base + 9 := by
    change (appendFreshChild r8 _ _).atomCount = _
    rw [appendFreshChild_atomCount, rc8]
  have rows9 : s9.order.length = s9.atoms.length :=
    attachSingle_row_count s8 (base + 5) (roleAtom parity .methylCarbon) rows8
  have eq9 : s9.molecule = r9 :=
    fresh_transport s8 r8 (base + 5) (roleAtom parity .methylCarbon) eq8 rows8 (by omega)
  let r10 := appendFreshChild r9 ⟨base + 8, by omega⟩ (roleAtom parity .methylHydrogenA)
  have rc10 : r10.atomCount = base + 10 := by
    change (appendFreshChild r9 _ _).atomCount = _
    rw [appendFreshChild_atomCount, rc9]
  have rows10 : s10.order.length = s10.atoms.length :=
    branch_rows s9 (base + 8) (roleAtom parity .methylHydrogenA) rows9
  have eq10 : s10.molecule = r10 :=
    branch_fresh_transport s9 r9 (base + 8) (roleAtom parity .methylHydrogenA) eq9 rows9 (by omega)
  let r11 := appendFreshChild r10 ⟨base + 8, by omega⟩ (roleAtom parity .methylHydrogenB)
  have rc11 : r11.atomCount = base + 11 := by
    change (appendFreshChild r10 _ _).atomCount = _
    rw [appendFreshChild_atomCount, rc10]
  have rows11 : s11.order.length = s11.atoms.length :=
    branch_rows s10 (base + 8) (roleAtom parity .methylHydrogenB) rows10
  have eq11 : s11.molecule = r11 :=
    branch_fresh_transport s10 r10 (base + 8) (roleAtom parity .methylHydrogenB) eq10 rows10 (by omega)
  let r12 := appendFreshChild r11 ⟨base + 8, by omega⟩ (roleAtom parity .methylHydrogenC)
  have eq12 : s12.molecule = r12 :=
    fresh_transport s11 r11 (base + 8) (roleAtom parity .methylHydrogenC) eq11 rows11 (by omega)
  have nativeFinal : (nativeBlockResult state parent parity).molecule = s12.molecule := by
    unfold nativeBlockResult
    rw [restore_molecule]
  have rawFinal : blockAppend state.molecule state.atoms.length rfl external parity = r12 := by
    unfold blockAppend
    rfl
  exact nativeFinal.trans (eq12.trans rawFinal.symm)

/-- Direct actual parsed block raw result, with no successful parser equation as an input. -/
theorem parse_native_block_raw (state : ParseState) (parent : Fin state.molecule.atomCount)
    (parity : TetrahedralInputParity) (spare : Nat)
    (rows : state.order.length = state.atoms.length) (current : state.current? = some parent.val) :
    (parseCharsFuel (spare + 41) (nativeBlockChars parity) state).map ParseState.molecule =
      Except.ok (blockAppend state.molecule state.atoms.length rfl parent parity) := by
  have parsed := parse_native_block parity (spare + 1) [] state parent.val current
  simp only [List.append_nil] at parsed
  change parseCharsFuel (spare + 41) (nativeBlockChars parity) state =
    Except.ok (nativeBlockResult state parent.val parity) at parsed
  rw [parsed]
  change Except.ok (nativeBlockResult state parent.val parity).molecule = _
  rw [native_block_molecule state parent parity rows]

theorem native_block_current (state : ParseState) (parent : Nat) (parity : TetrahedralInputParity) :
    (nativeBlockResult state parent parity).current? = some state.atoms.length := rfl

theorem native_block_branches (state : ParseState) (parent : Nat) (parity : TetrahedralInputParity) :
    (nativeBlockResult state parent parity).branches = state.branches := rfl

theorem native_block_rings (state : ParseState) (parent : Nat) (parity : TetrahedralInputParity) :
    (nativeBlockResult state parent parity).rings = state.rings := rfl

theorem native_block_pending (state : ParseState) (parent : Nat) (parity : TetrahedralInputParity) :
    (nativeBlockResult state parent parity).pendingBond? = none := rfl

theorem native_block_atom_count (state : ParseState) (parent : Nat) (parity : TetrahedralInputParity) :
    (nativeBlockResult state parent parity).atoms.length = state.atoms.length + 12 := by
  unfold nativeBlockResult
  dsimp only [attachSingle, singleBranchResult]
  simp only [List.length_append, List.length_singleton]

theorem native_block_rows (state : ParseState) (parent : Nat) (parity : TetrahedralInputParity)
    (rows : state.order.length = state.atoms.length) :
    (nativeBlockResult state parent parity).order.length =
      (nativeBlockResult state parent parity).atoms.length := by
  unfold nativeBlockResult
  dsimp only [singleBranchResult]
  repeat (first | apply attachSingle_row_count)
  exact rows


def nativeBlocksChars (ps : List TetrahedralInputParity) : List Char := ps.flatMap nativeBlockChars

def nativeBlocksResult : List TetrahedralInputParity → ParseState → Nat → ParseState
  | [], state, _ => state
  | parity :: rest, state, parent =>
      nativeBlocksResult rest (nativeBlockResult state parent parity) state.atoms.length

def nativeBlocksParent : List TetrahedralInputParity → ParseState → Nat → Nat
  | [], _, parent => parent
  | parity :: rest, state, parent =>
      nativeBlocksParent rest (nativeBlockResult state parent parity) state.atoms.length

theorem native_blocks_current (ps : List TetrahedralInputParity) (state : ParseState)
    (parent : Nat) (current : state.current? = some parent) :
    (nativeBlocksResult ps state parent).current? = some (nativeBlocksParent ps state parent) := by
  induction ps generalizing state parent with
  | nil => exact current
  | cons parity rest ih =>
      exact ih (nativeBlockResult state parent parity) state.atoms.length
        (native_block_current state parent parity)

theorem native_blocks_rows (ps : List TetrahedralInputParity) (state : ParseState)
    (parent : Nat) (rows : state.order.length = state.atoms.length) :
    (nativeBlocksResult ps state parent).order.length = (nativeBlocksResult ps state parent).atoms.length := by
  induction ps generalizing state parent with
  | nil => exact rows
  | cons parity rest ih =>
      exact ih (nativeBlockResult state parent parity) state.atoms.length
        (native_block_rows state parent parity rows)

theorem native_blocks_atom_count (ps : List TetrahedralInputParity) (state : ParseState) (parent : Nat) :
    (nativeBlocksResult ps state parent).atoms.length = state.atoms.length + 12 * ps.length := by
  induction ps generalizing state parent with
  | nil => simp [nativeBlocksResult]
  | cons parity rest ih =>
      rw [nativeBlocksResult, ih, native_block_atom_count]
      simp only [List.length_cons]
      omega

theorem native_blocks_parent_bound (ps : List TetrahedralInputParity) (state : ParseState)
    (parent : Nat) (bounded : parent < state.atoms.length) :
    nativeBlocksParent ps state parent < (nativeBlocksResult ps state parent).atoms.length := by
  induction ps generalizing state parent with
  | nil => exact bounded
  | cons parity rest ih =>
      exact ih (nativeBlockResult state parent parity) state.atoms.length (by
        rw [native_block_atom_count]
        omega)

theorem native_blocks_branches (ps : List TetrahedralInputParity) (state : ParseState) (parent : Nat) :
    (nativeBlocksResult ps state parent).branches = state.branches := by
  induction ps generalizing state parent with
  | nil => rfl
  | cons parity rest ih => rw [nativeBlocksResult, ih, native_block_branches]

theorem native_blocks_rings (ps : List TetrahedralInputParity) (state : ParseState) (parent : Nat) :
    (nativeBlocksResult ps state parent).rings = state.rings := by
  induction ps generalizing state parent with
  | nil => rfl
  | cons parity rest ih => rw [nativeBlocksResult, ih, native_block_rings]

/-- Arbitrary prefix, tail, fuel and size, from actual current-parent field alone. -/
theorem parse_native_blocks (ps : List TetrahedralInputParity) (fuel : Nat)
    (tail : List Char) (state : ParseState) (parent : Nat)
    (current : state.current? = some parent) :
    parseCharsFuel (fuel + 40 * ps.length) (nativeBlocksChars ps ++ tail) state =
      parseCharsFuel fuel tail (nativeBlocksResult ps state parent) := by
  induction ps generalizing state parent with
  | nil => simp only [nativeBlocksChars, List.flatMap_nil, List.length_nil,
      Nat.mul_zero, Nat.add_zero, List.nil_append, nativeBlocksResult]
  | cons parity rest ih =>
      simp only [nativeBlocksChars, List.flatMap_cons, List.append_assoc, List.length_cons]
      rw [show fuel + 40 * (rest.length + 1) = (fuel + 40 * rest.length) + 40 by omega]
      rw [parse_native_block parity (fuel + 40 * rest.length) _ state parent current]
      exact ih (nativeBlockResult state parent parity) state.atoms.length
        (native_block_current state parent parity)

private theorem blocks_raw_transport (ps : List TetrahedralInputParity) (a b : RawMolecule)
    (same : a = b) (parent : Nat) (first : parent < a.atomCount) (second : parent < b.atomCount) :
    blocksResult543 ps a ⟨parent, first⟩ = blocksResult543 ps b ⟨parent, second⟩ := by
  cases same
  rfl

private theorem parent_raw_transport (ps : List TetrahedralInputParity) (a b : RawMolecule)
    (same : a = b) (parent : Nat) (first : parent < a.atomCount) (second : parent < b.atomCount) :
    blocksParent543 ps a ⟨parent, first⟩ = blocksParent543 ps b ⟨parent, second⟩ := by
  cases same
  rfl

/-- Whole raw fold and actual terminal continuation parent, derived jointly from single-append joins. -/
theorem native_blocks_molecule_parent (ps : List TetrahedralInputParity) (state : ParseState)
    (parent : Fin state.molecule.atomCount) (rows : state.order.length = state.atoms.length) :
    (nativeBlocksResult ps state parent.val).molecule = blocksResult543 ps state.molecule parent ∧
      nativeBlocksParent ps state parent.val = blocksParent543 ps state.molecule parent := by
  induction ps generalizing state parent with
  | nil => exact ⟨rfl, rfl⟩
  | cons parity rest ih =>
      let next := nativeBlockResult state parent.val parity
      let rawNext := blockAppend state.molecule state.molecule.atomCount rfl parent parity
      have nextRows : next.order.length = next.atoms.length := native_block_rows state parent.val parity rows
      have nativeBound : state.atoms.length < next.molecule.atomCount := by
        change state.atoms.length < (nativeBlockResult state parent.val parity).atoms.length
        rw [native_block_atom_count]
        omega
      have rawBound : state.atoms.length < rawNext.atomCount := by
        rw [blockAppend_atomCount]
        change state.atoms.length < state.atoms.length + 12
        omega
      have nextEq : next.molecule = rawNext := native_block_molecule state parent parity rows
      have deeper := ih next ⟨state.atoms.length, nativeBound⟩ nextRows
      constructor
      · exact deeper.1.trans (blocks_raw_transport rest next.molecule rawNext nextEq
          state.atoms.length nativeBound rawBound)
      · exact deeper.2.trans (parent_raw_transport rest next.molecule rawNext nextEq
          state.atoms.length nativeBound rawBound)

/-- Closed native family source, internally constructed from the parity list. -/
def nativeFamilyState (ps : List TetrahedralInputParity) : ParseState :=
  let blocks := nativeBlocksResult ps initialHydrogenState 0
  attachSingle blocks (nativeBlocksParent ps initialHydrogenState 0) hydrogenSpec

def nativeFamilyChars (ps : List TetrahedralInputParity) : List Char :=
  atomChars .hydrogen ++ nativeBlocksChars ps ++ singleChars .hydrogen

def nativeFamilyString (ps : List TetrahedralInputParity) : String := String.ofList (nativeFamilyChars ps)

/-- Exact actual543 family raw record, atoms/bonds/all stored written rows included. -/
theorem native_family_molecule (ps : List TetrahedralInputParity) :
    (nativeFamilyState ps).molecule =
      TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords.familyRaw ps := by
  let blocks := nativeBlocksResult ps initialHydrogenState 0
  let raw := blocksResult543 ps family543Base baseFin
  let parent := nativeBlocksParent ps initialHydrogenState 0
  have folded := native_blocks_molecule_parent ps initialHydrogenState baseFin (by rfl)
  have same : blocks.molecule = raw := folded.1
  have rows : blocks.order.length = blocks.atoms.length := native_blocks_rows ps initialHydrogenState 0 (by rfl)
  have bounded : parent < raw.atomCount := by
    rw [← same]
    exact native_blocks_parent_bound ps initialHydrogenState 0 (by decide)
  have joined := fresh_transport blocks raw parent hydrogenSpec same rows bounded
  have parentEq : parent = blocksParent543 ps family543Base baseFin := folded.2
  change (attachSingle blocks parent hydrogenSpec).molecule =
    appendFreshChild raw
      ⟨blocksParent543 ps family543Base baseFin, blocksParent543_bounded ps family543Base baseFin⟩ hydrogenSpec
  have parentFinEq : (⟨parent, bounded⟩ : Fin raw.atomCount) =
      ⟨blocksParent543 ps family543Base baseFin,
        blocksParent543_bounded ps family543Base baseFin⟩ := by
    apply Fin.ext
    exact parentEq
  exact joined.trans (congrArg (fun actualParent => appendFreshChild raw actualParent hydrogenSpec)
    parentFinEq)

/-- An internally derived exact token budget, including the successful empty-tail recursion. -/
theorem parse_native_family_fuel (ps : List TetrahedralInputParity) (spare : Nat) :
    parseCharsFuel (spare + 40 * ps.length + 4) (nativeFamilyChars ps) {} =
      Except.ok (nativeFamilyState ps) := by
  simp only [nativeFamilyChars, List.append_assoc]
  rw [parse_family_atom_step .hydrogen (spare + 40 * ps.length + 3)]
  change parseCharsFuel (spare + 40 * ps.length + 3)
    (nativeBlocksChars ps ++ singleChars .hydrogen) initialHydrogenState = _
  rw [show spare + 40 * ps.length + 3 = (spare + 3) + 40 * ps.length by omega,
    parse_native_blocks ps (spare + 3) (singleChars .hydrogen) initialHydrogenState 0 rfl]
  have current := native_blocks_current ps initialHydrogenState 0 rfl
  change parseCharsFuel ((spare + 1) + 2) (singleChars .hydrogen ++ [])
    (nativeBlocksResult ps initialHydrogenState 0) = _
  rw [parse_single_chars_step .hydrogen (spare + 1) []
    (nativeBlocksResult ps initialHydrogenState 0) (nativeBlocksParent ps initialHydrogenState 0) current]
  rfl

theorem native_block_token_budget (parity : TetrahedralInputParity) :
    40 ≤ (nativeBlockChars parity).length := by
  cases parity <;> decide +kernel

theorem native_blocks_token_budget (ps : List TetrahedralInputParity) :
    40 * ps.length ≤ (nativeBlocksChars ps).length := by
  induction ps with
  | nil => decide
  | cons parity rest ih =>
      change 40 * (rest.length + 1) ≤ (nativeBlockChars parity ++ nativeBlocksChars rest).length
      rw [List.length_append]
      have budget := native_block_token_budget parity
      omega

theorem native_family_token_budget (ps : List TetrahedralInputParity) :
    40 * ps.length + 4 ≤ (nativeFamilyChars ps).length + 1 := by
  have budget := native_blocks_token_budget ps
  change 40 * ps.length + 4 ≤
    (atomChars .hydrogen ++ nativeBlocksChars ps ++ singleChars .hydrogen).length + 1
  simp only [List.length_append]
  change 40 * ps.length + 4 ≤ 3 + (nativeBlocksChars ps).length + 4 + 1
  omega

/-- Actual public character-count fuel, not an externally supplied successful parser budget. -/
theorem parse_native_family_chars (ps : List TetrahedralInputParity) :
    parseChars (nativeFamilyChars ps) {} = Except.ok (nativeFamilyState ps) := by
  have budget := native_family_token_budget ps
  let spare := (nativeFamilyChars ps).length + 1 - (40 * ps.length + 4)
  have fuel : (nativeFamilyChars ps).length + 1 = spare + 40 * ps.length + 4 := by
    dsimp only [spare]
    omega
  unfold parseChars
  rw [fuel]
  exact parse_native_family_fuel ps spare

theorem native_family_branches (ps : List TetrahedralInputParity) :
    (nativeFamilyState ps).branches = [] := by
  change (nativeBlocksResult ps initialHydrogenState 0).branches = []
  rw [native_blocks_branches]
  rfl

theorem native_family_rings (ps : List TetrahedralInputParity) :
    (nativeFamilyState ps).rings = [] := by
  change (nativeBlocksResult ps initialHydrogenState 0).rings = []
  rw [native_blocks_rings]
  rfl

theorem native_family_pending (ps : List TetrahedralInputParity) :
    (nativeFamilyState ps).pendingBond? = none := rfl

/-- Control-state updates leave the already established source-record invariant untouched.
Keeping this reduction abstract avoids unfolding twelve nested written-row updates. -/
private theorem restore_introduction (state : ParseState) (current : Option Nat)
    (branches : List Nat) :
    OpenSMILESIntroductionAppend.Valid
      ({ state with current? := current, branches := branches } : ParseState) ↔
      OpenSMILESIntroductionAppend.Valid state := Iff.rfl

/-- The twelve-role raw block preserves actual introduction history under the same real-parent
condition as its graph construction. No parser acceptance hypothesis is used. -/
theorem native_block_introduction (state : ParseState) (parent : Nat)
    (parity : TetrahedralInputParity) (valid : OpenSMILESIntroductionAppend.Valid state)
    (bound : parent < state.atoms.length) :
    OpenSMILESIntroductionAppend.Valid (nativeBlockResult state parent parity) := by
  let base := state.atoms.length
  let s1 := attachSingle state parent (roleAtom parity .backboneCarbon)
  let s2 := singleBranchResult s1 base (roleAtom parity .backboneHydrogen)
  let opened : ParseState := { s2 with branches := base :: state.branches }
  let s3 := attachSingle opened base (roleAtom parity .bridgeCarbon)
  let s4 := singleBranchResult s3 (base + 2) (roleAtom parity .bridgeHydrogenA)
  let s5 := singleBranchResult s4 (base + 2) (roleAtom parity .bridgeHydrogenB)
  let s6 := attachSingle s5 (base + 2) (roleAtom parity .tagCarbon)
  let s7 := singleBranchResult s6 (base + 5) (roleAtom parity .tagHydrogen)
  let s8 := singleBranchResult s7 (base + 5) (roleAtom parity .fluorine)
  let s9 := attachSingle s8 (base + 5) (roleAtom parity .methylCarbon)
  let s10 := singleBranchResult s9 (base + 8) (roleAtom parity .methylHydrogenA)
  let s11 := singleBranchResult s10 (base + 8) (roleAtom parity .methylHydrogenB)
  let s12 := attachSingle s11 (base + 8) (roleAtom parity .methylHydrogenC)
  have count1 : s1.atoms.length = base + 1 := by
    change (state.atoms ++ [_]).length = base + 1
    simp only [List.length_append, List.length_singleton, base]
  have valid1 : OpenSMILESIntroductionAppend.Valid s1 :=
    attachSingle_introduction state parent _ valid bound
  have count2 : s2.atoms.length = base + 2 := by
    change (s1.atoms ++ [_]).length = base + 2
    simp only [List.length_append, List.length_singleton, count1]
  have valid2 : OpenSMILESIntroductionAppend.Valid s2 :=
    singleBranchResult_introduction s1 base _ valid1 (by rw [count1]; omega)
  have openedValid : OpenSMILESIntroductionAppend.Valid opened :=
    (restore_introduction s2 s2.current? (base :: state.branches)).mpr valid2
  have count3 : s3.atoms.length = base + 3 := by
    change (s2.atoms ++ [_]).length = base + 3
    simp only [List.length_append, List.length_singleton, count2]
  have valid3 : OpenSMILESIntroductionAppend.Valid s3 :=
    attachSingle_introduction opened base _ openedValid
      (by change base < s2.atoms.length; rw [count2]; omega)
  have count4 : s4.atoms.length = base + 4 := by
    change (s3.atoms ++ [_]).length = base + 4
    simp only [List.length_append, List.length_singleton, count3]
  have valid4 : OpenSMILESIntroductionAppend.Valid s4 :=
    singleBranchResult_introduction s3 (base + 2) _ valid3 (by rw [count3]; omega)
  have count5 : s5.atoms.length = base + 5 := by
    change (s4.atoms ++ [_]).length = base + 5
    simp only [List.length_append, List.length_singleton, count4]
  have valid5 : OpenSMILESIntroductionAppend.Valid s5 :=
    singleBranchResult_introduction s4 (base + 2) _ valid4 (by rw [count4]; omega)
  have count6 : s6.atoms.length = base + 6 := by
    change (s5.atoms ++ [_]).length = base + 6
    simp only [List.length_append, List.length_singleton, count5]
  have valid6 : OpenSMILESIntroductionAppend.Valid s6 :=
    attachSingle_introduction s5 (base + 2) _ valid5 (by rw [count5]; omega)
  have count7 : s7.atoms.length = base + 7 := by
    change (s6.atoms ++ [_]).length = base + 7
    simp only [List.length_append, List.length_singleton, count6]
  have valid7 : OpenSMILESIntroductionAppend.Valid s7 :=
    singleBranchResult_introduction s6 (base + 5) _ valid6 (by rw [count6]; omega)
  have count8 : s8.atoms.length = base + 8 := by
    change (s7.atoms ++ [_]).length = base + 8
    simp only [List.length_append, List.length_singleton, count7]
  have valid8 : OpenSMILESIntroductionAppend.Valid s8 :=
    singleBranchResult_introduction s7 (base + 5) _ valid7 (by rw [count7]; omega)
  have count9 : s9.atoms.length = base + 9 := by
    change (s8.atoms ++ [_]).length = base + 9
    simp only [List.length_append, List.length_singleton, count8]
  have valid9 : OpenSMILESIntroductionAppend.Valid s9 :=
    attachSingle_introduction s8 (base + 5) _ valid8 (by rw [count8]; omega)
  have count10 : s10.atoms.length = base + 10 := by
    change (s9.atoms ++ [_]).length = base + 10
    simp only [List.length_append, List.length_singleton, count9]
  have valid10 : OpenSMILESIntroductionAppend.Valid s10 :=
    singleBranchResult_introduction s9 (base + 8) _ valid9 (by rw [count9]; omega)
  have count11 : s11.atoms.length = base + 11 := by
    change (s10.atoms ++ [_]).length = base + 11
    simp only [List.length_append, List.length_singleton, count10]
  have valid11 : OpenSMILESIntroductionAppend.Valid s11 :=
    singleBranchResult_introduction s10 (base + 8) _ valid10 (by rw [count10]; omega)
  have valid12 : OpenSMILESIntroductionAppend.Valid s12 :=
    attachSingle_introduction s11 (base + 8) _ valid11 (by rw [count11]; omega)
  unfold nativeBlockResult
  rw [restore_introduction]
  exact valid12

theorem native_blocks_introduction (ps : List TetrahedralInputParity)
    (state : ParseState) (parent : Nat) (valid : OpenSMILESIntroductionAppend.Valid state)
    (bound : parent < state.atoms.length) :
    OpenSMILESIntroductionAppend.Valid (nativeBlocksResult ps state parent) := by
  induction ps generalizing state parent with
  | nil => exact valid
  | cons parity rest ih =>
      exact ih (nativeBlockResult state parent parity) state.atoms.length
        (native_block_introduction state parent parity valid bound)
        (by rw [native_block_atom_count]; omega)

theorem native_family_introduction (ps : List TetrahedralInputParity) :
    OpenSMILESIntroductionAppend.Valid (nativeFamilyState ps) := by
  have initial : OpenSMILESIntroductionAppend.Valid initialHydrogenState := by
    refine ⟨rfl, rfl, ?_⟩
    intro index predecessor observed
    cases index <;> simp [initialHydrogenState] at observed
  exact attachSingle_introduction _ _ _
    (native_blocks_introduction ps initialHydrogenState 0 initial (by decide))
    (native_blocks_parent_bound ps initialHydrogenState 0 (by decide))

theorem native_family_introduction_valid (ps : List TetrahedralInputParity) :
    RawMolecule.parserIntroductionValid?
      (TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords.familyRaw ps) = true := by
  rw [← native_family_molecule]
  exact OpenSMILESIntroductionAppend.Valid.parserIntroductionValid _
    (native_family_introduction ps)

theorem syntax_single_role (parity : TetrahedralInputParity) (role : FamilyRole)
    (fuel : Nat) (tail : List Char) (count : Nat) (branches : List Nat) :
    openSMILESSyntaxValidFuel (fuel + 2) (singleRoleChars parity role ++ tail)
      (familySyntaxState count branches) =
      openSMILESSyntaxValidFuel fuel tail (familySyntaxState (count + 1) branches) :=
  syntax_single_chars_step (roleFamilyAtom parity role) fuel tail count branches

theorem syntax_branch_role (parity : TetrahedralInputParity) (role : FamilyRole)
    (fuel : Nat) (tail : List Char) (count : Nat) (branches : List Nat)
    (ready : branches.head? ≠ some count) :
    openSMILESSyntaxValidFuel (fuel + 4) (branchRoleChars parity role ++ tail)
      (familySyntaxState count branches) =
      openSMILESSyntaxValidFuel fuel tail (familySyntaxState (count + 1) branches) :=
  syntax_branch_chars_step (roleFamilyAtom parity role) fuel tail count branches ready

theorem syntax_native_block (parity : TetrahedralInputParity) (fuel : Nat)
    (tail : List Char) (count : Nat) :
    openSMILESSyntaxValidFuel (fuel + 40) (nativeBlockChars parity ++ tail)
      (familySyntaxState count) =
      openSMILESSyntaxValidFuel fuel tail (familySyntaxState (count + 12)) := by
  simp only [nativeBlockChars, List.append_assoc, List.cons_append]
  change openSMILESSyntaxValidFuel ((fuel + 38) + 2)
    (singleRoleChars parity .backboneCarbon ++ _) (familySyntaxState count) = _
  rw [syntax_single_role]
  change openSMILESSyntaxValidFuel ((fuel + 34) + 4)
    (branchRoleChars parity .backboneHydrogen ++ _) (familySyntaxState (count + 1)) = _
  rw [syntax_branch_role parity .backboneHydrogen (fuel + 34) _ (count + 1) [] (by simp)]
  change openSMILESSyntaxValidFuel ((fuel + 33) + 1) ('(' :: _)
    (familySyntaxState (count + 2)) = _
  rw [syntax_open_branch_step (fuel + 33) _ (count + 2) [] (by simp)]
  change openSMILESSyntaxValidFuel ((fuel + 31) + 2)
    (singleRoleChars parity .bridgeCarbon ++ _)
    (familySyntaxState (count + 2) [count + 2]) = _
  rw [syntax_single_role]
  change openSMILESSyntaxValidFuel ((fuel + 27) + 4)
    (branchRoleChars parity .bridgeHydrogenA ++ _)
    (familySyntaxState (count + 3) [count + 2]) = _
  rw [syntax_branch_role parity .bridgeHydrogenA (fuel + 27) _ (count + 3) [count + 2] (by simp)]
  change openSMILESSyntaxValidFuel ((fuel + 23) + 4)
    (branchRoleChars parity .bridgeHydrogenB ++ _)
    (familySyntaxState (count + 4) [count + 2]) = _
  rw [syntax_branch_role parity .bridgeHydrogenB (fuel + 23) _ (count + 4) [count + 2] (by simp)]
  change openSMILESSyntaxValidFuel ((fuel + 21) + 2)
    (singleRoleChars parity .tagCarbon ++ _)
    (familySyntaxState (count + 5) [count + 2]) = _
  rw [syntax_single_role]
  change openSMILESSyntaxValidFuel ((fuel + 17) + 4)
    (branchRoleChars parity .tagHydrogen ++ _)
    (familySyntaxState (count + 6) [count + 2]) = _
  rw [syntax_branch_role parity .tagHydrogen (fuel + 17) _ (count + 6) [count + 2] (by simp)]
  change openSMILESSyntaxValidFuel ((fuel + 13) + 4)
    (branchRoleChars parity .fluorine ++ _)
    (familySyntaxState (count + 7) [count + 2]) = _
  rw [syntax_branch_role parity .fluorine (fuel + 13) _ (count + 7) [count + 2] (by simp)]
  change openSMILESSyntaxValidFuel ((fuel + 11) + 2)
    (singleRoleChars parity .methylCarbon ++ _)
    (familySyntaxState (count + 8) [count + 2]) = _
  rw [syntax_single_role]
  change openSMILESSyntaxValidFuel ((fuel + 7) + 4)
    (branchRoleChars parity .methylHydrogenA ++ _)
    (familySyntaxState (count + 9) [count + 2]) = _
  rw [syntax_branch_role parity .methylHydrogenA (fuel + 7) _ (count + 9) [count + 2] (by simp)]
  change openSMILESSyntaxValidFuel ((fuel + 3) + 4)
    (branchRoleChars parity .methylHydrogenB ++ _)
    (familySyntaxState (count + 10) [count + 2]) = _
  rw [syntax_branch_role parity .methylHydrogenB (fuel + 3) _ (count + 10) [count + 2] (by simp)]
  change openSMILESSyntaxValidFuel ((fuel + 1) + 2)
    (singleRoleChars parity .methylHydrogenC ++ _)
    (familySyntaxState (count + 11) [count + 2]) = _
  rw [syntax_single_role]
  change openSMILESSyntaxValidFuel (fuel + 1) (')' :: tail)
    (familySyntaxState (count + 12) [count + 2]) = _
  rw [syntax_close_branch_step fuel tail (count + 12) (count + 2) [] (by omega)]

theorem syntax_native_blocks (ps : List TetrahedralInputParity) (fuel : Nat)
    (tail : List Char) (count : Nat) :
    openSMILESSyntaxValidFuel (fuel + 40 * ps.length) (nativeBlocksChars ps ++ tail)
      (familySyntaxState count) =
      openSMILESSyntaxValidFuel fuel tail (familySyntaxState (count + 12 * ps.length)) := by
  induction ps generalizing count with
  | nil => rfl
  | cons parity rest ih =>
      simp only [nativeBlocksChars] at ih
      simp only [nativeBlocksChars, List.flatMap_cons, List.length_cons, List.append_assoc]
      rw [show fuel + 40 * (rest.length + 1) = (fuel + 40 * rest.length) + 40 by omega,
        syntax_native_block, ih]
      congr 2
      omega

theorem syntax_native_family_fuel (ps : List TetrahedralInputParity) (spare : Nat) :
    openSMILESSyntaxValidFuel (spare + 40 * ps.length + 4) (nativeFamilyChars ps) {} = true := by
  simp only [nativeFamilyChars, List.append_assoc]
  rw [syntax_family_atom_step .hydrogen (spare + 40 * ps.length + 3)]
  change openSMILESSyntaxValidFuel (spare + 40 * ps.length + 3)
    (nativeBlocksChars ps ++ singleChars .hydrogen) (familySyntaxState 1) = _
  rw [show spare + 40 * ps.length + 3 = (spare + 3) + 40 * ps.length by omega,
    syntax_native_blocks]
  change openSMILESSyntaxValidFuel ((spare + 1) + 2) (singleChars .hydrogen ++ [])
    (familySyntaxState (1 + 12 * ps.length)) = _
  rw [syntax_single_chars_step]
  rfl

theorem native_family_syntax_valid (ps : List TetrahedralInputParity) :
    openSMILESSyntaxValid (nativeFamilyString ps) = true := by
  have budget := native_family_token_budget ps
  let spare := (nativeFamilyChars ps).length + 1 - (40 * ps.length + 4)
  have fuel : (nativeFamilyChars ps).length + 1 = spare + 40 * ps.length + 4 := by
    dsimp [spare]
    omega
  unfold openSMILESSyntaxValid nativeFamilyString
  rw [String.toList_ofList, fuel]
  exact syntax_native_family_fuel ps spare

/-- Whole STRING parser and finalizer, exact independently constructed543 raw family.
No parser success, desired raw/output/table equality or acceptance input is provided. -/
theorem parse_native_family_string (ps : List TetrahedralInputParity) :
    parseOpenSMILES (nativeFamilyString ps) =
      Except.ok (TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords.familyRaw ps) := by
  let raw := TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords.familyRaw ps
  have single : raw.normalizeUnspecifiedBonds = raw :=
    normalize_eq_of_all_single raw
      (TetraStereo.UniversalProof.SecondSphereFamilyPhysicalInstantiation.familyRaw_all_single ps)
  have admitted : raw.admissible? = true :=
    (RawMolecule.admissible?_eq_true_iff raw).mpr
      ⟨TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords.familyRaw_wellFormed ps,
       TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords.familyRaw_bondRecordsUnique ps⟩
  have finalized : finalizeParseState (nativeFamilyState ps) = .ok raw := by
    unfold finalizeParseState
    rw [native_family_branches, native_family_rings, native_family_pending]
    rw [if_pos rfl, if_pos rfl, if_pos rfl, native_family_molecule]
    change (if raw.normalizeUnspecifiedBonds.admissible? then
      Except.ok raw.normalizeUnspecifiedBonds else _) = _
    rw [single, admitted]
    rfl
  apply parseOpenSMILES_eq_ok_of _ (nativeFamilyState ps) _
    (native_family_syntax_valid ps) _ finalized (native_family_introduction_valid ps)
  simpa only [nativeFamilyString, String.toList_ofList] using parse_native_family_chars ps

end TetraStereo.UniversalProof.SecondSphereNativeBlockParser
