import TetraStereo.OneCenter.LocalizedMarkedFrameCalibration
import TetraStereo.OneCenter.CIPAuthoritativeRule6Scheduler
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Transport from molecular frame configurations

The geometric observations needed by recursive marked recalculation are the handednesses of
its actual occurrence frames. Agreement on arbitrary quadruples of atoms is unnecessary.
The ordering permutations are derived from the production sorting calls. Missing coordinates,
degenerate frames and refusals are retained. This is an invariance theorem for the experimental
constructor, not chemical completeness or a production/specification agreement theorem.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedConfigurationTransport

open LocalizedGenericMarkedRecalculation CertifiedLocalizedCIPInput
open LocalizedMarkedFrameCalibration Rule6HandednessSemantics
open OccurrenceRule6RankingPermutation DeclarativeCIP.ProductionOccurrenceRules456

private theorem mapM_none_of_missing (geom : Geometry) (atoms : List Nat) (atom : Nat)
    (member : atom ∈ atoms) (missing : geom atom = none) : atoms.mapM geom = none := by
  induction atoms with
  | nil => simp at member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | member
      · simp [List.mapM_cons, missing]
      · rw [List.mapM_cons, ih member]
        cases geom head <;> rfl

theorem readback_none_of_missing (geom : Geometry) (atoms : List Nat) (atom : Nat)
    (member : atom ∈ atoms) (missing : geom atom = none) : readback? geom atoms = none := by
  simp [readback?, mapM_none_of_missing geom atoms atom member missing]

/-- Frame permutation law without coordinate-completeness or nondegeneracy assumptions. -/
theorem reordered_readback_partial (geom : Geometry) (atoms : Fin 4 → Nat)
    (positions : List Nat) (permutation : positions.Perm [0, 1, 2, 3]) :
    (atomsAt? [atoms 0, atoms 1, atoms 2, atoms 3] positions).bind (readback? geom) =
      if RawMolecule.permutationIsEven positions then
        readback? geom [atoms 0, atoms 1, atoms 2, atoms 3]
      else (readback? geom [atoms 0, atoms 1, atoms 2, atoms 3]).map RS.swap := by
  classical
  by_cases complete : ∀ i, (geom (atoms i)).isSome
  · let points : Fin 4 → CartesianPoint3 := fun i => (geom (atoms i)).get (complete i)
    have coordinates : ∀ i, geom (atoms i) = some (points i) := by
      intro i
      exact (Option.eq_some_iff_get_eq).mpr ⟨complete i, rfl⟩
    rw [reordered_readback geom atoms points coordinates positions permutation,
      readback_coordinates geom atoms points coordinates]
  · push_neg at complete
    obtain ⟨i, missing⟩ := complete
    have absent : geom (atoms i) = none := Option.not_isSome_iff_eq_none.mp missing
    let ordering := finFourEquivOfPermutationList positions (by simpa using permutation)
    have code : finFourPermutationList ordering = positions :=
      finFourPermutationList_equivOfPermutationList positions _
    have before : atoms i ∈ [atoms 0, atoms 1, atoms 2, atoms 3] := by
      fin_cases i <;> simp
    have after : atoms i ∈
        [atoms (ordering 0), atoms (ordering 1), atoms (ordering 2), atoms (ordering 3)] := by
      obtain ⟨j, rfl⟩ := ordering.surjective i
      fin_cases j <;> simp
    rw [← code, select_permutation]
    simp only [Option.bind_some]
    rw [readback_none_of_missing geom _ _ before absent,
      readback_none_of_missing geom _ _ after absent]
    split <;> rfl

theorem frame_length (mol : RawMolecule) (node : RawMolecule.CanonicalBranchNode)
    (atoms : List Nat) (frame : frameAtoms? mol node = some atoms) : atoms.length = 4 := by
  obtain ⟨roots, computed, rfl⟩ := Option.map_eq_some_iff.mp frame
  simpa [frameAtomsOf] using
    AuthoritativeCIPRule6Scheduler.occurrenceLigandFrame?_result_length mol node roots computed

/-- One original-frame reading per actual occurrence, including missing/zero-volume readings. -/
def SameFrameConfigurations (mol : RawMolecule) (first second : Geometry) : Prop :=
  ∀ node atoms, frameAtoms? mol node = some atoms → readback? first atoms = readback? second atoms

theorem SameFrameConfigurations.mirror {mol : RawMolecule} {first second : Geometry}
    (agree : SameFrameConfigurations mol first second) :
    SameFrameConfigurations mol (mirror first) (mirror second) := by
  intro node atoms frame
  rw [readback_mirror, readback_mirror, agree node atoms frame]

theorem reordered_frame_congr_at (mol : RawMolecule) {first second : Geometry}
    (node : RawMolecule.CanonicalBranchNode)
    (agree : ∀ atoms, frameAtoms? mol node = some atoms → readback? first atoms = readback? second atoms)
    (atoms positions : List Nat)
    (frame : frameAtoms? mol node = some atoms) (permutation : positions.Perm [0, 1, 2, 3]) :
    (atomsAt? atoms positions).bind (readback? first) =
      (atomsAt? atoms positions).bind (readback? second) := by
  have length := frame_length mol node atoms frame
  rcases atoms with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, tail⟩⟩⟩⟩ <;> simp at length
  subst tail
  have calibration := agree [a, b, c, d] frame
  have expand (geom : Geometry) :
      (atomsAt? [a, b, c, d] positions).bind (readback? geom) =
        if RawMolecule.permutationIsEven positions then readback? geom [a, b, c, d]
        else (readback? geom [a, b, c, d]).map RS.swap := by
    simpa using reordered_readback_partial geom ![a, b, c, d] positions permutation
  rw [expand first, expand second, calibration]

theorem reordered_frame_congr (mol : RawMolecule) {first second : Geometry}
    (agree : SameFrameConfigurations mol first second)
    (node : RawMolecule.CanonicalBranchNode) (atoms positions : List Nat)
    (frame : frameAtoms? mol node = some atoms) (permutation : positions.Perm [0, 1, 2, 3]) :
    (atomsAt? atoms positions).bind (readback? first) =
      (atomsAt? atoms positions).bind (readback? second) :=
  reordered_frame_congr_at mol node (agree node) atoms positions frame permutation

theorem ordinary_positions_perm (mol : RawMolecule) (fuel : Nat) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) (sorted : List Nat)
    (adjacent : List (Option Ordering))
    (computed : ordinary? mol fuel state node = some (sorted, adjacent)) :
    sorted.Perm [0, 1, 2, 3] := by
  cases frame : occurrenceLigandFrame? mol node with
  | none => simp [ordinary?, frame] at computed
  | some roots =>
      cases sorting : sortRule6InitialPositions? (mol := mol) state fuel roots
          (List.range roots.length) with
      | none => simp [ordinary?, frame, sorting] at computed
      | some result =>
          cases comparison : compareRule6InitialAdjacent? (mol := mol) state fuel roots result with
          | none => simp [ordinary?, frame, sorting, comparison] at computed
          | some observations =>
              simp [ordinary?, frame, sorting, comparison] at computed
              obtain ⟨rfl, rfl⟩ := computed
              have perm := (sortRule6InitialDerivation_of_production state fuel roots _ _ sorting).perm
              simpa [AuthoritativeCIPRule6Scheduler.occurrenceLigandFrame?_result_length
                mol node roots frame] using perm

theorem markedReadback_congr_at (mol : RawMolecule) (fuel : Nat) {first second : Geometry}
    (node : RawMolecule.CanonicalBranchNode)
    (agree : ∀ atoms, frameAtoms? mol node = some atoms → readback? first atoms = readback? second atoms)
    (state : OccurrenceAuxState) (mark : Nat) :
    markedReadback? mol fuel first state node mark =
      markedReadback? mol fuel second state node mark := by
  cases frame : frameAtoms? mol node with
  | none => simp [markedReadback?, frame]
  | some atoms =>
      cases computed : marked? mol fuel state node mark with
      | none => simp [markedReadback?, frame, computed]
      | some ranking =>
          by_cases unique : ranking.unique = true
          · have reading := reordered_frame_congr_at mol node agree atoms ranking.positions frame
              (marked_positions_perm mol state fuel node mark ranking computed)
            simpa [markedReadback?, frame, computed, rankedAtoms?, unique, atomsAt?] using reading
          · simp [markedReadback?, frame, computed, rankedAtoms?, unique]

theorem markedReadback_congr (mol : RawMolecule) (fuel : Nat) {first second : Geometry}
    (agree : SameFrameConfigurations mol first second) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) (mark : Nat) :
    markedReadback? mol fuel first state node mark =
      markedReadback? mol fuel second state node mark :=
  markedReadback_congr_at mol fuel node (agree node) state mark

theorem rawStep_congr_at (mol : RawMolecule) (fuel : Nat) {first second : Geometry}
    (node : RawMolecule.CanonicalBranchNode)
    (agree : ∀ atoms, frameAtoms? mol node = some atoms → readback? first atoms = readback? second atoms)
    (state : OccurrenceAuxState) (ctx : Option Nat)
    (underFirst underSecond : Nat → OccurrenceAuxState)
    (under : ∀ mark, underFirst mark = underSecond mark) :
    rawStep? mol fuel first state ctx node underFirst =
      rawStep? mol fuel second state ctx node underSecond := by
  rw [show underFirst = underSecond from funext under]
  have marked : ∀ s r, markedReadback? mol fuel first s node r =
      markedReadback? mol fuel second s node r := fun s r =>
    markedReadback_congr_at mol fuel node agree s r
  cases frame : frameAtoms? mol node with
  | none => simp [rawStep?, frame]
  | some atoms =>
      cases computed : ordinary? mol fuel state node with
      | none => simp [rawStep?, frame, computed]
      | some pair =>
          obtain ⟨sorted, adjacent⟩ := pair
          by_cases bad : ¬ atoms.Nodup ∨ consistent adjacent = false
          · simp [rawStep?, frame, computed, bad]
          · by_cases strong : strict adjacent = true
            · simpa [rawStep?, frame, computed, bad, strong] using
                reordered_frame_congr_at mol node agree atoms sorted frame
                  (ordinary_positions_perm mol fuel state node sorted adjacent computed)
            · simp [rawStep?, frame, computed, bad, strong, marked]

theorem rawStep_congr (mol : RawMolecule) (fuel : Nat) {first second : Geometry}
    (agree : SameFrameConfigurations mol first second) (state : OccurrenceAuxState)
    (ctx : Option Nat) (node : RawMolecule.CanonicalBranchNode)
    (underFirst underSecond : Nat → OccurrenceAuxState)
    (under : ∀ mark, underFirst mark = underSecond mark) :
    rawStep? mol fuel first state ctx node underFirst =
      rawStep? mol fuel second state ctx node underSecond :=
  rawStep_congr_at mol fuel node (agree node) state ctx underFirst underSecond under

theorem rawWith_congr (mol : RawMolecule) (fuel : Nat) {first second : Geometry}
    (agree : SameFrameConfigurations mol first second) (state : OccurrenceAuxState)
    (ctx : Option Nat) (node : RawMolecule.CanonicalBranchNode)
    (subFirst subSecond : Geometry → OccurrenceAuxState → Option Nat →
      RawMolecule.CanonicalBranchNode → OccurrenceAuxState)
    (sub : ∀ s x child, subFirst first s x child = subSecond second s x child) :
    rawWith? mol fuel first state ctx node subFirst =
      rawWith? mol fuel second state ctx node subSecond := by
  apply rawStep_congr mol fuel agree
  intro mark
  unfold underWith
  exact flatMap_congr_mem _ _ _ fun child _ => sub state (some mark) child

/-- All generated auxiliary facts depend only on the molecular frame configurations. -/
theorem facts_congr (mol : RawMolecule) (fuel depth : Nat) :
    ∀ first second, SameFrameConfigurations mol first second →
      ∀ (state : OccurrenceAuxState) (ctx : Option Nat)
        (node : RawMolecule.CanonicalBranchNode),
      facts mol fuel depth first state ctx node = facts mol fuel depth second state ctx node := by
  induction depth with
  | zero => intros; rfl
  | succ depth ih =>
      intro first second agree state ctx node
      have descriptor : descriptor? mol fuel depth first state ctx node =
          descriptor? mol fuel depth second state ctx node := by
        unfold descriptor? descriptorWith?
        rw [rawWith_congr mol fuel agree state ctx node _ _ (ih first second agree),
          rawWith_congr mol fuel agree.mirror state ctx node _ _
            (ih (mirror first) (mirror second) agree.mirror)]
      rw [facts_succ, facts_succ, descriptor]
      congr 1
      exact flatMap_congr_mem _ _ _ fun child _ => ih first second agree state ctx child

theorem descriptor_congr (mol : RawMolecule) (fuel depth : Nat) {first second : Geometry}
    (agree : SameFrameConfigurations mol first second) (state : OccurrenceAuxState)
    (ctx : Option Nat) (node : RawMolecule.CanonicalBranchNode) :
    descriptor? mol fuel depth first state ctx node =
      descriptor? mol fuel depth second state ctx node := by
  unfold descriptor? descriptorWith?
  rw [rawWith_congr mol fuel agree state ctx node _ _ (facts_congr mol fuel depth _ _ agree),
    rawWith_congr mol fuel agree.mirror state ctx node _ _
      (facts_congr mol fuel depth _ _ agree.mirror)]

theorem assignCenter_congr (mol : RawMolecule) (fuel center : Nat) {first second : Geometry}
    (agree : SameFrameConfigurations mol first second) :
    assignCenter? mol fuel first center = assignCenter? mol fuel second center :=
  descriptor_congr mol fuel _ agree [] none _

/-- The entire emitted report, including its omissions, is determined by frame configurations. -/
theorem assign_congr (mol : RawMolecule) {first second : Geometry}
    (agree : SameFrameConfigurations mol first second) : assign mol first = assign mol second := by
  have centers : assignCenter? mol (comparatorFuel mol) first =
      assignCenter? mol (comparatorFuel mol) second := by
    funext center
    exact assignCenter_congr mol _ center agree
  unfold assign
  rw [centers]

end TetraStereo.OneCenter.LocalizedMarkedConfigurationTransport

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedConfigurationTransport.reordered_readback_partial
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedConfigurationTransport.reordered_frame_congr
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedConfigurationTransport.ordinary_positions_perm
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedConfigurationTransport.markedReadback_congr
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedConfigurationTransport.rawStep_congr
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedConfigurationTransport.facts_congr
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedConfigurationTransport.descriptor_congr
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedConfigurationTransport.assign_congr

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedConfigurationTransport.rawStep_congr_at
