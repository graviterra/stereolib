/-
COORDINATION: Consumer is the live owner of `LocalizedRetainedArmExpansion`. Do not edit that
file and do not rebuild its cursor map here. This module is only the local child-law recipe
for a real focus. Feed `cutChild_iff_cutStep` to `RootedDigraph.LocalChildCovering`
(`child_map`, `child_surjective`, `sibling_injective`) and use the existing
`realCut_unique_parent` as `target_unique_parent`. `LocalChildCovering.toIso` is the
approved global step. `incoming` stays the supplied `RealCutAnchor` child, inward or outward;
this file never replaces it by `focus.dropLast` and never assumes the molecule is acyclic.
-/
import TetraStereo.OneCenter.DeclarativeCIPRetainedCutArm
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

/-!
# Local traversal law for a retained cut arm

`realCutRetainedArm` deletes the subtree of one reroot-child of a real focus. That child is
the traversal predecessor at the focus. It may be the original carrier parent or an outward
carrier child; `RealCutAnchor` is the only restriction.

At every kept cursor, a cut step is exactly one undirected carrier edge that does not return
to that predecessor. Walking those steps from the focus stays inside `KeptAfterCut`, so a
bridge does not re-prove the global subtree condition at each cursor. Labels, provenance, and
ring distance are the carrier label; digraph depth is the full-reroot depth.
-/

namespace TetraStereo.OneCenter.DeclarativeCIP
namespace RetainedCutArmTraversal

open RetainedOccurrenceCarrier
open RetainedCutArm
open scoped Classical

noncomputable section

universe u

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]

variable {molecule : MoleculeGraph Atom} {root : Atom}

/-- Undirected edge of the outer-root carrier tree. -/
def CarrierAdjacent (a b : CarrierNode Atom) : Prop :=
  CarrierNode.Child a b ∨ CarrierNode.Child b a

/-- Predecessor excluded by a nonbacktracking step.
At the focus this is the supplied incoming anchor, whichever arm child it is.
Elsewhere it is the unique full-reroot parent. -/
def ExcludedPredecessor (focus : List Atom) (incoming : Option (Nodes molecule root))
    (cursor step : Nodes molecule root) : Prop :=
  (cursor.1 = .real focus ∧ incoming = some step) ∨
    (cursor.1 ≠ .real focus ∧ armChild focus step cursor)

/-- One allowed traversal step: a carrier edge that does not return to the predecessor. -/
def CutStep (focus : List Atom) (incoming : Option (Nodes molecule root))
    (cursor step : Nodes molecule root) : Prop :=
  CarrierAdjacent cursor.1 step.1 ∧ ¬ ExcludedPredecessor focus incoming cursor step

variable {focus : List Atom}

theorem armChild_carrierAdjacent {parent node : Nodes molecule root}
    (hchild : armChild focus parent node) : CarrierAdjacent parent.1 node.1 := by
  cases node with
  | mk val hval =>
      cases val with
      | ring path atom =>
          have hne : CarrierNode.ring path atom ≠ CarrierNode.real focus := by
            intro h
            cases h
          unfold armChild rawNewParent at hchild
          rw [if_neg hne] at hchild
          have hparent : parent.1 = .real path := Option.some_inj.mp hchild.symm
          exact Or.inl (by rw [hparent]; rfl)
      | real path =>
          have hne : CarrierNode.real path ≠ CarrierNode.real focus := by
            intro heq
            cases heq
            simp [armChild, rawNewParent_focus] at hchild
          unfold armChild rawNewParent at hchild
          rw [if_neg hne] at hchild
          by_cases hpre : path.length < focus.length ∧ focus.take path.length = path
          · simp [hpre] at hchild
            refine Or.inr ?_
            rw [← hchild]
            exact ⟨focus[path.length], rfl⟩
          · simp [hpre] at hchild
            refine Or.inl ?_
            rw [← hchild]
            exact ⟨path.getLast (SimpleFrom.ne_nil hval),
              (List.dropLast_concat_getLast (SimpleFrom.ne_nil hval)).symm⟩

theorem not_armChild_both (hfocus : SimpleFrom molecule root focus)
    {a b : Nodes molecule root} (hab : armChild focus a b) (hba : armChild focus b a) : False := by
  have habD := (realRetainedArm molecule root hfocus).child_depth hab
  have hbaD := (realRetainedArm molecule root hfocus).child_depth hba
  omega

theorem focus_carrierAdjacent_iff (hfocus : SimpleFrom molecule root focus)
    (node : Nodes molecule root) :
    CarrierAdjacent (.real focus) node.1 ↔
      CarrierNode.Child (.real focus) node.1 ∨
        (1 < focus.length ∧ node.1 = .real focus.dropLast) := by
  constructor
  · intro hadj
    rcases hadj with hto | hfrom
    · exact Or.inl hto
    · cases node with
      | mk val hv =>
          cases val with
          | ring _ _ => simp [CarrierNode.Child] at hfrom
          | real path =>
              obtain ⟨atom, hpath⟩ := hfrom
              have hdrop : focus.dropLast = path := by
                rw [hpath]
                exact List.dropLast_concat
              have hlen : 1 < focus.length := by
                have hpos : 0 < path.length :=
                  List.length_pos_iff.mpr (SimpleFrom.ne_nil hv)
                have hlenEq : focus.length = path.length + 1 := by
                  simpa [List.length_append] using congrArg List.length hpath
                omega
              exact Or.inr ⟨hlen, by simp [hdrop]⟩
  · intro h
    rcases h with hto | ⟨_, hparent⟩
    · exact Or.inl hto
    · have happ : focus = focus.dropLast ++
          [focus.getLast (SimpleFrom.ne_nil hfocus)] :=
        (List.dropLast_concat_getLast (SimpleFrom.ne_nil hfocus)).symm
      have hchild : CarrierNode.Child (.real focus.dropLast) (.real focus) :=
        ⟨focus.getLast (SimpleFrom.ne_nil hfocus), happ⟩
      exact Or.inr (by simpa [hparent] using hchild)

theorem focus_armChild_iff_carrierAdjacent (hfocus : SimpleFrom molecule root focus)
    (node : Nodes molecule root) :
    armChild focus ⟨.real focus, hfocus⟩ node ↔ CarrierAdjacent (.real focus) node.1 := by
  rw [armChild_focus_iff hfocus node]
  exact (focus_carrierAdjacent_iff hfocus node).symm

theorem rawNewParent_strictPrefix {path : List Atom}
    (hpre : path.length < focus.length ∧ focus.take path.length = path)
    (hne : (CarrierNode.real path : CarrierNode Atom) ≠ .real focus) :
    rawNewParent focus (.real path) = some (.real (path ++ [focus[path.length]])) := by
  unfold rawNewParent
  rw [if_neg hne]
  simp [hpre]

theorem rawNewParent_notPrefix {path : List Atom}
    (hne : (CarrierNode.real path : CarrierNode Atom) ≠ .real focus)
    (hpre : ¬ (path.length < focus.length ∧ focus.take path.length = path)) :
    rawNewParent focus (.real path) = some (.real path.dropLast) := by
  unfold rawNewParent
  rw [if_neg hne]
  simp [hpre]

/-- A carrier neighbor of a non-focus node, other than its reroot parent, is its reroot child. -/
theorem armChild_of_carrierAdjacent_not_parent
    {cursor step : Nodes molecule root}
    (hne : cursor.1 ≠ .real focus)
    (hadj : CarrierAdjacent cursor.1 step.1)
    (hnot : ¬ armChild focus step cursor) :
    armChild focus cursor step := by
  rcases hadj with hto | hfrom
  · cases cursor with
    | mk cval hc =>
        cases step with
        | mk sval hs =>
            cases cval with
            | ring _ _ => simp [CarrierNode.Child] at hto
            | real p =>
                cases sval with
                | ring path atom =>
                    cases hto
                    have hring : CarrierNode.ring p atom ≠ CarrierNode.real focus := by
                      intro h
                      cases h
                    have hraw : rawNewParent focus (.ring p atom) = some (.real p) := by
                      unfold rawNewParent
                      rw [if_neg hring]
                    exact hraw
                | real s =>
                    obtain ⟨atom, hs⟩ := hto
                    by_cases hpre : s.length < focus.length ∧ focus.take s.length = s
                    · have hpLen : p.length < focus.length := by
                        have hsLen : s.length = p.length + 1 := by
                          simpa [hs, List.length_append] using congrArg List.length hs
                        omega
                      have hptake : focus.take p.length = p := by
                        have htakeS : focus.take s.length = s := hpre.2
                        have hsTake : s.take p.length = p := by
                          rw [hs]
                          exact List.take_left
                        have hmin : min p.length s.length = p.length := by
                          have : p.length + 1 = s.length := by
                            simpa [hs, List.length_append] using congrArg List.length hs
                          omega
                        calc
                          focus.take p.length = (focus.take s.length).take p.length := by
                            rw [List.take_take, hmin]
                          _ = s.take p.length := by rw [htakeS]
                          _ = p := hsTake
                      have hpNe : (CarrierNode.real p : CarrierNode Atom) ≠ .real focus := by
                        intro heq
                        exact hne (by simp [heq])
                      have hraw := rawNewParent_strictPrefix (focus := focus)
                        ⟨hpLen, hptake⟩ hpNe
                      have hatom : focus[p.length] = atom := by
                        have hsucc : focus.take (p.length + 1) = p ++ [atom] := by
                          have hlenS : s.length = p.length + 1 := by
                            simpa [hs, List.length_append] using congrArg List.length hs
                          simpa [hs, hlenS] using hpre.2
                        have hsplit : focus.take (p.length + 1) = p ++ [focus[p.length]] := by
                          rw [List.take_succ_eq_append_getElem hpLen, hptake]
                        have happ : p ++ [focus[p.length]] = p ++ [atom] := by
                          rw [← hsplit, hsucc]
                        simpa using List.append_cancel_left happ
                      have hparent : rawNewParent focus (.real p) = some (.real s) := by
                        simpa [hs, hatom] using hraw
                      exact (hnot hparent).elim
                    · by_cases hsFocus : CarrierNode.real s = CarrierNode.real focus
                      · cases hsFocus
                        exfalso
                        apply hnot
                        unfold armChild rawNewParent
                        have hpNe : CarrierNode.real p ≠ CarrierNode.real focus := by
                          intro heq
                          cases heq
                          have hlen := congrArg List.length hs
                          simp [List.length_append] at hlen
                        rw [if_neg hpNe]
                        simp [hs]
                      · have hraw := rawNewParent_notPrefix (focus := focus) hsFocus hpre
                        simpa [hs, List.dropLast_concat] using hraw
  · cases cursor with
    | mk cval hc =>
        cases cval with
        | ring path atom =>
            cases step with
            | mk sval hs =>
                cases sval with
                | ring _ _ => simp [CarrierNode.Child] at hfrom
                | real q =>
                    cases hfrom
                    have hring : (CarrierNode.ring path atom : CarrierNode Atom) ≠ .real focus := by
                      intro h
                      cases h
                    have hraw : rawNewParent focus (.ring path atom) = some (.real path) := by
                      unfold rawNewParent
                      rw [if_neg hring]
                    exact (hnot hraw).elim
        | real p =>
            cases step with
            | mk sval hs =>
                cases sval with
                | ring _ _ => simp [CarrierNode.Child] at hfrom
                | real s =>
                    obtain ⟨atom, hp⟩ := hfrom
                    by_cases hpre : p.length < focus.length ∧ focus.take p.length = p
                    · have hpNe : (CarrierNode.real p : CarrierNode Atom) ≠ .real focus := hne
                      have hrawP := rawNewParent_strictPrefix (focus := focus) hpre hpNe
                      have hsLen : s.length < focus.length := by
                        have : p.length = s.length + 1 := by
                          simpa [hp, List.length_append] using congrArg List.length hp
                        omega
                      have hstake : focus.take s.length = s := by
                        have htakeP : focus.take p.length = p := hpre.2
                        have hpTake : p.take s.length = s := by
                          rw [hp]
                          exact List.take_left
                        have hmin : min s.length p.length = s.length := by
                          have : s.length + 1 = p.length := by
                            simpa [hp, List.length_append] using congrArg List.length hp
                          omega
                        calc
                          focus.take s.length = (focus.take p.length).take s.length := by
                            rw [List.take_take, hmin]
                          _ = p.take s.length := by rw [htakeP]
                          _ = s := hpTake
                      have hsNe : CarrierNode.real s ≠ CarrierNode.real focus := by
                        intro heq
                        cases heq
                        exact Nat.lt_irrefl _ hsLen
                      have hrawS := rawNewParent_strictPrefix (focus := focus)
                        ⟨hsLen, hstake⟩ hsNe
                      have hatom : focus[s.length] = atom := by
                        have hsucc : focus.take (s.length + 1) = s ++ [atom] := by
                          have hlenP : p.length = s.length + 1 := by
                            simpa [hp, List.length_append] using congrArg List.length hp
                          simpa [hp, hlenP] using hpre.2
                        have hsplit : focus.take (s.length + 1) = s ++ [focus[s.length]] := by
                          rw [List.take_succ_eq_append_getElem hsLen, hstake]
                        have happ : s ++ [focus[s.length]] = s ++ [atom] := by
                          rw [← hsplit, hsucc]
                        simpa using List.append_cancel_left happ
                      simpa [hp, hatom] using hrawS
                    · have hpNe : CarrierNode.real p ≠ CarrierNode.real focus := hne
                      have hraw := rawNewParent_notPrefix (focus := focus) hpNe hpre
                      have hparent : rawNewParent focus (CarrierNode.real p) =
                          some (CarrierNode.real s) := by
                        simpa [hp, List.dropLast_concat] using hraw
                      exact (hnot hparent).elim

theorem kept_of_outward_armChild (hfocus : SimpleFrom molecule root focus)
    {incoming : Option (Nodes molecule root)}
    (hanchor : RealCutAnchor focus hfocus incoming)
    {cursor step : Nodes molecule root}
    (hkept : KeptAfterCut focus incoming cursor)
    (hchild : armChild focus cursor step)
    (hnot : ¬ ExcludedPredecessor focus incoming cursor step) :
    KeptAfterCut focus incoming step := by
  intro inc hinc hsub
  have hincChild : armChild focus ⟨.real focus, hfocus⟩ inc := hanchor inc hinc
  cases hsub with
  | refl =>
      have hcur := realRetainedArm_unique_parent molecule root hfocus hchild hincChild
      exact hnot (Or.inl ⟨by simp [hcur], hinc⟩)
  | @tail mid _ hprev hedge =>
      have hmid := realRetainedArm_unique_parent molecule root hfocus hedge hchild
      cases hmid
      exact hkept inc hinc hprev

/-- A cut-graph child of a kept cursor is exactly a carrier neighbor other than the
traversal predecessor. The predecessor at the focus is `incoming`, including when that
anchor is an outward carrier child. -/
theorem cutChild_iff_cutStep (hfocus : SimpleFrom molecule root focus)
    {incoming : Option (Nodes molecule root)}
    (hanchor : RealCutAnchor focus hfocus incoming)
    (cursor : (realCutRetainedArm molecule root hfocus incoming hanchor).Node)
    (step : Nodes molecule root) :
    (∃ hstep : KeptAfterCut focus incoming step,
        (realCutRetainedArm molecule root hfocus incoming hanchor).child cursor
          ⟨step, hstep⟩) ↔
      CutStep focus incoming cursor.1 step := by
  constructor
  · intro ⟨hstep, hchild⟩
    refine ⟨armChild_carrierAdjacent hchild, ?_⟩
    intro hex
    rcases hex with ⟨hroot, hin⟩ | ⟨hne, hparent⟩
    · have hkeptInc : KeptAfterCut focus (some step) step := by
        simpa [hin] using hstep
      exact realCut_excludes_incoming hfocus step hkeptInc
    · exact not_armChild_both hfocus hchild hparent
  · intro ⟨hadj, hnot⟩
    by_cases hroot : cursor.1.1 = CarrierNode.real focus
    · have hcursor : cursor.1 = ⟨CarrierNode.real focus, hfocus⟩ := Subtype.ext hroot
      have hchild : armChild focus cursor.1 step := by
        rw [hcursor]
        exact (focus_armChild_iff_carrierAdjacent hfocus step).2 (by simpa [hroot] using hadj)
      have hkept : KeptAfterCut focus incoming step :=
        kept_of_outward_armChild hfocus hanchor cursor.2 hchild hnot
      exact ⟨hkept, hchild⟩
    · have hnotParent : ¬ armChild focus step cursor.1 := by
        intro hparent
        exact hnot (Or.inr ⟨hroot, hparent⟩)
      have hchild := armChild_of_carrierAdjacent_not_parent (cursor := cursor.1)
        hroot hadj hnotParent
      have hkept := kept_of_outward_armChild hfocus hanchor cursor.2 hchild hnot
      exact ⟨hkept, hchild⟩

/-- Every node reached from the focus by nonbacktracking `CutStep`s lies in the cut.
The first excluded neighbor is the supplied incoming anchor. -/
theorem kept_of_cutTraversal (hfocus : SimpleFrom molecule root focus)
    {incoming : Option (Nodes molecule root)}
    (hanchor : RealCutAnchor focus hfocus incoming)
    {node : Nodes molecule root}
    (hwalk : Relation.ReflTransGen (CutStep focus incoming) ⟨.real focus, hfocus⟩ node) :
    KeptAfterCut focus incoming node := by
  induction hwalk with
  | refl => exact focus_kept hfocus hanchor
  | @tail prev node _ hstep ih =>
      obtain ⟨hkept, _⟩ :=
        (cutChild_iff_cutStep hfocus hanchor ⟨prev, ih⟩ node).2 hstep
      exact hkept

/-- The cut keeps the full-reroot label, provenance, ring distance, and depth. -/
theorem realCut_preserves_full_reroot_state (hfocus : SimpleFrom molecule root focus)
    {incoming : Option (Nodes molecule root)}
    (hanchor : RealCutAnchor focus hfocus incoming)
    (node : (realCutRetainedArm molecule root hfocus incoming hanchor).Node) :
    (realCutRetainedArm molecule root hfocus incoming hanchor).label node =
        (realRetainedArm molecule root hfocus).label node.1 ∧
      (realCutRetainedArm molecule root hfocus incoming hanchor).depth node =
        (realRetainedArm molecule root hfocus).depth node.1 :=
  ⟨rfl, rfl⟩

theorem ring_no_cutStep {path : List Atom} {atom : Atom}
    (h : CarrierNode.Valid molecule root (.ring path atom))
    (incoming : Option (Nodes molecule root)) (step : Nodes molecule root) :
    ¬ CutStep focus incoming ⟨.ring path atom, h⟩ step := by
  intro ⟨hadj, hnot⟩
  rcases hadj with hto | hfrom
  · simp [CarrierNode.Child] at hto
  · rcases step with ⟨val, hv⟩
    cases val with
    | ring _ _ => simp [CarrierNode.Child] at hfrom
    | real q =>
        cases hfrom
        have hring : CarrierNode.ring path atom ≠ CarrierNode.real focus := by
          intro hne
          cases hne
        have hparent : armChild focus ⟨CarrierNode.real path, hv⟩
            ⟨CarrierNode.ring path atom, h⟩ := by
          unfold armChild rawNewParent
          rw [if_neg hring]
        exact hnot (Or.inr ⟨by simp, hparent⟩)

theorem cutRetainedArm_child_iff_cutStep {path : List Atom}
    (hpath : SimpleFrom molecule root path) {incoming : Option (Nodes molecule root)}
    (hanchor : CutAnchor ⟨.real path, hpath⟩ incoming)
    (cursor : (cutRetainedArm molecule root ⟨.real path, hpath⟩ incoming hanchor).Node)
    (step : Nodes molecule root) :
    (∃ hstep : KeptAfterCut path incoming step,
        (cutRetainedArm molecule root ⟨.real path, hpath⟩ incoming hanchor).child cursor
          ⟨step, hstep⟩) ↔
      CutStep path incoming cursor.1 step := by
  simpa [cutRetainedArm_real] using
    cutChild_iff_cutStep hpath (realAnchor hanchor) cursor step

end

end RetainedCutArmTraversal
end DeclarativeCIP
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedCutArmTraversal.cutChild_iff_cutStep
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedCutArmTraversal.kept_of_cutTraversal
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedCutArmTraversal.realCut_preserves_full_reroot_state
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedCutArmTraversal.ring_no_cutStep
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedCutArmTraversal.cutRetainedArm_child_iff_cutStep
