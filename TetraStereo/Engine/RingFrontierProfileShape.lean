import TetraStereo.Engine.RingAtomicProfileShape
import TetraStereo.Engine.RingMolecularSchedule

set_option autoImplicit false

namespace TetraStereo.Engine.RingFrontierProfileShape
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (masked consistent Labels)
open RingMolecularSchedule (frontier atRoot)
open RingAtomicProfileShape (Ready)

/-- A scheduled positive publication has four distinct physical ligand slots at
the uncut occurrence. This holds for both constitutional and later-rule labels. -/
theorem positive_four {i : Input} {root : i.certified.Atom} {q : Site i} {v}
    (on : q.val.root = root) (published : atRoot i root q = some (some v)) :
    (RingRetainedAuxiliary.frame i.certified q).length = 4 := by
  rw [RingMolecularSchedule.atRoot_eq on] at published
  rcases RingNestedActivePair.publication_source published with ⟨s,actual,_⟩ | ⟨a,_,_⟩
  · obtain ⟨p,_⟩ := (RingRetainedAuxiliary.read_iff i q s).mp actual
    have ids := (TerminalTie.mapM_forall₂ _ _ _ p.coordinates).length_eq
    have rank := (RingRetainedAuxiliary.order_perm i.certified q).length_eq
    have four := p.carriers.length_eq
    simp only [RingRetainedAuxiliary.canonical,List.length_map,List.length_finRange] at four
    simp only [List.length_map] at rank
    exact rank.symm.trans (ids.trans four)
  · exact a.frame.four

private theorem single_cut {α : Type} (keep : α → Bool) (xs : List α)
    (distinct : xs.Nodup) (one : ∀ a ∈ xs, ∀ b ∈ xs, keep a = false → keep b = false → a = b) :
    xs.length ≤ (xs.filter keep).length + 1 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have nd := List.nodup_cons.mp distinct
    cases h : keep x with
    | false =>
      have all : xs.filter keep = xs := List.filter_eq_self.mpr (fun y hy => by
        cases e : keep y with
        | true => rfl
        | false =>
          have same := one x List.mem_cons_self y (List.mem_cons_of_mem x hy) h e
          exact False.elim (nd.1 (same ▸ hy)))
      simp [h,all]
    | true =>
      have rest := ih nd.2 (fun a ha b hb => one a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem x hb))
      simpa only [List.filter_cons,h,ite_true,List.length_cons,Nat.succ_le_succ_iff] using Nat.succ_le_succ rest

/-- A directed cursor removes at most one occurrence address from the uncut
physical frame, including when it enters toward the original root. -/
theorem cut_frame {i : Input} (q : Arm i) :
    (RingRetainedAuxiliary.frame i.certified q.occurrence).length ≤
      (i.certified.executableLocalizedRerootChildren q).length + 1 := by
  let c := i.certified
  have lengths (a : Arm i) :
      (c.executableLocalizedRerootChildren a).length = (c.intendedLocalizedRerootChildFrames a).length := by
    simpa only [List.length_map] using congrArg List.length (c.executableLocalizedRerootChildren_map a)
  change (c.executableLocalizedRerootChildren ⟨q.occurrence,none⟩).length ≤ _
  rw [lengths,lengths]
  rcases q with ⟨q,prev⟩
  cases dup : q.val.node.isDuplicateLeaf with
  | true => simp [intendedLocalizedRerootChildFrames,dup]
  | false =>
    cases prev with
    | none => simp [intendedLocalizedRerootChildFrames,dup]
    | some p =>
      simp only [intendedLocalizedRerootChildFrames,dup,Bool.false_eq_true,if_false]
      let ns := c.localizedRerootNeighborFrames (fuel := c.certified.input.molecule.atomCount+1) q.val
      apply single_cut _ ns (c.localizedRerootNeighborFrames_nodup _)
      intro a ha b hb ra rb
      have addra : a.address = p.val.address := by simpa using ra
      have addrb : b.address = p.val.address := by simpa using rb
      have present (a : c.LocalizedCIPOccurrenceFrame) (ha : a ∈ ns) :=
        (c.mem_localizedOccurrences_iff _ a).mp (c.mem_localizedOccurrences_of_mem_localizedRerootNeighborFrames _ a ha)
      exact c.declarativeLocalizedOccurrence_functional_at_root_address (present a ha) (present b hb)
        ((c.localizedRerootNeighborFrames_root_eq _ a ha).trans (c.localizedRerootNeighborFrames_root_eq _ b hb).symm)
        (addra.trans addrb.symm)

/-- The partial schedule at a frontier focus gives a known, mirror-consistent
masked cell everywhere on its original root, and a certified absence on every
terminal directed occurrence. -/
theorem frontier_observation {i : Input} {root : i.certified.Atom} {f : Site i}
    (listed : f ∈ frontier i root) (q : Arm i) (on : q.occurrence.val.root = f.val.root) :
    ∃ labels, masked f (atRoot i root) q.occurrence = some labels ∧ labels.all consistent = true ∧
      (i.certified.executableLocalizedRerootChildren q = [] → labels = none) := by
  obtain ⟨focus,_,known⟩ := RingMolecularSchedule.mem_frontier.mp listed
  by_cases vis : RingNestedActivePair.Eligible f q.occurrence
  · obtain ⟨v,hv⟩ := Option.isSome_iff_exists.mp (known q.occurrence vis)
    refine ⟨v,by simp [masked,on,vis,hv],?_⟩
    cases v with
    | none => exact ⟨rfl,fun _ => rfl⟩
    | some labels =>
      have four := positive_four (on.trans focus) hv
      have cover := cut_frame q
      refine ⟨RingMolecularSchedule.mirror_label (on.trans focus) hv,?_⟩
      intro empty
      rw [empty,four] at cover
      contradiction
  · exact ⟨none,by simp [masked,on,vis],rfl,fun _ => rfl⟩

/-- On a scheduled frontier the local obstruction consists entirely of choosing
the chemical sibling order and checking its shallow observations. -/
theorem ready_iff {i : Input} {root : i.certified.Atom} {f : Site i} (listed : f ∈ frontier i root)
    (q : Arm i) (on : q.occurrence.val.root = f.val.root) :
    Ready i (masked f (atRoot i root)) q ↔
      ∃ row, RingRetainedSiblingOrder.chemicalChildren? i q = some row ∧
        RingNestedActivePair.ShallowOrder i (masked f (atRoot i root)) row.val := by
  constructor
  · rintro ⟨row,_,found,shallow,_⟩
    exact ⟨row,found,shallow⟩
  · rintro ⟨row,found,shallow⟩
    obtain ⟨labels,published,consistent,terminal⟩ := frontier_observation listed q on
    refine ⟨row,labels,found,shallow,published,consistent,?_⟩
    by_cases zero : row.val.length = 0
    · have length := row.property.complete.length_eq
      have empty := List.length_eq_zero_iff.mp (length.symm.trans zero)
      rw [terminal empty]
      exact Or.inr rfl
    · exact Or.inl zero

/-- Every molecular reroot step stays in the same original carrier. -/
theorem reaches_root {i : Input} {a b : Arm i} (h : RingRetainedChemicalTrace.Reaches i a b) :
    b.occurrence.val.root = a.occurrence.val.root := by
  induction h with
  | here => rfl
  | descend hd _ ih =>
    exact ih.trans (i.certified.localizedRerootChildren_root_eq _ _ _ (i.certified.executableLocalizedRerootChildren_declarative _) hd)

/-- At a frontier site, every failed retained arm profile localizes to an actual
sibling-priority obstruction on that same carrier. -/
theorem missing_iff_sibling {i : Input} {root : i.certified.Atom} {f : Site i}
    (listed : f ∈ frontier i root) (q : Arm i) (on : q.occurrence.val.root = f.val.root)
    (valid : i.certified.LocalizedRerootCursorValid q) :
    let read := masked f (atRoot i root)
    RingNestedActivePair.retainedLevels? i read (2*(i.certified.certified.input.molecule.atomCount+2)+2) [q] = none ↔
      ∃ t, RingRetainedChemicalTrace.Reaches i q t ∧
        ¬ ∃ row, RingRetainedSiblingOrder.chemicalChildren? i t = some row ∧ RingNestedActivePair.ShallowOrder i read row.val := by
  dsimp only
  rw [RingAtomicProfileShape.missing_iff _ q valid]
  apply exists_congr
  intro t
  apply and_congr_right
  intro reach
  exact not_congr (ready_iff listed t ((reaches_root reach).trans on))

end TetraStereo.Engine.RingFrontierProfileShape

assert_kernel_only TetraStereo.Engine.RingFrontierProfileShape.positive_four
assert_kernel_only TetraStereo.Engine.RingFrontierProfileShape.cut_frame
assert_kernel_only TetraStereo.Engine.RingFrontierProfileShape.frontier_observation
assert_kernel_only TetraStereo.Engine.RingFrontierProfileShape.ready_iff
assert_kernel_only TetraStereo.Engine.RingFrontierProfileShape.missing_iff_sibling
assert_kernel_only TetraStereo.Engine.RingFrontierProfileShape.reaches_root
