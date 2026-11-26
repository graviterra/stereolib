import TetraStereo.Engine.RingAtomicFramePriority
import TetraStereo.Engine.RingChildKeyRecovery

/-! Rule 1a at the first two spheres, under an explicit local carrier guard.
The guard concerns atom identities in actual rerooted children, not priorities. -/
set_option autoImplicit false
noncomputable section
namespace TetraStereo.Engine.RingAtomicSecondShell
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm)
open RingRetainedChemicalTrace
attribute [local instance] lexOrd
open private source_children from TetraStereo.Engine.RingChildKeyRecovery
open private rulePrefix shallow byDescending makeColumn from TetraStereo.Engine.RingRetainedChemicalTrace

/-- Descending atomic-number observations, retaining all multiplicities. -/
def sorted (xs : List Nat) := xs.mergeSort (fun a b => decide (b ≤ a))

private theorem sorted_projection (ks : List Key) :
    (byDescending (shallow .atomic) ks).map (fun k => k.root.atomic) =
      sorted (ks.map (fun k => k.root.atomic)) := by
  apply List.Perm.eq_of_pairwise (fun _ _ _ _ ab ba => le_antisymm ba ab)
  · have h := List.pairwise_mergeSort (le := fun a b : Key => decide (shallow .atomic b ≤ shallow .atomic a))
      (fun _ _ _ h k => decide_eq_true (le_trans (of_decide_eq_true k) (of_decide_eq_true h)))
      (fun a b => by simpa using le_total (shallow .atomic b) (shallow .atomic a)) ks
    apply List.pairwise_map.mpr
    exact h.imp (fun {a b} h => by
      have hh : [b.root.atomic] ≤ [a.root.atomic] := of_decide_eq_true h
      apply le_of_not_gt
      intro gt
      exact (not_lt_of_ge hh) (List.Lex.rel gt))
  · exact (List.pairwise_mergeSort (le := fun a b : Nat => decide (b ≤ a))
      (fun _ _ _ h k => decide_eq_true (le_trans (of_decide_eq_true k) (of_decide_eq_true h)))
      (fun a b => by simpa using le_total b a) _).imp (fun h => of_decide_eq_true h)
  · exact ((List.mergeSort_perm ..).map _).trans (List.mergeSort_perm ..).symm

private theorem project {α β γ : Type} (xs : List α) (f : α → Option β)
    (p : β → γ) (v : α → γ)
    (sound : ∀ x ∈ xs, ∀ b, f x = some b → p b = v x)
    (size : (xs.filterMap f).length = xs.length) :
    (xs.filterMap f).map p = xs.map v := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : f x with
    | none =>
      have bound := List.length_filterMap_le f xs
      simp only [List.filterMap_cons,h,List.length_cons] at size
      omega
    | some b =>
      simp only [List.filterMap_cons,h,List.length_cons] at size ⊢
      rw [List.map_cons,List.map_cons,sound x List.mem_cons_self b h]
      exact congrArg (List.cons _) (ih (fun y hy => sound y (List.mem_cons_of_mem _ hy)) (by omega))

/-- A sufficient local guard, checkable from the graph and carrier alone.
Every actual child names a written atom, and its identity multiset is exactly
all graph neighbors of the arm atom other than the focus. A closure duplicate
is therefore included only if it represents one of those neighbors. Incoming
arms are covered by the same condition; no outward-only convention is used. -/
structure LocalGuard (i : Input) (q : Arm i) (focus atom : i.certified.Atom) where
  current : q.occurrence.val.node.current? = some atom
  childAtom : Arm i → i.certified.Atom
  record : Arm i → AtomSpec
  childCurrent : ∀ c ∈ i.certified.executableLocalizedRerootChildren q,
    c.occurrence.val.node.current? = some (childAtom c)
  childWritten : ∀ c ∈ i.certified.executableLocalizedRerootChildren q,
    i.molecule.atoms[(childAtom c).val]? = some (record c)
  physical : ((i.certified.executableLocalizedRerootChildren q).map childAtom).Perm
    ((i.certified.moleculeGraph.neighborFinset atom).erase focus).toList

/-- The graph's first-neighbor atomic-number word, excluding the focus. -/
def graphWord (i : Input) (focus atom : i.certified.Atom) : List Nat :=
  sorted ((((i.certified.moleculeGraph.neighborFinset atom).erase focus).toList).map
    (fun a => ((i.molecule.atoms[a.val]?).getD (AtomSpec.aliphatic .H)).element.atomicNumber))

/-- Recovery of the genuine shallow Rule-1a row from written child atoms.
This statement precedes any comparison and does not assume key equality. -/
theorem second_row {i : Input} {q : Arm i} {focus atom : i.certified.Atom}
    (g : LocalGuard i q focus atom) {k : Key} (read : key? i q = some k) :
    k.atomic.word[1]? = some (graphWord i focus atom) := by
  obtain ⟨o,h,_,size⟩ := source_children read
  have values : (RingChildKeyRecovery.childKeys i q).map (fun k => k.root.atomic) =
      (i.certified.executableLocalizedRerootChildren q).map
        (fun a => ((i.molecule.atoms[(g.childAtom a).val]?).getD (AtomSpec.aliphatic .H)).element.atomicNumber) := by
    apply project _ (key? i) (fun k => k.root.atomic) _ _ size
    intro c hc v hv
    have z := RingPyramidalConstitution.key_atomic (g.childCurrent c hc) (g.childWritten c hc) hv
    simpa [g.childWritten c hc] using z
  have perm := g.physical.map
    (fun a => ((i.molecule.atoms[a.val]?).getD (AtomSpec.aliphatic .H)).element.atomicNumber)
  have sortEq : sorted ((RingChildKeyRecovery.childKeys i q).map (fun k => k.root.atomic)) = graphWord i focus atom := by
    rw [values]
    unfold graphWord sorted
    have sortedNat (xs : List Nat) : (xs.mergeSort (fun a b => decide (b ≤ a))).Pairwise (· ≥ ·) :=
      (List.pairwise_mergeSort (le := fun a b : Nat => decide (b ≤ a))
        (fun _ _ _ h k => decide_eq_true (le_trans (of_decide_eq_true k) (of_decide_eq_true h)))
        (fun a b => by simpa using le_total b a) xs).imp (fun h => of_decide_eq_true h)
    apply List.Perm.eq_of_pairwise (fun _ _ _ _ ab ba => le_antisymm ba ab) (sortedNat _) (sortedNat _)
    have p : ((i.certified.executableLocalizedRerootChildren q).map
        (fun a => ((i.molecule.atoms[(g.childAtom a).val]?).getD (AtomSpec.aliphatic .H)).element.atomicNumber)).Perm
        ((((i.certified.moleculeGraph.neighborFinset atom).erase focus).toList).map
        (fun a => ((i.molecule.atoms[a.val]?).getD (AtomSpec.aliphatic .H)).element.atomicNumber)) := by
      simpa only [List.map_map,Function.comp_def] using perm
    exact (List.mergeSort_perm ..).trans (p.trans (List.mergeSort_perm ..).symm)
  rw [h]
  change some ((byDescending (shallow .atomic) (RingChildKeyRecovery.childKeys i q)).map
    (fun k => k.root.atomic)) = _
  rw [sorted_projection,sortEq]

/-- Strict second-sphere separation decides the complete constitutional word;
later spheres, duplicate origins and masses cannot reverse it. -/
theorem word_lt_second {i j : Input} {a : Arm i} {b : Arm j}
    {fa aa : i.certified.Atom} {fb ab : j.certified.Atom}
    (ga : LocalGuard i a fa aa) (gb : LocalGuard j b fb ab)
    {ka kb : Key} (ra : key? i a = some ka) (rb : key? j b = some kb)
    (same : ka.root.atomic = kb.root.atomic)
    (less : graphWord i fa aa < graphWord j fb ab) :
    RingRetainedChemicalPreorder.orderWord ka < RingRetainedChemicalPreorder.orderWord kb := by
  have ha := ((key_source ra).formed .atomic).2
  have hb := ((key_source rb).formed .atomic).2
  change ka.atomic.word = [ka.root.atomic] :: ka.atomic.levels.flatten at ha
  change kb.atomic.word = [kb.root.atomic] :: kb.atomic.levels.flatten at hb
  have sa := second_row ga ra
  have sb := second_row gb rb
  rw [ha] at sa
  rw [hb] at sb
  generalize ka.atomic.levels.flatten = xs at ha sa
  generalize kb.atomic.levels.flatten = ys at hb sb
  cases xs with
  | nil => simp at sa
  | cons x xs =>
    cases ys with
    | nil => simp at sb
    | cons y ys =>
      have ex : x = graphWord i fa aa := Option.some.inj sa
      have ey : y = graphWord j fb ab := Option.some.inj sb
      change ka.atomic.word :: _ < kb.atomic.word :: _
      apply List.Lex.rel
      rw [ha,hb,same]
      exact List.Lex.cons (List.Lex.rel (by simpa only [ex,ey] using less))

/-- Graph-only first/second-shell separation, with records read from the
written molecular atoms. Neither supplied priorities nor final key equality
is a premise. -/
theorem word_lt_graph {i j : Input} {a : Arm i} {b : Arm j}
    {fa aa : i.certified.Atom} {fb ab : j.certified.Atom}
    (ga : LocalGuard i a fa aa) (gb : LocalGuard j b fb ab)
    {ar br : AtomSpec}
    (wa : i.molecule.atoms[aa.val]? = some ar)
    (wb : j.molecule.atoms[ab.val]? = some br)
    {ka kb : Key} (ra : key? i a = some ka) (rb : key? j b = some kb)
    (less : ar.element.atomicNumber < br.element.atomicNumber ∨
      ar.element.atomicNumber = br.element.atomicNumber ∧ graphWord i fa aa < graphWord j fb ab) :
    RingRetainedChemicalPreorder.orderWord ka < RingRetainedChemicalPreorder.orderWord kb := by
  have za := RingPyramidalConstitution.key_atomic ga.current wa ra
  have zb := RingPyramidalConstitution.key_atomic gb.current wb rb
  rcases less with h | ⟨eq,h⟩
  · exact RingPyramidalConstitution.word_lt_of_Z (key_source ra).formed (key_source rb).formed
      (by simpa only [za,zb] using h)
  · exact word_lt_second ga gb ra rb (by simpa only [za,zb] using eq) h

open RingNestedActivePair (Frame Reader)
open RingActivePairReport (Slot)

/-- Four separated graph signatures give the physical hand in slot order at
this actual rerooted frame, including any inward slot. -/
theorem centre_strict_second {i : Input}
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {q : RingActivePairs.Site i} (fr : Frame i q) {r : Reader i}
    (ready : RingGroupedStereo.Ready q r)
    (guards : ∀ k : Slot, LocalGuard i (RingGroupedCentre.cursor fr k) fr.center.val
      (RingAtomicFramePriority.slotNeighbor fr k).val)
    (records : Slot → AtomSpec)
    (written : ∀ k, i.molecule.atoms[(RingAtomicFramePriority.slotNeighbor fr k).val.val]? = some (records k))
    (descending : ∀ j k : Slot, j < k →
      (records k).element.atomicNumber < (records j).element.atomicNumber ∨
      (records k).element.atomicNumber = (records j).element.atomicNumber ∧
      graphWord i fr.center.val (RingAtomicFramePriority.slotNeighbor fr k).val <
        graphWord i fr.center.val (RingAtomicFramePriority.slotNeighbor fr j).val) :
    RingFullPathPublication.centre? fr r = some
      ((readback? (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified)
        (fr.atoms (List.finRange 4))).map fun h =>
        (LocalizedTetrahedralRSPseudoDescriptor.chiral h,
          LocalizedTetrahedralRSPseudoDescriptor.chiral h.swap)) := by
  have lower {j k : Slot} (h : j < k) :
      RingFullPathConstitution.word fr k < RingFullPathConstitution.word fr j :=
    word_lt_graph (guards k) (guards j) (written k) (written j)
      (RingRetainedChemicalPreorder.read_key (fr.direction k))
      (RingRetainedChemicalPreorder.read_key (fr.direction j)) (descending j k h)
  have inj : Function.Injective (RingFullPathConstitution.word fr) := by
    intro j k eqn
    by_contra ne
    rcases lt_or_gt_of_ne ne with lt | lt
    · exact (ne_of_lt (lower lt)) eqn.symm
    · exact (ne_of_lt (lower lt)) eqn
  have legal : RingStereoSiblingPass.Legal (RingFullPathConstitution.word fr)
      (List.finRange 4) (List.finRange 4) :=
    ⟨List.Perm.refl _,List.pairwise_map.mpr
      ((List.pairwise_lt_finRange 4).imp (fun h => le_of_lt (lower h)))⟩
  exact RingConstitutionalHand.centre_read geom
    (RingConstitutionalHand.DescendingFrame.ranked ⟨List.finRange 4,inj,legal,rfl⟩) ready

end TetraStereo.Engine.RingAtomicSecondShell
assert_kernel_only TetraStereo.Engine.RingAtomicSecondShell.second_row
assert_kernel_only TetraStereo.Engine.RingAtomicSecondShell.word_lt_second
assert_kernel_only TetraStereo.Engine.RingAtomicSecondShell.word_lt_graph
assert_kernel_only TetraStereo.Engine.RingAtomicSecondShell.centre_strict_second
