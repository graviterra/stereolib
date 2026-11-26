import Mathlib.Data.List.Lex
import TetraStereo.Engine.RingAllLigandTwoShell
import TetraStereo.Engine.RingAtomicNeighborOrder

/-! Executable graph-only two-shell decisions at retained tetrahedral frames. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingSecondShellDecision
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Frame Reader)
open RingActivePairReport (Slot)
open RingAtomicNeighborOrder (atomicNumber record written)
attribute [local instance] lexOrd
open private bound toAtom raw_adj from TetraStereo.Engine.RingAtomicNeighborOrder

/-- Original graph IDs adjacent to the ligand, excluding the focus. -/
def adjacent (m : RawMolecule) (focus atom : Nat) : List Nat :=
  (List.range m.atomCount).filter fun n => n != focus && 0 < m.bondOrder atom n

def shell (m : RawMolecule) (focus atom : Nat) : List Nat :=
  RingAtomicSecondShell.sorted ((adjacent m focus atom).map (atomicNumber m))

/-- Only written atomic numbers and original graph bonds enter this key. -/
def signature (m : RawMolecule) (focus atom : Nat) : List (List Nat) :=
  [[atomicNumber m atom],shell m focus atom]

private theorem sorted_perm {xs ys : List Nat} (p : xs.Perm ys) :
    RingAtomicSecondShell.sorted xs = RingAtomicSecondShell.sorted ys := by
  have sorted (xs : List Nat) : (RingAtomicSecondShell.sorted xs).Pairwise (· ≥ ·) :=
    (List.pairwise_mergeSort (le := fun a b : Nat => decide (b ≤ a))
      (fun _ _ _ h k => decide_eq_true (le_trans (of_decide_eq_true k) (of_decide_eq_true h)))
      (fun a b => by simpa using le_total b a) xs).imp (fun h => of_decide_eq_true h)
  exact List.Perm.eq_of_pairwise (fun _ _ _ _ ab ba => le_antisymm ba ab)
    (sorted xs) (sorted ys) ((List.mergeSort_perm ..).trans (p.trans (List.mergeSort_perm ..).symm))

theorem shell_graphWord (i : Input) (focus atom : i.certified.Atom) :
    shell i.molecule focus.val atom.val = RingAtomicSecondShell.graphWord i focus atom := by
  let fs := (i.certified.moleculeGraph.neighborFinset atom).erase focus
  have memFS (a : i.certified.Atom) : a ∈ fs.toList ↔ a ≠ focus ∧ i.certified.moleculeGraph.Adj atom a := by
    rw [Finset.mem_toList]
    simp only [fs,Finset.mem_erase,MoleculeGraph.mem_neighborFinset]
  have p : (adjacent i.molecule focus.val atom.val).Perm (fs.toList.map Fin.val) := by
    have nd : (fs.toList.map Fin.val).Nodup := (Finset.nodup_toList _).map Fin.val_injective
    apply (List.perm_ext_iff_of_nodup (List.nodup_range.filter _) nd).mpr
    intro n
    simp only [List.mem_filter,List.mem_range,Bool.and_eq_true,bne_iff_ne,decide_eq_true_eq,
      List.mem_map,memFS]
    constructor
    · rintro ⟨hn,ne,adj⟩
      exact ⟨toAtom i n hn,⟨fun eq => ne (congrArg Fin.val eq),(raw_adj i atom _).mpr adj⟩,rfl⟩
    · rintro ⟨a,⟨ne,adj⟩,rfl⟩
      exact ⟨bound i a,fun eq => ne (Fin.ext eq),(raw_adj i atom a).mp adj⟩
  unfold shell RingAtomicSecondShell.graphWord
  apply sorted_perm
  have h := p.map (atomicNumber i.molecule)
  rw [List.map_map] at h
  convert h using 1
  apply List.map_congr_left
  intro a _
  simp [atomicNumber,written]

/-- Executable two-shell prefix at any actual direction, including an inward
edge or a terminal closure endpoint. Only original graph records and endpoint
provenance are inspected. -/
def prefixFor (i : Input) (f : RingRetainedChemicalPreorder.Site i)
    (a : RingRetainedChemicalPreorder.Direction i f) : List (List Nat) :=
  let focus := RingAllLigandTwoShell.siteAtom i f
  let atom := RingAllLigandTwoShell.siteAtom i a.val
  [[atomicNumber i.molecule atom.val],
    if a.val.val.node.provenance = .realAtom then shell i.molecule focus.val atom.val else []]

theorem prefixFor_physical (i : Input) (f : RingRetainedChemicalPreorder.Site i)
    (a : RingRetainedChemicalPreorder.Direction i f) :
    prefixFor i f a = RingAllLigandTwoShell.physical i f a := by
  simp [prefixFor,RingAllLigandTwoShell.physical,RingSecondShellIncidence.secondWord,
    atomicNumber,written,shell_graphWord]

/-- The executable score retains the endpoint kind: real atoms expose their
physical second shell, and closure leaves terminate after their represented Z. -/
def score {i : Input} {q : Site i} (fr : Frame i q) (k : Slot) : List (List Nat) :=
  [[atomicNumber i.molecule (fr.atoms [k]).head!],
    if (fr.arm k).occurrence.val.node.provenance = .realAtom then
      shell i.molecule fr.center.val.val (fr.atoms [k]).head! else []]

/-- The executable raw-graph score is the independent all-direction observation. -/
theorem score_physical {i : Input} {q : Site i} (fr : Frame i q) (k : Slot) :
    score fr k = RingAllLigandTwoShell.physical i q (fr.direction k) := by
  have focus := (i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff q fr.center).mp fr.recognized
  have focusAtom : RingAllLigandTwoShell.siteAtom i q = fr.center.val := by
    simp [RingAllLigandTwoShell.siteAtom,focus.2]
  have current : (fr.direction k).val.val.node.current? =
      some (RingAtomicFramePriority.slotNeighbor fr k).val := RingAtomicFramePriority.slot_current fr k
  have armAtom : RingAllLigandTwoShell.siteAtom i (fr.direction k).val =
      (RingAtomicFramePriority.slotNeighbor fr k).val := by
    simp [RingAllLigandTwoShell.siteAtom,current]
  have val : (RingAtomicFramePriority.slotNeighbor fr k).val.val = (fr.atoms [k]).head! :=
    RingAtomicFramePriority.slotNeighbor_val fr k
  simp only [score,RingAllLigandTwoShell.physical,armAtom,focusAtom,←val]
  simp [RingSecondShellIncidence.secondWord,atomicNumber,written,shell_graphWord,RingNestedActivePair.Frame.direction]

private theorem score_lt {i : Input} {q : Site i} (fr : Frame i q)
    {a b : Slot} (h : score fr a < score fr b) :
    RingFullPathConstitution.word fr a < RingFullPathConstitution.word fr b := by
  exact RingAllLigandTwoShell.word_lt_of_prefix (fr.direction a) (fr.direction b)
    (by simpa only [score_physical] using h)

/-- A sorted permutation, accepted only when all four graph signatures differ. -/
def row? {i : Input} {q : Site i} (fr : Frame i q) : Option (List Slot) :=
  let row := RingStereoSiblingPass.order (score fr) (List.finRange 4)
  if row.Pairwise (fun a b => score fr b < score fr a) then some row else none

private noncomputable def ranked {i : Input} {q : Site i} (fr : Frame i q)
    {row : List Slot} (hit : row? fr = some row) :
    RingConstitutionalHand.OrientationFrame fr (fr.atoms row) := by
  dsimp only [row?] at hit
  split at hit <;> try contradiction
  rename_i strict
  obtain rfl := Option.some.inj hit
  have perm := (RingStereoSiblingPass.legal_order (score fr) (List.finRange 4)).perm
  have strictNative := strict.imp (fun h => score_lt fr h)
  have inj : Function.Injective (RingFullPathConstitution.word fr) := by
    intro a b eqn
    have nd : ((RingStereoSiblingPass.order (score fr) (List.finRange 4)).map
        (RingFullPathConstitution.word fr)).Nodup :=
      List.pairwise_map.mpr (strictNative.imp (fun h => ne_of_gt h))
    have all := perm.map (RingFullPathConstitution.word fr)
    have nd' : ((List.finRange 4).map (RingFullPathConstitution.word fr)).Nodup := all.nodup_iff.mp nd
    exact ((List.nodup_map_iff_inj_on (List.nodup_finRange 4)).mp nd') a (List.mem_finRange _) b (List.mem_finRange _) eqn
  exact RingConstitutionalHand.DescendingFrame.ranked
    ⟨_,inj,⟨perm,List.pairwise_map.mpr (strictNative.imp le_of_lt)⟩,rfl⟩

/-- A partial two-shell assignment for every actual direction, including inward
arms and closure endpoints. No native key or auxiliary-store computation occurs. -/
def reference? (i : Input) (q : Site i) : Option RingNestedActivePair.Labels := do
  let fr ← RingNestedActivePair.frame? i q
  let row ← row? fr
  (readback? (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified) (fr.atoms row)).map
    fun h => (.chiral h,.chiral h.swap)

/-- Every returned pair is the actual native publication at this occurrence. -/
theorem reference_sound {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (q : Site i) {labels : RingNestedActivePair.Labels} (hit : reference? i q = some labels) :
    RingChemicalGraphProof.state i q = some (some labels) := by
  unfold reference? at hit
  obtain ⟨fr,hfr,more⟩ := Option.bind_eq_some_iff.mp hit
  obtain ⟨row,hrow,read⟩ := Option.bind_eq_some_iff.mp more
  have centre := RingConstitutionalHand.centre_read geom (ranked fr hrow)
    (RingChemicalGraphProof.ready geom q)
  have focus := (i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff q fr.center).mp fr.recognized
  have degree : Fintype.card (i.certified.moleculeGraph.Neighbor fr.center.val) = 4 :=
    (i.certified.moleculeGraph.mem_tetrahedralCenterSet fr.center.val).mp fr.center.property
  have noP : RingPyramidalPublication.focusP i q = none := by
    have off := RingHydrogenLeafGeometry.notP_of_degree_four (i := i) fr.center.val degree
    simp [RingPyramidalPublication.focusP,focus.1,focus.2,off]
  rw [RingChemicalGraphProof.state_eq,RingPyramidalPublication.publish,noP,
    RingFullPathConstitution.fast_local geom (RingChemicalGraphProof.ready geom q),
    RingFullPathPublication.publish?,hfr]
  simpa only [read] using centre

private theorem filter_dedup {α : Type} [DecidableEq α] (p : α → Bool) (xs : List α) :
    xs.dedup.filter p = (xs.filter p).dedup := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases hp : p a <;> by_cases hm : a ∈ xs <;> simp [hp,hm,ih]

private theorem flatMap_filter {α β : Type} (p : α → Bool) (f : α → List β) (xs : List α) :
    (xs.filter p).flatMap f = xs.flatMap (fun a => if p a then f a else []) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases hp : p a <;> simp [hp,ih]

/-- Materialize only this original root, preserving the exact carrier order. -/
def rootFrames (i : Input) (q : Site i) :=
  (i.certified.localizedOccurrencesAtAtom (i.certified.certified.input.molecule.atomCount+1) q.val.root).dedup

private theorem rootFrames_eq (i : Input) (q : Site i) : rootFrames i q =
    (i.certified.localizedOccurrences (i.certified.certified.input.molecule.atomCount+1)).filter
      (fun f => f.root == q.val.root) := by
  let fuel := i.certified.certified.input.molecule.atomCount+1
  have roots : (List.finRange i.certified.certified.input.molecule.atomCount).filter
      (fun r => r == q.val.root) = [q.val.root] := by
    apply List.perm_singleton.mp
    apply (List.perm_ext_iff_of_nodup ((List.nodup_finRange _).filter _) (by simp)).mpr
    intro r
    simp
  have filter_root (root : i.certified.Atom) :
      (i.certified.localizedOccurrencesAtAtom fuel root).filter (fun f => f.root == q.val.root) =
        if root == q.val.root then i.certified.localizedOccurrencesAtAtom fuel root else [] := by
    have tag (f : i.certified.LocalizedCIPOccurrenceFrame)
        (mem : f ∈ i.certified.localizedOccurrencesAtAtom fuel root) : f.root = root :=
      i.certified.declarativeLocalizedOccurrenceSubtree_root_eq
        ((i.certified.mem_localizedOccurrencesAtAtom_iff fuel root f).mp mem)
    by_cases same : root = q.val.root
    · subst root
      simp only [beq_self_eq_true,if_true]
      apply List.filter_eq_self.mpr
      intro f mem
      exact beq_iff_eq.mpr (tag f mem)
    · simp only [beq_iff_eq,same,if_false]
      apply List.filter_eq_nil_iff.mpr
      intro f mem observed
      exact same ((tag f mem).symm.trans (beq_iff_eq.mp observed))
  calc
    rootFrames i q = (((List.finRange i.certified.certified.input.molecule.atomCount).filter
        (fun r => r == q.val.root)).flatMap (i.certified.localizedOccurrencesAtAtom fuel)).dedup := by
      rw [roots]
      simp [rootFrames,fuel]
    _ = (((List.finRange i.certified.certified.input.molecule.atomCount).flatMap
        (i.certified.localizedOccurrencesAtAtom fuel)).filter (fun f => f.root == q.val.root)).dedup := by
      congr 1
      rw [flatMap_filter,List.filter_flatMap]
      apply LocalizedGenericMarkedRecalculation.flatMap_congr_mem
      intro root _
      exact (filter_root root).symm
    _ = _ := (filter_dedup _ _).symm

private theorem filter_redundant {α : Type} (xs : List α) (p r : α → Bool)
    (implies : ∀ a, p a = true → r a = true) : (xs.filter r).filter p = xs.filter p := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro a _
  cases h : p a with
  | false => simp
  | true => simp [implies a h]

def neighborsFast (i : Input) (q : Site i) :=
  let frames := rootFrames i q
  (frames.filter fun f => f.root == q.val.root && f.address.length+1 == q.val.address.length &&
    f.address == q.val.address.dropLast) ++
  (frames.filter fun f => f.root == q.val.root && f.address.length == q.val.address.length+1 &&
    f.address.dropLast == q.val.address)

private theorem neighborsFast_eq (i : Input) (q : Site i) : neighborsFast i q =
    i.certified.localizedRerootNeighborFrames (fuel := i.certified.certified.input.molecule.atomCount+1) q.val := by
  unfold neighborsFast localizedRerootNeighborFrames localizedCarrierParentFrames localizedCarrierOutwardChildFrames
  rw [rootFrames_eq]
  dsimp only
  congr 1 <;> apply filter_redundant
  all_goals
    intro f h
    simp only [Bool.and_eq_true] at h
    exact h.1.1

def armsFast (i : Input) (q : Site i) : List (Arm i) :=
  let frames := if q.val.node.isDuplicateLeaf then [] else neighborsFast i q
  frames.attach.map fun f =>
    ⟨⟨f.val,by
      apply i.certified.mem_localizedOccurrences_of_mem_intendedLocalizedRerootChildFrames ⟨q,none⟩
      simpa only [frames,intendedLocalizedRerootChildFrames,neighborsFast_eq] using f.property⟩,some q⟩

private theorem attachMap_congr {α β : Type} (xs ys : List α) (same : xs = ys)
    (f : {x // x ∈ xs} → β) (g : {x // x ∈ ys} → β)
    (pointwise : ∀ x hx hy, f ⟨x,hx⟩ = g ⟨x,hy⟩) : xs.attach.map f = ys.attach.map g := by
  subst ys
  apply List.map_congr_left
  intro entry _
  exact pointwise entry.val entry.property entry.property

private theorem armsFast_eq (i : Input) (q : Site i) : armsFast i q = RingRetainedAuxiliary.frame i.certified q := by
  unfold armsFast RingRetainedAuxiliary.frame executableLocalizedRerootChildren
  apply attachMap_congr
  · simp only [intendedLocalizedRerootChildFrames,neighborsFast_eq]
  · intros; rfl

private def frameWith? (i : Input) (q : Site i) (arms : List (Arm i))
    (exactArms : arms = RingRetainedAuxiliary.frame i.certified q) : Option (Frame i q) := do
  let ⟨c,hc⟩ ← (i.certified.localizedOccurrenceDescriptorCenter? q).attach
  if four : arms.length = 4 then
    let ⟨ids,hi⟩ ← (arms.mapM (fun (a : Arm i) => a.occurrence.val.node.current?.map Fin.val)).attach
    if p : ids.Perm (RingRetainedAuxiliary.canonical i.certified c) then
      return ⟨c,hc,by simpa only [exactArms] using four,ids,by simpa only [exactArms] using hi,p⟩
  none

private theorem frameWith_eq (i : Input) (q : Site i) (arms : List (Arm i))
    (exactArms : arms = RingRetainedAuxiliary.frame i.certified q) :
    frameWith? i q arms exactArms = RingNestedActivePair.frame? i q := by
  subst arms
  rfl

private def scoreWith {i : Input} {q : Site i} (fr : Frame i q) (arms : List (Arm i)) (k : Slot) :=
  let id := (fr.atoms [k]).head!
  [[atomicNumber i.molecule id],
    if (arms[k.val]?).any (fun a => a.occurrence.val.node.provenance == .realAtom) then
      shell i.molecule fr.center.val.val id else []]

private theorem scoreWith_eq {i : Input} {q : Site i} (fr : Frame i q) (arms : List (Arm i))
    (exactArms : arms = RingRetainedAuxiliary.frame i.certified q) (k : Slot) : scoreWith fr arms k = score fr k := by
  subst arms
  have bound : k.val < (RingRetainedAuxiliary.frame i.certified q).length := by rw [fr.four]; exact k.isLt
  simp [scoreWith,score,RingNestedActivePair.Frame.arm,List.getElem?_eq_getElem bound]

private def snapshot {i : Input} {q : Site i} (fr : Frame i q) (arms : List (Arm i)) : Slot → List (List Nat) :=
  let a := scoreWith fr arms 0
  let b := scoreWith fr arms 1
  let c := scoreWith fr arms 2
  let d := scoreWith fr arms 3
  ![a,b,c,d]

private theorem snapshot_eq {i : Input} {q : Site i} (fr : Frame i q) (arms : List (Arm i))
    (exactArms : arms = RingRetainedAuxiliary.frame i.certified q) : snapshot fr arms = score fr := by
  funext k
  fin_cases k <;> simp [snapshot,scoreWith_eq fr arms exactArms]

/-- Equivalent executable with one original-root materialization and four cached scores. -/
def direct? (i : Input) (q : Site i) : Option RingNestedActivePair.Labels := do
  let arms := armsFast i q
  let fr ← frameWith? i q arms (armsFast_eq i q)
  let values := snapshot fr arms
  let row := RingStereoSiblingPass.order values (List.finRange 4)
  if row.Pairwise (fun a b => values b < values a) then
    (readback? (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified) (fr.atoms row)).map
      fun h => (.chiral h,.chiral h.swap)
  else none

/-- Caching and root-local enumeration preserve every success and failure. -/
theorem direct_eq_reference (i : Input) (q : Site i) : direct? i q = reference? i q := by
  unfold direct? reference?
  simp only [frameWith_eq]
  apply congrArg (fun f => (RingNestedActivePair.frame? i q).bind f)
  funext fr
  rw [snapshot_eq fr _ (armsFast_eq i q)]
  simp only [row?]
  split <;> rfl

theorem direct_sound {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (q : Site i) {labels : RingNestedActivePair.Labels} (hit : direct? i q = some labels) :
    RingChemicalGraphProof.state i q = some (some labels) :=
  reference_sound geom q (by simpa only [direct_eq_reference] using hit)

end TetraStereo.Engine.RingSecondShellDecision
assert_kernel_only TetraStereo.Engine.RingSecondShellDecision.shell_graphWord
assert_kernel_only TetraStereo.Engine.RingSecondShellDecision.direct_sound
assert_kernel_only TetraStereo.Engine.RingSecondShellDecision.score_physical
assert_kernel_only TetraStereo.Engine.RingSecondShellDecision.prefixFor_physical
assert_kernel_only TetraStereo.Engine.RingSecondShellDecision.direct_eq_reference
