import TetraStereo.Engine.RingMarkedTypeRecovery
import TetraStereo.Engine.RingMarkedTreeOrder
import TetraStereo.Engine.RingOrdinaryLigandInventory
import TetraStereo.Engine.RingFullPathTrialParity

/-! The unordered tree of through-4c types and occurrences of the selected
atom characterizes a public Rule 6 comparison after an ordinary tie. -/
set_option autoImplicit false

namespace TetraStereo.Engine.RingMarkedLigandTree
open OneCenter RingMarkedTreeFold
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader Frame)
open RingRule5Shape (Valid On kids)
open RingRetainedChemicalTrace (Word)
open RingActivePairReport (Slot)
open RingFullPathTrialReadings (markWords? trialKey readTrial)
open private flatMap_keys from TetraStereo.Engine.RingReferenceGroupTransport
open private trial_eq from TetraStereo.Engine.RingFullPathTrialParity

/-- A native tie recovers the entire marked ligand, truncated at any requested depth. -/
theorem view_of_tie {i : Input} {f : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready f r)
    (left right : Nat) (n : Nat) (a b : Arm i) (va : Valid a) (vb : Valid b)
    (oa : On f a) (ob : On f b)
    (equal : RingMarkedTypeRecovery.key i r left a = RingMarkedTypeRecovery.key i r right b) :
    view i r left n a = view i r right n b := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    obtain ⟨perm,prior,marks⟩ := RingMarkedTypeRecovery.same_children ready left right a b va vb oa ob equal
    apply Prod.ext
    · exact Prod.ext prior marks
    · apply Quot.sound
      have rows := flatMap_keys (RingMarkedTypeRecovery.key i r left) (RingMarkedTypeRecovery.key i r right)
        (fun c => [view i r left n c]) (fun c => [view i r right n c]) perm (by
          intro x hx y hy matchKeys
          have ca := i.certified.executableLocalizedRerootChildren_declarative a
          have cb := i.certified.executableLocalizedRerootChildren_declarative b
          have h := ih x y (i.certified.localizedRerootChild_valid _ _ _ ca hx)
            (i.certified.localizedRerootChild_valid _ _ _ cb hy)
            ((i.certified.localizedRerootChildren_root_eq _ _ _ ca hx).trans oa)
            ((i.certified.localizedRerootChildren_root_eq _ _ _ cb hy).trans ob) matchKeys
          exact List.Perm.of_eq (congrArg List.singleton h))
      simpa only [← List.map_eq_flatMap] using rows

/-- The depth needed to cover both actual rerooted arms. -/
def depth {i : Input} (a b : Arm i) : Nat :=
  max (i.certified.localizedRerootCursorBudget a) (i.certified.localizedRerootCursorBudget b) + 1

open private key_read from TetraStereo.Engine.RingMarkedTypeRecovery

private theorem prior_of_read {i f r rev q p atom} (ready : @RingGroupedStereo.Ready i f r)
    (v : Valid q) (o : On f q) (h : RingGroupedMark.OnGeometry i r rev atom q p) :
    p.priorDeep = RingRule5Shape.key i r rev q := by
  cases h with
  | node before _ _ _ _ _ =>
    obtain ⟨d,hd⟩ := RingOccurrenceStereo.rank_total ready rev [.lowercase] q v o
    change RingRetainedStereoRefinement.priority i r rev [.lowercase] q = some d at hd
    obtain rfl := RingRetainedStereoRefinement.unique [.lowercase] _ _ _ before
      (RingRetainedStereoRefinement.source _ _ hd)
    simp [RingRetainedStereoRefinement.extend,RingRule5Shape.key,hd]

/-- Complete native marked priorities agree exactly on equal unordered typed trees. -/
theorem marked_tie_iff {i f r} (ready : @RingGroupedStereo.Ready i f r)
    (left right : Nat) (a b : Arm i) (va : Valid a) (vb : Valid b) (oa : On f a) (ob : On f b) :
    RingMarkedTypeRecovery.key i r left a = RingMarkedTypeRecovery.key i r right b ↔
      view i r left (depth a b) a = view i r right (depth a b) b := by
  refine ⟨view_of_tie ready left right _ a b va vb oa ob,?_⟩
  intro tree
  obtain ⟨x,hx⟩ := RingGroupedMark.arm_ready ready left a va oa
  obtain ⟨y,hy⟩ := RingGroupedMark.arm_ready ready right b vb ob
  have ba : i.certified.localizedRerootCursorBudget a < depth a b := Nat.lt_succ_of_le (Nat.le_max_left ..)
  have bb : i.certified.localizedRerootCursorBudget b < depth a b := Nat.lt_succ_of_le (Nat.le_max_right ..)
  have branches := RingMarkedTreeFold.reading_eq ready (depth a b) va vb oa ob ba bb tree
    (RingGroupedMark.arm_source hx).2 (RingGroupedMark.arm_source hy).2
  simp [RingMarkedTypeRecovery.key,hx,hy,branches]

/-- Molecular data shared by two arms after giving a physical atom preference. -/
def sameArms {i : Input} (r : Reader i) (rev : Bool) (atom : Nat) (a b : Arm i) : Prop :=
  RingOrdinaryLigandInventory.observe? i r rev a = RingOrdinaryLigandInventory.observe? i r rev b ∧
    view i r atom (depth a b) a = view i r atom (depth a b) b

/-- A pair of real ligand rows uses the same marked comparison in both the
four-coordinate and the pyramidal trial. This covers either geometry. -/
theorem arm_trial_tie_iff {i f r} (ready : @RingGroupedStereo.Ready i f r)
    (rev : Bool) (atom : Nat) (a b : Arm i) (va : Valid a) (vb : Valid b)
    (oa : On f a) (ob : On f b) {ka kb x y}
    (ha : RingFullPathEligibility.key? i r rev a = some ka)
    (hb : RingFullPathEligibility.key? i r rev b = some kb)
    (ma : RingGroupedMark.Reading i r atom a x) (mb : RingGroupedMark.Reading i r atom b y) :
    trialKey ka x.word = trialKey kb y.word ↔ sameArms r rev atom a b := by
  have inv := RingOrdinaryLigandInventory.tie_iff ready rev a b va vb oa ob
  rw [ha,hb,Option.some.injEq] at inv
  have base {q p k} (v : Valid q) (o : On f q) (h : RingFullPathEligibility.key? i r rev q = some k)
      (m : RingGroupedMark.Reading i r atom q p) : p.priorDeep = k.throughFourA ++ [k.fourC] := by
    obtain ⟨d,hd,src⟩ := RingFullPathEligibility.key_exact ready rev q v o
    have marked : RingGroupedMark.OnGeometry i r rev atom q p := by
      cases rev
      · exact m
      · exact m.reflect
    exact (prior_of_read ready v o marked).trans
      (RingRule5Tie.reading_key ready v o ((src _).mpr (Option.some.inj (h.symm.trans hd))))
  have tree := marked_tie_iff ready atom atom a b va vb oa ob
  rw [key_read ma ready va oa,key_read mb ready vb ob] at tree
  rw [trial_eq]
  constructor
  · rintro ⟨keys,words⟩
    refine ⟨inv.mp keys,tree.mp ?_⟩
    have earlier := (base va oa ha ma).trans (keys ▸ (base vb ob hb mb).symm)
    exact congrArg₂ List.append earlier (congrArg List.singleton words)
  · rintro ⟨obs,shape⟩
    refine ⟨inv.mpr obs,?_⟩
    simpa [RingStereoSiblingPass.Branch.deep] using congrArg List.getLast? (tree.mpr shape)

/-- Read a full marked trial priority from the ordinary signed inventory
and the typed marked tree. The decoder has no molecule, reader or atom ID. -/
def trialFromTree (n : Nat) (ordinary : Option RingOrdinaryLigandInventory.Observation)
    (shape : Shape n) : Option (List (List Word)) := do
  let obs ← ordinary
  let branch ← RingMarkedTreeOrder.reconstruct n shape
  return trialKey (RingOrdinaryLigandInventory.assemble obs) branch.word

theorem trialFromTree_exact {i f r} (ready : @RingGroupedStereo.Ready i f r)
    (rev : Bool) (atom n : Nat) (q : Arm i) (v : Valid q) (o : On f q)
    (budget : i.certified.localizedRerootCursorBudget q < n) :
    trialFromTree n (RingOrdinaryLigandInventory.observe? i r rev q) (view i r atom n q) =
      (do let k ← RingFullPathEligibility.key? i r rev q
          let e ← RingGroupedMark.arm? i r atom q
          return trialKey k e.2.word) := by
  rw [← RingOrdinaryLigandInventory.key_exact,
    trialFromTree,RingMarkedTreeOrder.reconstruct_arm ready n q atom v o budget]
  unfold RingOrdinaryLigandInventory.key?
  cases RingOrdinaryLigandInventory.observe? i r rev q <;>
    cases RingGroupedMark.arm? i r atom q <;> rfl

abbrev sameSlots {i f} (fr : @Frame i f) (r : Reader i) (rev : Bool) (s j k : Slot) : Prop :=
  sameArms r rev (RingGroupedTrials.atom fr s) (RingGroupedCentre.cursor fr j) (RingGroupedCentre.cursor fr k)

/-- A tie in the actual four-slot reader. -/
theorem trial_tie_iff {i f r} (fr : @Frame i f) (ready : RingGroupedStereo.Ready f r)
    (rev : Bool) (s j k : Slot) {ks ws}
    (ordinary : RingFullPathPublication.keys? fr r rev = some ks)
    (promoted : markWords? fr r (some s) = some ws) :
    trialKey (ks j) (ws j) = trialKey (ks k) (ws k) ↔ sameSlots fr r rev s j k := by
  obtain ⟨m,hm⟩ := Option.isSome_iff_exists.mp (RingGroupedTrials.marking_ready fr ready s)
  have wsEq : ws = m.word := by simpa [markWords?,hm] using promoted.symm
  rw [wsEq]
  exact arm_trial_tie_iff ready rev _ _ _ (RingGroupedCentre.valid fr j) (RingGroupedCentre.valid fr k)
    (fr.direction j).property.1 (fr.direction k).property.1
    (RingActivePairReport.four_at ordinary j) (RingActivePairReport.four_at ordinary k)
    (m.source j) (m.source k)

/-- On a public root or auxiliary store, a marked tetrahedral trial returns no hand
exactly when two distinct slots share the ordinary inventory and the marked tree. -/
theorem public_refusal_iff {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {root : i.certified.Atom} {stage : Nat} {f : Site i} (called : RingGlobalComparison.Called i root stage f)
    (fr : Frame i f) (rev : Bool) (s : Slot) {ks ws}
    (ordinary : RingFullPathPublication.keys? fr (RingGlobalComparison.prior i root stage) rev = some ks)
    (promoted : markWords? fr (RingGlobalComparison.prior i root stage) (some s) = some ws) :
    readTrial fr rev (fun k => trialKey (ks k) (ws k)) = none ↔
      ∃ j k, j ≠ k ∧ sameSlots fr (RingGlobalComparison.prior i root stage) rev s j k := by
  rw [RingGlobalComparison.prior_exact called] at ordinary promoted ⊢
  have pair := fun j k => trial_tie_iff fr (RingChemicalGraphProof.ready geom f) rev s j k ordinary promoted
  have law := RingFullPathTrialReadings.read_exact geom fr rev (fun k => trialKey (ks k) (ws k)) none
  constructor
  · intro h
    cases law.mpr h.symm with
    | tie ne same => exact ⟨_,_,ne,(pair _ _).mp same⟩
  · rintro ⟨j,k,ne,same⟩
    exact (law.mp (.tie ne ((pair j k).mpr same))).symm

end TetraStereo.Engine.RingMarkedLigandTree

assert_kernel_only TetraStereo.Engine.RingMarkedLigandTree.marked_tie_iff
assert_kernel_only TetraStereo.Engine.RingMarkedLigandTree.public_refusal_iff
assert_kernel_only TetraStereo.Engine.RingMarkedLigandTree.trialFromTree_exact
