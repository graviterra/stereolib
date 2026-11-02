import TetraStereo.OneCenter.LocalizedHiddenParityMarkedProbe
import TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation
import TetraStereo.KernelOnly
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 0

/-!
# Geometry readback of marked far rankings and a mark-indexed temporary near recalculation

**Experimental adapter.** This module examines the expressly non-recommended promotion-indexed
auxiliary recalculation on the accepted 15-atom cage, using only existing runtime calls
(`occurrenceLigandFrame?`, `rankOccurrencePositionsThroughRule6Tracked?`) and the accepted
certified coordinates of the physical family `certifiedWith P len`. Nothing here is the ordinary
generated `referenceState`, no production default changes, and no ordinary `Label` evidence is
created for the temporary values. No chemical sanction is claimed.

1. `rankingReadback?` is a generic geometry readback of a strict tracked ranking: returned
   positions (read as descending priority, the same reading the production constructor applies
   through `permutationIsEven`) → actual frame atom IDs → certified source coordinates →
   `descriptorOfPriorityOrderedPoints?`. The six off-diagonal far outputs of the accepted probe are
   pinned by kernel reduction and their letters are **derived**: each far readback volume is
   `± ligandVolumeWith P len k8` by an exact algebraic identity, so the raw letter is a function of
   the far bridgehead's volume sign for every nondegenerate table of the family.
2. `tempStateA r first uppercase` is one mark-indexed temporary snapshot: facts at exactly the two
   off-diagonal far occurrence keys `[8, o, 3, 0]`, `o ≠ r`, carrying the derived opposite raw
   letters. The case bit is an explicit parameter (`uppercase`); it is never chosen by the desired
   physical output. `nearTrackedWith?` feeds the snapshot into the **existing** near ranking call.
3. The near outputs are pinned by kernel reduction and read back geometrically. For every
   nondegenerate table of the family, every permitted mark and both case policies, the near
   recalculated raw letter is the letter of
   the volume product `ligandVolumeWith k3 * ligandVolumeWith k8`: it *is* the joint bridgehead
   sign bit. Cage B is treated identically, and the two near letters agree iff the root is not
   pairwise properly distinguishable (`family_root_classification`).
-/

namespace TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback

open TetraStereo.OneCenter
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.OneCenter.CartesianPoint3
open TetraStereo.OneCenter.DeclarativeCIP
open TetraStereo.OneCenter.DeclarativeCIP.ProductionOccurrenceRules456
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCompletion
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation
open TetraStereo.OneCenter.LocalizedHiddenParityMarkedProbe
open TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry

/-! ## Generic geometry readback of a strict tracked ranking -/

/-- Actual frame atom identifiers in frame order. -/
def frameAtoms (roots : List CanonicalRerootCursor) : List Nat :=
  roots.map fun cursor => cursor.node.atom

/-- Atom identifiers in the returned priority order of a strict ranking; `none` for a non-strict
one. -/
def rankedAtomsOf? (atoms : List Nat) (ranking : Rule6TrackedRanking) : Option (List Nat) :=
  if ranking.unique then ranking.positions.mapM fun position => atoms[position]? else none

/-- Frame atoms in the returned priority order of a strict ranking. -/
def rankedAtoms? (roots : List CanonicalRerootCursor) (ranking : Rule6TrackedRanking) :
    Option (List Nat) :=
  rankedAtomsOf? (frameAtoms roots) ranking

/-- The accepted probe's frame-atom projection is the frame map. -/
theorem frameAtoms?_eq (node : RawMolecule.CanonicalBranchNode) :
    frameAtoms? node = (frame? node).map frameAtoms := rfl

/-- Certified source coordinate of a runtime atom identifier of the family member `P`. -/
def pointOf? (P : List CartesianPoint3) (len : P.length = 15) (atom : Nat) :
    Option CartesianPoint3 :=
  if h : atom < 15 then some (posWith P len ⟨atom, h⟩) else none

theorem pointOf?_spatial (P : List CartesianPoint3) (len : P.length = 15) (atom : Fin 15) :
    pointOf? P len atom.val = (certifiedWith P len).spatialPointAt? atom := by
  rw [sourcePointAtWith]
  simp [pointOf?, atom.isLt]

/-- Certified points in returned priority order. -/
def rankedPoints? (P : List CartesianPoint3) (len : P.length = 15)
    (roots : List CanonicalRerootCursor) (ranking : Rule6TrackedRanking) :
    Option (List CartesianPoint3) := do
  let atoms ← rankedAtoms? roots ranking
  atoms.mapM (pointOf? P len)

/-- **Generic geometry readback**: the raw `R/S` of a strict tracked ranking from the certified
coordinates of its frame atoms in returned priority order. -/
def rankingReadback? (P : List CartesianPoint3) (len : P.length = 15)
    (roots : List CanonicalRerootCursor) (ranking : Rule6TrackedRanking) : Option RS := do
  let points ← rankedPoints? P len roots ranking
  descriptorOfPriorityOrderedPoints? points

/-- A successful readback is the independent geometric relation on the ranked certified points. -/
theorem rankingReadback?_sound (P : List CartesianPoint3) (len : P.length = 15)
    (roots : List CanonicalRerootCursor) (ranking : Rule6TrackedRanking) (letter : RS)
    (read : rankingReadback? P len roots ranking = some letter) :
    ∃ points, rankedPoints? P len roots ranking = some points ∧
      RationalTetrahedralDescriptor points letter := by
  unfold rankingReadback? at read
  cases h : rankedPoints? P len roots ranking with
  | none => rw [h] at read; cases read
  | some points =>
      rw [h] at read
      exact ⟨points, rfl, (descriptorOfPriorityOrderedPoints?_eq_some_iff points letter).mp read⟩

/-- The letter determined by a nonzero oriented volume: negative is `R`, positive is `S`. -/
def letterOfVolume (volume : ℚ) : RS := if volume < 0 then RS.R else RS.S

theorem descriptorOfOrientedVolume?_of_ne {volume : ℚ} (nonzero : volume ≠ 0) :
    descriptorOfOrientedVolume? volume = some (letterOfVolume volume) := by
  unfold descriptorOfOrientedVolume? letterOfVolume
  rcases lt_or_gt_of_ne nonzero with negative | positive
  · simp [negative]
  · simp [positive, not_lt.mpr positive.le]

theorem letterOfVolume_neg {volume : ℚ} (nonzero : volume ≠ 0) :
    letterOfVolume (-volume) = (letterOfVolume volume).swap := by
  unfold letterOfVolume
  rcases lt_or_gt_of_ne nonzero with negative | positive
  · simp [negative, not_lt.mpr negative.le, RS.swap]
  · simp [positive, not_lt.mpr positive.le, RS.swap]

theorem letterOfVolume_mul_of_neg {a b : ℚ} (ha : a ≠ 0) (hb : b < 0) :
    letterOfVolume (a * b) = letterOfVolume (-a) := by
  unfold letterOfVolume
  rcases lt_or_gt_of_ne ha with h | h
  · have h1 : ¬ a * b < 0 := not_lt.mpr (mul_pos_of_neg_of_neg h hb).le
    have h2 : ¬ -a < 0 := by linarith
    simp [h1, h2]
  · have h1 : a * b < 0 := mul_neg_of_pos_of_neg h hb
    have h2 : -a < 0 := by linarith
    simp [h1, h2]

theorem letterOfVolume_mul_of_pos {a b : ℚ} (ha : a ≠ 0) (hb : 0 < b) :
    letterOfVolume (a * b) = letterOfVolume a := by
  unfold letterOfVolume
  rcases lt_or_gt_of_ne ha with h | h
  · have h1 : a * b < 0 := mul_neg_of_neg_of_pos h hb
    simp [h1, h]
  · have h1 : ¬ a * b < 0 := not_lt.mpr (mul_pos h hb).le
    simp [h1, not_lt.mpr h.le]

theorem letterOfVolume_eq_iff (a b : ℚ) :
    letterOfVolume a = letterOfVolume b ↔ (a < 0 ↔ b < 0) := by
  unfold letterOfVolume
  by_cases ha : a < 0 <;> by_cases hb : b < 0 <;> simp [ha, hb]

/-! ## Cage A: the actual off-diagonal far outputs (accepted probe call), pinned -/

theorem far_o5_mark7 : tracked? (farA 5) 7 =
    some { positions := [0, 3, 2, 1], unique := true, pseudoComparisons := 1 } := by
  decide +kernel

theorem far_o6_mark5 : tracked? (farA 6) 5 =
    some { positions := [0, 2, 3, 1], unique := true, pseudoComparisons := 1 } := by
  decide +kernel

theorem far_o6_mark7 : tracked? (farA 6) 7 =
    some { positions := [0, 3, 2, 1], unique := true, pseudoComparisons := 1 } := by
  decide +kernel

theorem far_o7_mark5 : tracked? (farA 7) 5 =
    some { positions := [0, 2, 3, 1], unique := true, pseudoComparisons := 1 } := by
  decide +kernel

theorem far_o7_mark6 : tracked? (farA 7) 6 =
    some { positions := [0, 3, 2, 1], unique := true, pseudoComparisons := 1 } := by
  decide +kernel

/-- Frame atoms of a visit in the returned priority order of a mark (accepted probe call). -/
def visitRankedAtoms? (node : RawMolecule.CanonicalBranchNode) (r : Nat) : Option (List Nat) := do
  let atoms ← frameAtoms? node
  let ranking ← tracked? node r
  rankedAtomsOf? atoms ranking

/-! The six far atom orders follow from the pinned tracked outputs and the accepted frame pins by
rewriting; no ranking is recomputed. -/

theorem farRankedAtoms_56 : visitRankedAtoms? (farA 5) 6 = some [5, 6, 7, 4] := by
  unfold visitRankedAtoms?; rw [farA5_frameAtoms, far_o5_mark6_tracked_output]; rfl
theorem farRankedAtoms_57 : visitRankedAtoms? (farA 5) 7 = some [5, 7, 6, 4] := by
  unfold visitRankedAtoms?; rw [farA5_frameAtoms, far_o5_mark7]; rfl
theorem farRankedAtoms_65 : visitRankedAtoms? (farA 6) 5 = some [6, 5, 7, 4] := by
  unfold visitRankedAtoms?; rw [farA6_frameAtoms, far_o6_mark5]; rfl
theorem farRankedAtoms_67 : visitRankedAtoms? (farA 6) 7 = some [6, 7, 5, 4] := by
  unfold visitRankedAtoms?; rw [farA6_frameAtoms, far_o6_mark7]; rfl
theorem farRankedAtoms_75 : visitRankedAtoms? (farA 7) 5 = some [7, 5, 6, 4] := by
  unfold visitRankedAtoms?; rw [farA7_frameAtoms, far_o7_mark5]; rfl
theorem farRankedAtoms_76 : visitRankedAtoms? (farA 7) 6 = some [7, 6, 5, 4] := by
  unfold visitRankedAtoms?; rw [farA7_frameAtoms, far_o7_mark6]; rfl

/-- Raw geometric letter of a visit under a mark on the family member `P`: the generic readback on
the actual frame and the actual tracked ranking. -/
def visitReadback? (P : List CartesianPoint3) (len : P.length = 15)
    (node : RawMolecule.CanonicalBranchNode) (r : Nat) : Option RS := do
  let atoms ← visitRankedAtoms? node r
  let points ← atoms.mapM (pointOf? P len)
  descriptorOfPriorityOrderedPoints? points

theorem visitReadback?_eq_generic (P : List CartesianPoint3) (len : P.length = 15)
    (node : RawMolecule.CanonicalBranchNode) (r : Nat) :
    visitReadback? P len node r =
      (frame? node).bind fun roots => (tracked? node r).bind fun ranking =>
        rankingReadback? P len roots ranking := by
  unfold visitReadback? visitRankedAtoms? rankingReadback? rankedPoints? rankedAtoms?
  rw [frameAtoms?_eq]
  cases frame? node with
  | none => rfl
  | some roots =>
      cases tracked? node r with
      | none => rfl
      | some ranking =>
          show (rankedAtomsOf? (frameAtoms roots) ranking).bind
              (fun atoms => (atoms.mapM (pointOf? P len)).bind
                descriptorOfPriorityOrderedPoints?) =
            ((rankedAtomsOf? (frameAtoms roots) ranking).bind
              fun atoms => atoms.mapM (pointOf? P len)).bind descriptorOfPriorityOrderedPoints?
          cases rankedAtomsOf? (frameAtoms roots) ranking <;> rfl

section Family

variable (P : List CartesianPoint3) (len : P.length = 15)

/-! ### Exact volume identities: each far readback volume is `± ligandVolumeWith P len k8` -/

theorem vol8_canonical :
    ligandVolumeWith P len k8 =
      orientedVolume (posWith P len 4) (posWith P len 5) (posWith P len 6) (posWith P len 7) := by
  simp only [ligandVolumeWith, lig8.1, lig8.2.1, lig8.2.2.1, lig8.2.2.2]

theorem vol_5674 :
    orientedVolume (posWith P len 5) (posWith P len 6) (posWith P len 7) (posWith P len 4) =
      - ligandVolumeWith P len k8 := by
  rw [vol8_canonical]; simp only [orientedVolume]; ring

theorem vol_5764 :
    orientedVolume (posWith P len 5) (posWith P len 7) (posWith P len 6) (posWith P len 4) =
      ligandVolumeWith P len k8 := by
  rw [vol8_canonical]; simp only [orientedVolume]; ring

theorem vol_6574 :
    orientedVolume (posWith P len 6) (posWith P len 5) (posWith P len 7) (posWith P len 4) =
      ligandVolumeWith P len k8 := by
  rw [vol8_canonical]; simp only [orientedVolume]; ring

theorem vol_6754 :
    orientedVolume (posWith P len 6) (posWith P len 7) (posWith P len 5) (posWith P len 4) =
      - ligandVolumeWith P len k8 := by
  rw [vol8_canonical]; simp only [orientedVolume]; ring

theorem vol_7564 :
    orientedVolume (posWith P len 7) (posWith P len 5) (posWith P len 6) (posWith P len 4) =
      - ligandVolumeWith P len k8 := by
  rw [vol8_canonical]; simp only [orientedVolume]; ring

theorem vol_7654 :
    orientedVolume (posWith P len 7) (posWith P len 6) (posWith P len 5) (posWith P len 4) =
      ligandVolumeWith P len k8 := by
  rw [vol8_canonical]; simp only [orientedVolume]; ring

/-! ### Derived far letters, for every table of the family -/

theorem farReadback_56 :
    visitReadback? P len (farA 5) 6 = descriptorOfOrientedVolume? (- ligandVolumeWith P len k8) := by
  unfold visitReadback?
  rw [farRankedAtoms_56]
  show descriptorOfOrientedVolume? (orientedVolume (posWith P len 5) (posWith P len 6)
    (posWith P len 7) (posWith P len 4)) = _
  rw [vol_5674]

theorem farReadback_57 :
    visitReadback? P len (farA 5) 7 = descriptorOfOrientedVolume? (ligandVolumeWith P len k8) := by
  unfold visitReadback?
  rw [farRankedAtoms_57]
  show descriptorOfOrientedVolume? (orientedVolume (posWith P len 5) (posWith P len 7)
    (posWith P len 6) (posWith P len 4)) = _
  rw [vol_5764]

theorem farReadback_65 :
    visitReadback? P len (farA 6) 5 = descriptorOfOrientedVolume? (ligandVolumeWith P len k8) := by
  unfold visitReadback?
  rw [farRankedAtoms_65]
  show descriptorOfOrientedVolume? (orientedVolume (posWith P len 6) (posWith P len 5)
    (posWith P len 7) (posWith P len 4)) = _
  rw [vol_6574]

theorem farReadback_67 :
    visitReadback? P len (farA 6) 7 = descriptorOfOrientedVolume? (- ligandVolumeWith P len k8) := by
  unfold visitReadback?
  rw [farRankedAtoms_67]
  show descriptorOfOrientedVolume? (orientedVolume (posWith P len 6) (posWith P len 7)
    (posWith P len 5) (posWith P len 4)) = _
  rw [vol_6754]

theorem farReadback_75 :
    visitReadback? P len (farA 7) 5 = descriptorOfOrientedVolume? (- ligandVolumeWith P len k8) := by
  unfold visitReadback?
  rw [farRankedAtoms_75]
  show descriptorOfOrientedVolume? (orientedVolume (posWith P len 7) (posWith P len 5)
    (posWith P len 6) (posWith P len 4)) = _
  rw [vol_7564]

theorem farReadback_76 :
    visitReadback? P len (farA 7) 6 = descriptorOfOrientedVolume? (ligandVolumeWith P len k8) := by
  unfold visitReadback?
  rw [farRankedAtoms_76]
  show descriptorOfOrientedVolume? (orientedVolume (posWith P len 7) (posWith P len 6)
    (posWith P len 5) (posWith P len 4)) = _
  rw [vol_7654]

/-- The far letter of cage A: `R` iff the far bridgehead volume is negative. -/
noncomputable abbrev farLetterA : RS := letterOfVolume (ligandVolumeWith P len k8)

/-- **For a fixed mark the two off-diagonal far readbacks are opposite letters**, each determined
by the far bridgehead volume sign: mark `5` reads the far letter at `o = 6` and its complement at
`o = 7`; mark `6` reads the complement at `o = 5` and the far letter at `o = 7`; mark `7` reads the
far letter at `o = 5` and the complement at `o = 6`. -/
theorem farReadbackA_letters (nondeg : Nondegenerate P len) :
    visitReadback? P len (farA 6) 5 = some (farLetterA P len) ∧
    visitReadback? P len (farA 7) 5 = some (farLetterA P len).swap ∧
    visitReadback? P len (farA 5) 6 = some (farLetterA P len).swap ∧
    visitReadback? P len (farA 7) 6 = some (farLetterA P len) ∧
    visitReadback? P len (farA 5) 7 = some (farLetterA P len) ∧
    visitReadback? P len (farA 6) 7 = some (farLetterA P len).swap := by
  have nonzero := nondeg k8
  have negNonzero : - ligandVolumeWith P len k8 ≠ 0 := neg_ne_zero.mpr nonzero
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [farReadback_65, descriptorOfOrientedVolume?_of_ne nonzero]
  · rw [farReadback_75, descriptorOfOrientedVolume?_of_ne negNonzero, letterOfVolume_neg nonzero]
  · rw [farReadback_56, descriptorOfOrientedVolume?_of_ne negNonzero, letterOfVolume_neg nonzero]
  · rw [farReadback_76, descriptorOfOrientedVolume?_of_ne nonzero]
  · rw [farReadback_57, descriptorOfOrientedVolume?_of_ne nonzero]
  · rw [farReadback_67, descriptorOfOrientedVolume?_of_ne negNonzero, letterOfVolume_neg nonzero]

end Family

/-! ## One mark-indexed temporary auxiliary snapshot (cage A) -/

/-- A temporary fact at an exact occurrence key (real atom). The case bit is an explicit
parameter. -/
def tempFact (node : RawMolecule.CanonicalBranchNode) (letter : RS) (uppercase : Bool) :
    OccurrenceAuxFact :=
  { key := canonicalOccurrenceKey node, atom := node.atom, descriptor := letter,
    uppercase := uppercase, priorityPositions := [] }

/-- The two off-diagonal oxygens of a cage-A mark, in increasing order. -/
def offDiagonalA : Nat → List Nat
  | 5 => [6, 7]
  | 6 => [5, 7]
  | 7 => [5, 6]
  | _ => []

/-- **Mark-indexed temporary snapshot** for cage-A mark `r`: facts at exactly the two off-diagonal
far visits `[8, o, 3, 0]`, `o ≠ r`. The smaller oxygen carries `first`, the larger its complement.
No fact is installed at the diagonal visit, the near occurrence or the root. -/
def tempStateA (r : Nat) (first : RS) (uppercase : Bool) : OccurrenceAuxState :=
  match offDiagonalA r with
  | [o₁, o₂] => [tempFact (farA o₁) first uppercase, tempFact (farA o₂) first.swap uppercase]
  | _ => []

/-- The computed snapshot of a family member under a case policy: `first` is the derived letter of
the smaller off-diagonal visit (`farReadbackA_letters`). -/
noncomputable def computedStateA (P : List CartesianPoint3) (len : P.length = 15) (r : Nat)
    (uppercase : Bool) : OccurrenceAuxState :=
  match r with
  | 5 => tempStateA 5 (farLetterA P len) uppercase
  | 6 => tempStateA 6 (farLetterA P len).swap uppercase
  | 7 => tempStateA 7 (farLetterA P len) uppercase
  | _ => []

/-! ### Exact occurrence-key readback of the snapshot -/

theorem tempStateA5_reads (first : RS) (uppercase : Bool) :
    (tempStateA 5 first uppercase).factAt? (farA 5) = none ∧
    (tempStateA 5 first uppercase).factAt? (farA 6) = some (tempFact (farA 6) first uppercase) ∧
    (tempStateA 5 first uppercase).factAt? (farA 7) =
      some (tempFact (farA 7) first.swap uppercase) := by
  cases first <;> cases uppercase <;> decide

theorem tempStateA6_reads (first : RS) (uppercase : Bool) :
    (tempStateA 6 first uppercase).factAt? (farA 6) = none ∧
    (tempStateA 6 first uppercase).factAt? (farA 5) = some (tempFact (farA 5) first uppercase) ∧
    (tempStateA 6 first uppercase).factAt? (farA 7) =
      some (tempFact (farA 7) first.swap uppercase) := by
  cases first <;> cases uppercase <;> decide

theorem tempStateA7_reads (first : RS) (uppercase : Bool) :
    (tempStateA 7 first uppercase).factAt? (farA 7) = none ∧
    (tempStateA 7 first uppercase).factAt? (farA 5) = some (tempFact (farA 5) first uppercase) ∧
    (tempStateA 7 first uppercase).factAt? (farA 6) =
      some (tempFact (farA 6) first.swap uppercase) := by
  cases first <;> cases uppercase <;> decide

/-- No temporary fact is read at the near occurrence itself or at the root. -/
theorem tempStateA_near_root_none (r : Nat) (hr : r ∈ [5, 6, 7]) (first : RS) (uppercase : Bool) :
    (tempStateA r first uppercase).factAt? nearA = none ∧
    (tempStateA r first uppercase).factAt? root0 = none := by
  have cases : r = 5 ∨ r = 6 ∨ r = 7 := by simpa using hr
  rcases cases with rfl | rfl | rfl <;> cases first <;> cases uppercase <;> decide

/-! ## The existing near ranking call fed with a snapshot -/

/-- The accepted probe's call shape with an explicit auxiliary state. -/
def trackedWith? (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (mark : Nat) : Option Rule6TrackedRanking := do
  let roots ← frame? node
  let ligands := roots.map fun cursor => cursor.node.atom
  let referencePosition := ligands.idxOf mark
  if referencePosition >= ligands.length then none else
    rankOccurrencePositionsThroughRule6Tracked? (mol := cageRaw) state 16 roots ligands
      [0, 1, 2, 3] referencePosition

/-- The accepted probe call is the empty-state instance. -/
theorem trackedWith?_empty (node : RawMolecule.CanonicalBranchNode) (mark : Nat) :
    trackedWith? emptyOrdinaryAux node mark = tracked? node mark := rfl

/-- Frame atoms of a visit in the returned priority order under a snapshot and mark. -/
def rankedAtomsWith? (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (mark : Nat) : Option (List Nat) := do
  let atoms ← frameAtoms? node
  let ranking ← trackedWith? state node mark
  rankedAtomsOf? atoms ranking

theorem root0_frameAtoms : frameAtoms? root0 = some [1, 2, 3, 9] := by decide +kernel

/-- Geometric readback of a visit under a snapshot and mark on the family member `P`. -/
def readbackWith? (P : List CartesianPoint3) (len : P.length = 15) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) (mark : Nat) : Option RS := do
  let atoms ← rankedAtomsWith? state node mark
  let points ← atoms.mapM (pointOf? P len)
  descriptorOfPriorityOrderedPoints? points

/-! ### Cage A near outputs under the snapshot, pinned by kernel reduction

All twelve runs are strict with `pseudoComparisons = 0`: the order is decided by Rules 4/5 from the
temporary far facts, never by the Rule-6 marker. The case policy does not change the output. -/

theorem nearA_5R (u : Bool) : trackedWith? (tempStateA 5 RS.R u) nearA 5 =
    some { positions := [2, 3, 1, 0], unique := true, pseudoComparisons := 0 } := by
  cases u <;> decide +kernel

theorem nearA_5S (u : Bool) : trackedWith? (tempStateA 5 RS.S u) nearA 5 =
    some { positions := [3, 2, 1, 0], unique := true, pseudoComparisons := 0 } := by
  cases u <;> decide +kernel

theorem nearA_6R (u : Bool) : trackedWith? (tempStateA 6 RS.R u) nearA 6 =
    some { positions := [1, 3, 2, 0], unique := true, pseudoComparisons := 0 } := by
  cases u <;> decide +kernel

theorem nearA_6S (u : Bool) : trackedWith? (tempStateA 6 RS.S u) nearA 6 =
    some { positions := [3, 1, 2, 0], unique := true, pseudoComparisons := 0 } := by
  cases u <;> decide +kernel

theorem nearA_7R (u : Bool) : trackedWith? (tempStateA 7 RS.R u) nearA 7 =
    some { positions := [1, 2, 3, 0], unique := true, pseudoComparisons := 0 } := by
  cases u <;> decide +kernel

theorem nearA_7S (u : Bool) : trackedWith? (tempStateA 7 RS.S u) nearA 7 =
    some { positions := [2, 1, 3, 0], unique := true, pseudoComparisons := 0 } := by
  cases u <;> decide +kernel

theorem nearAtomsA_5R (u : Bool) : rankedAtomsWith? (tempStateA 5 RS.R u) nearA 5 =
    some [6, 7, 5, 0] := by
  unfold rankedAtomsWith?; rw [nearA_frameAtoms, nearA_5R]; rfl
theorem nearAtomsA_5S (u : Bool) : rankedAtomsWith? (tempStateA 5 RS.S u) nearA 5 =
    some [7, 6, 5, 0] := by
  unfold rankedAtomsWith?; rw [nearA_frameAtoms, nearA_5S]; rfl
theorem nearAtomsA_6R (u : Bool) : rankedAtomsWith? (tempStateA 6 RS.R u) nearA 6 =
    some [5, 7, 6, 0] := by
  unfold rankedAtomsWith?; rw [nearA_frameAtoms, nearA_6R]; rfl
theorem nearAtomsA_6S (u : Bool) : rankedAtomsWith? (tempStateA 6 RS.S u) nearA 6 =
    some [7, 5, 6, 0] := by
  unfold rankedAtomsWith?; rw [nearA_frameAtoms, nearA_6S]; rfl
theorem nearAtomsA_7R (u : Bool) : rankedAtomsWith? (tempStateA 7 RS.R u) nearA 7 =
    some [5, 6, 7, 0] := by
  unfold rankedAtomsWith?; rw [nearA_frameAtoms, nearA_7R]; rfl
theorem nearAtomsA_7S (u : Bool) : rankedAtomsWith? (tempStateA 7 RS.S u) nearA 7 =
    some [6, 5, 7, 0] := by
  unfold rankedAtomsWith?; rw [nearA_frameAtoms, nearA_7S]; rfl

section FamilyNear

variable (P : List CartesianPoint3) (len : P.length = 15)

theorem vol3_canonical :
    ligandVolumeWith P len k3 =
      orientedVolume (posWith P len 0) (posWith P len 5) (posWith P len 6) (posWith P len 7) := by
  simp only [ligandVolumeWith, lig3.1, lig3.2.1, lig3.2.2.1, lig3.2.2.2]

theorem vol_6750 :
    orientedVolume (posWith P len 6) (posWith P len 7) (posWith P len 5) (posWith P len 0) =
      - ligandVolumeWith P len k3 := by
  rw [vol3_canonical]; simp only [orientedVolume]; ring

theorem vol_7650 :
    orientedVolume (posWith P len 7) (posWith P len 6) (posWith P len 5) (posWith P len 0) =
      ligandVolumeWith P len k3 := by
  rw [vol3_canonical]; simp only [orientedVolume]; ring

theorem vol_5760 :
    orientedVolume (posWith P len 5) (posWith P len 7) (posWith P len 6) (posWith P len 0) =
      ligandVolumeWith P len k3 := by
  rw [vol3_canonical]; simp only [orientedVolume]; ring

theorem vol_7560 :
    orientedVolume (posWith P len 7) (posWith P len 5) (posWith P len 6) (posWith P len 0) =
      - ligandVolumeWith P len k3 := by
  rw [vol3_canonical]; simp only [orientedVolume]; ring

theorem vol_5670 :
    orientedVolume (posWith P len 5) (posWith P len 6) (posWith P len 7) (posWith P len 0) =
      - ligandVolumeWith P len k3 := by
  rw [vol3_canonical]; simp only [orientedVolume]; ring

theorem vol_6570 :
    orientedVolume (posWith P len 6) (posWith P len 5) (posWith P len 7) (posWith P len 0) =
      ligandVolumeWith P len k3 := by
  rw [vol3_canonical]; simp only [orientedVolume]; ring

/-- Near readback volumes under each snapshot: for marks 5 and 7, first letter `R` gives
`-vol3` and `S` gives `+vol3`; mark 6 reverses these signs. -/
theorem nearReadbackA_5R (u : Bool) : readbackWith? P len (tempStateA 5 RS.R u) nearA 5 =
    descriptorOfOrientedVolume? (- ligandVolumeWith P len k3) := by
  unfold readbackWith?
  rw [nearAtomsA_5R]
  show descriptorOfOrientedVolume? (orientedVolume (posWith P len 6) (posWith P len 7)
    (posWith P len 5) (posWith P len 0)) = _
  rw [vol_6750]

theorem nearReadbackA_5S (u : Bool) : readbackWith? P len (tempStateA 5 RS.S u) nearA 5 =
    descriptorOfOrientedVolume? (ligandVolumeWith P len k3) := by
  unfold readbackWith?
  rw [nearAtomsA_5S]
  show descriptorOfOrientedVolume? (orientedVolume (posWith P len 7) (posWith P len 6)
    (posWith P len 5) (posWith P len 0)) = _
  rw [vol_7650]

theorem nearReadbackA_6R (u : Bool) : readbackWith? P len (tempStateA 6 RS.R u) nearA 6 =
    descriptorOfOrientedVolume? (ligandVolumeWith P len k3) := by
  unfold readbackWith?
  rw [nearAtomsA_6R]
  show descriptorOfOrientedVolume? (orientedVolume (posWith P len 5) (posWith P len 7)
    (posWith P len 6) (posWith P len 0)) = _
  rw [vol_5760]

theorem nearReadbackA_6S (u : Bool) : readbackWith? P len (tempStateA 6 RS.S u) nearA 6 =
    descriptorOfOrientedVolume? (- ligandVolumeWith P len k3) := by
  unfold readbackWith?
  rw [nearAtomsA_6S]
  show descriptorOfOrientedVolume? (orientedVolume (posWith P len 7) (posWith P len 5)
    (posWith P len 6) (posWith P len 0)) = _
  rw [vol_7560]

theorem nearReadbackA_7R (u : Bool) : readbackWith? P len (tempStateA 7 RS.R u) nearA 7 =
    descriptorOfOrientedVolume? (- ligandVolumeWith P len k3) := by
  unfold readbackWith?
  rw [nearAtomsA_7R]
  show descriptorOfOrientedVolume? (orientedVolume (posWith P len 5) (posWith P len 6)
    (posWith P len 7) (posWith P len 0)) = _
  rw [vol_5670]

theorem nearReadbackA_7S (u : Bool) : readbackWith? P len (tempStateA 7 RS.S u) nearA 7 =
    descriptorOfOrientedVolume? (ligandVolumeWith P len k3) := by
  unfold readbackWith?
  rw [nearAtomsA_7S]
  show descriptorOfOrientedVolume? (orientedVolume (posWith P len 6) (posWith P len 5)
    (posWith P len 7) (posWith P len 0)) = _
  rw [vol_6570]

/-- The joint bridgehead bit of cage A as a letter: `R` iff `vol3 * vol8 < 0` (opposite bridgehead
volume signs, the out/out pattern), `S` iff they agree. -/
noncomputable abbrev jointLetterA : RS :=
  letterOfVolume (ligandVolumeWith P len k3 * ligandVolumeWith P len k8)

/-- **The mark-indexed near recalculation of cage A reads the joint bridgehead bit**, for every
nondegenerate table, every mark and both case policies. -/
theorem nearRecalcA (nondeg : Nondegenerate P len) (r : Nat) (hr : r ∈ [5, 6, 7]) (u : Bool) :
    readbackWith? P len (computedStateA P len r u) nearA r = some (jointLetterA P len) := by
  have n3 := nondeg k3
  have n8 := nondeg k8
  have cases : r = 5 ∨ r = 6 ∨ r = 7 := by simpa using hr
  have neg3 : - ligandVolumeWith P len k3 ≠ 0 := neg_ne_zero.mpr n3
  rcases lt_or_gt_of_ne n8 with h8 | h8
  · have far : farLetterA P len = RS.R := by simp [farLetterA, letterOfVolume, h8]
    have joint : jointLetterA P len = letterOfVolume (- ligandVolumeWith P len k3) :=
      letterOfVolume_mul_of_neg n3 h8
    rcases cases with rfl | rfl | rfl
    · simp only [computedStateA, far]
      rw [nearReadbackA_5R, descriptorOfOrientedVolume?_of_ne neg3, joint]
    · simp only [computedStateA, far, RS.swap]
      rw [nearReadbackA_6S, descriptorOfOrientedVolume?_of_ne neg3, joint]
    · simp only [computedStateA, far]
      rw [nearReadbackA_7R, descriptorOfOrientedVolume?_of_ne neg3, joint]
  · have far : farLetterA P len = RS.S := by
      simp [farLetterA, letterOfVolume, not_lt.mpr h8.le]
    have joint : jointLetterA P len = letterOfVolume (ligandVolumeWith P len k3) :=
      letterOfVolume_mul_of_pos n3 h8
    rcases cases with rfl | rfl | rfl
    · simp only [computedStateA, far]
      rw [nearReadbackA_5S, descriptorOfOrientedVolume?_of_ne n3, joint]
    · simp only [computedStateA, far, RS.swap]
      rw [nearReadbackA_6R, descriptorOfOrientedVolume?_of_ne n3, joint]
    · simp only [computedStateA, far]
      rw [nearReadbackA_7S, descriptorOfOrientedVolume?_of_ne n3, joint]

end FamilyNear

/-! ## Cage B: the same construction on the second arm -/

def nearB : RawMolecule.CanonicalBranchNode :=
  { atom := 9, parent := 0, history := [9, 0], provenance := .realAtom }

def farB (o : Nat) : RawMolecule.CanonicalBranchNode :=
  { atom := 14, parent := o, history := [14, o, 9, 0], provenance := .realAtom }

theorem nearB_frameAtoms : frameAtoms? nearB = some [0, 11, 12, 13] := by decide +kernel
theorem farB11_frameAtoms : frameAtoms? (farB 11) = some [11, 10, 12, 13] := by decide +kernel
theorem farB12_frameAtoms : frameAtoms? (farB 12) = some [12, 10, 11, 13] := by decide +kernel
theorem farB13_frameAtoms : frameAtoms? (farB 13) = some [13, 10, 11, 12] := by decide +kernel

theorem farB_o11_mark12 : tracked? (farB 11) 12 =
    some { positions := [0, 2, 3, 1], unique := true, pseudoComparisons := 1 } := by
  decide +kernel
theorem farB_o11_mark13 : tracked? (farB 11) 13 =
    some { positions := [0, 3, 2, 1], unique := true, pseudoComparisons := 1 } := by
  decide +kernel
theorem farB_o12_mark11 : tracked? (farB 12) 11 =
    some { positions := [0, 2, 3, 1], unique := true, pseudoComparisons := 1 } := by
  decide +kernel
theorem farB_o12_mark13 : tracked? (farB 12) 13 =
    some { positions := [0, 3, 2, 1], unique := true, pseudoComparisons := 1 } := by
  decide +kernel
theorem farB_o13_mark11 : tracked? (farB 13) 11 =
    some { positions := [0, 2, 3, 1], unique := true, pseudoComparisons := 1 } := by
  decide +kernel
theorem farB_o13_mark12 : tracked? (farB 13) 12 =
    some { positions := [0, 3, 2, 1], unique := true, pseudoComparisons := 1 } := by
  decide +kernel

/-- The empty-state near visit of cage B remains non-strict (counterevidence preserved). The
diagonal far visit of cage B was observed non-strict (`[0, 2, 3, 1]`, `unique = false`) in the
stage-2 run and is not pinned, to keep the kernel load within the build deadline. -/
theorem nearB_mark11_empty : tracked? nearB 11 =
    some { positions := [1, 2, 3, 0], unique := false, pseudoComparisons := 1 } := by
  decide +kernel

theorem farRankedAtomsB_1112 : visitRankedAtoms? (farB 11) 12 = some [11, 12, 13, 10] := by
  unfold visitRankedAtoms?; rw [farB11_frameAtoms, farB_o11_mark12]; rfl
theorem farRankedAtomsB_1113 : visitRankedAtoms? (farB 11) 13 = some [11, 13, 12, 10] := by
  unfold visitRankedAtoms?; rw [farB11_frameAtoms, farB_o11_mark13]; rfl
theorem farRankedAtomsB_1211 : visitRankedAtoms? (farB 12) 11 = some [12, 11, 13, 10] := by
  unfold visitRankedAtoms?; rw [farB12_frameAtoms, farB_o12_mark11]; rfl
theorem farRankedAtomsB_1213 : visitRankedAtoms? (farB 12) 13 = some [12, 13, 11, 10] := by
  unfold visitRankedAtoms?; rw [farB12_frameAtoms, farB_o12_mark13]; rfl
theorem farRankedAtomsB_1311 : visitRankedAtoms? (farB 13) 11 = some [13, 11, 12, 10] := by
  unfold visitRankedAtoms?; rw [farB13_frameAtoms, farB_o13_mark11]; rfl
theorem farRankedAtomsB_1312 : visitRankedAtoms? (farB 13) 12 = some [13, 12, 11, 10] := by
  unfold visitRankedAtoms?; rw [farB13_frameAtoms, farB_o13_mark12]; rfl

/-- The two off-diagonal oxygens of a cage-B mark, in increasing order. -/
def offDiagonalB : Nat → List Nat
  | 11 => [12, 13]
  | 12 => [11, 13]
  | 13 => [11, 12]
  | _ => []

def tempStateB (r : Nat) (first : RS) (uppercase : Bool) : OccurrenceAuxState :=
  match offDiagonalB r with
  | [o₁, o₂] => [tempFact (farB o₁) first uppercase, tempFact (farB o₂) first.swap uppercase]
  | _ => []

theorem tempStateB11_reads (first : RS) (uppercase : Bool) :
    (tempStateB 11 first uppercase).factAt? (farB 11) = none ∧
    (tempStateB 11 first uppercase).factAt? (farB 12) =
      some (tempFact (farB 12) first uppercase) ∧
    (tempStateB 11 first uppercase).factAt? (farB 13) =
      some (tempFact (farB 13) first.swap uppercase) := by
  cases first <;> cases uppercase <;> decide

theorem tempStateB12_reads (first : RS) (uppercase : Bool) :
    (tempStateB 12 first uppercase).factAt? (farB 12) = none ∧
    (tempStateB 12 first uppercase).factAt? (farB 11) =
      some (tempFact (farB 11) first uppercase) ∧
    (tempStateB 12 first uppercase).factAt? (farB 13) =
      some (tempFact (farB 13) first.swap uppercase) := by
  cases first <;> cases uppercase <;> decide

theorem tempStateB13_reads (first : RS) (uppercase : Bool) :
    (tempStateB 13 first uppercase).factAt? (farB 13) = none ∧
    (tempStateB 13 first uppercase).factAt? (farB 11) =
      some (tempFact (farB 11) first uppercase) ∧
    (tempStateB 13 first uppercase).factAt? (farB 12) =
      some (tempFact (farB 12) first.swap uppercase) := by
  cases first <;> cases uppercase <;> decide

section FamilyB

variable (P : List CartesianPoint3) (len : P.length = 15)

theorem vol14_canonical :
    ligandVolumeWith P len k14 = orientedVolume (posWith P len 10) (posWith P len 11)
      (posWith P len 12) (posWith P len 13) := by
  simp only [ligandVolumeWith, lig14.1, lig14.2.1, lig14.2.2.1, lig14.2.2.2]

theorem vol9_canonical :
    ligandVolumeWith P len k9 = orientedVolume (posWith P len 0) (posWith P len 11)
      (posWith P len 12) (posWith P len 13) := by
  simp only [ligandVolumeWith, lig9.1, lig9.2.1, lig9.2.2.1, lig9.2.2.2]

theorem volB_11_12_13_10 : orientedVolume (posWith P len 11) (posWith P len 12) (posWith P len 13)
    (posWith P len 10) = - ligandVolumeWith P len k14 := by
  rw [vol14_canonical]; simp only [orientedVolume]; ring
theorem volB_11_13_12_10 : orientedVolume (posWith P len 11) (posWith P len 13) (posWith P len 12)
    (posWith P len 10) = ligandVolumeWith P len k14 := by
  rw [vol14_canonical]; simp only [orientedVolume]; ring
theorem volB_12_11_13_10 : orientedVolume (posWith P len 12) (posWith P len 11) (posWith P len 13)
    (posWith P len 10) = ligandVolumeWith P len k14 := by
  rw [vol14_canonical]; simp only [orientedVolume]; ring
theorem volB_12_13_11_10 : orientedVolume (posWith P len 12) (posWith P len 13) (posWith P len 11)
    (posWith P len 10) = - ligandVolumeWith P len k14 := by
  rw [vol14_canonical]; simp only [orientedVolume]; ring
theorem volB_13_11_12_10 : orientedVolume (posWith P len 13) (posWith P len 11) (posWith P len 12)
    (posWith P len 10) = - ligandVolumeWith P len k14 := by
  rw [vol14_canonical]; simp only [orientedVolume]; ring
theorem volB_13_12_11_10 : orientedVolume (posWith P len 13) (posWith P len 12) (posWith P len 11)
    (posWith P len 10) = ligandVolumeWith P len k14 := by
  rw [vol14_canonical]; simp only [orientedVolume]; ring

noncomputable abbrev farLetterB : RS := letterOfVolume (ligandVolumeWith P len k14)

theorem farReadbackB_letters (nondeg : Nondegenerate P len) :
    visitReadback? P len (farB 12) 11 = some (farLetterB P len) ∧
    visitReadback? P len (farB 13) 11 = some (farLetterB P len).swap ∧
    visitReadback? P len (farB 11) 12 = some (farLetterB P len).swap ∧
    visitReadback? P len (farB 13) 12 = some (farLetterB P len) ∧
    visitReadback? P len (farB 11) 13 = some (farLetterB P len) ∧
    visitReadback? P len (farB 12) 13 = some (farLetterB P len).swap := by
  have nonzero := nondeg k14
  have negNonzero : - ligandVolumeWith P len k14 ≠ 0 := neg_ne_zero.mpr nonzero
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold visitReadback?
    rw [farRankedAtomsB_1211]
    show descriptorOfOrientedVolume? (orientedVolume (posWith P len 12) (posWith P len 11)
      (posWith P len 13) (posWith P len 10)) = _
    rw [volB_12_11_13_10, descriptorOfOrientedVolume?_of_ne nonzero]
  · unfold visitReadback?
    rw [farRankedAtomsB_1311]
    show descriptorOfOrientedVolume? (orientedVolume (posWith P len 13) (posWith P len 11)
      (posWith P len 12) (posWith P len 10)) = _
    rw [volB_13_11_12_10, descriptorOfOrientedVolume?_of_ne negNonzero, letterOfVolume_neg nonzero]
  · unfold visitReadback?
    rw [farRankedAtomsB_1112]
    show descriptorOfOrientedVolume? (orientedVolume (posWith P len 11) (posWith P len 12)
      (posWith P len 13) (posWith P len 10)) = _
    rw [volB_11_12_13_10, descriptorOfOrientedVolume?_of_ne negNonzero, letterOfVolume_neg nonzero]
  · unfold visitReadback?
    rw [farRankedAtomsB_1312]
    show descriptorOfOrientedVolume? (orientedVolume (posWith P len 13) (posWith P len 12)
      (posWith P len 11) (posWith P len 10)) = _
    rw [volB_13_12_11_10, descriptorOfOrientedVolume?_of_ne nonzero]
  · unfold visitReadback?
    rw [farRankedAtomsB_1113]
    show descriptorOfOrientedVolume? (orientedVolume (posWith P len 11) (posWith P len 13)
      (posWith P len 12) (posWith P len 10)) = _
    rw [volB_11_13_12_10, descriptorOfOrientedVolume?_of_ne nonzero]
  · unfold visitReadback?
    rw [farRankedAtomsB_1213]
    show descriptorOfOrientedVolume? (orientedVolume (posWith P len 12) (posWith P len 13)
      (posWith P len 11) (posWith P len 10)) = _
    rw [volB_12_13_11_10, descriptorOfOrientedVolume?_of_ne negNonzero, letterOfVolume_neg nonzero]

noncomputable def computedStateB (r : Nat) (uppercase : Bool) : OccurrenceAuxState :=
  match r with
  | 11 => tempStateB 11 (farLetterB P len) uppercase
  | 12 => tempStateB 12 (farLetterB P len).swap uppercase
  | 13 => tempStateB 13 (farLetterB P len) uppercase
  | _ => []

end FamilyB

/-! ### Cage B near outputs under the snapshot, pinned by kernel reduction

Mirror of cage A: all strict, `pseudoComparisons = 0`, policy independent. -/

theorem nearB_11R (u : Bool) : trackedWith? (tempStateB 11 RS.R u) nearB 11 =
    some { positions := [2, 3, 1, 0], unique := true, pseudoComparisons := 0 } := by
  cases u <;> decide +kernel
theorem nearB_11S (u : Bool) : trackedWith? (tempStateB 11 RS.S u) nearB 11 =
    some { positions := [3, 2, 1, 0], unique := true, pseudoComparisons := 0 } := by
  cases u <;> decide +kernel
theorem nearB_12R (u : Bool) : trackedWith? (tempStateB 12 RS.R u) nearB 12 =
    some { positions := [1, 3, 2, 0], unique := true, pseudoComparisons := 0 } := by
  cases u <;> decide +kernel
theorem nearB_12S (u : Bool) : trackedWith? (tempStateB 12 RS.S u) nearB 12 =
    some { positions := [3, 1, 2, 0], unique := true, pseudoComparisons := 0 } := by
  cases u <;> decide +kernel
theorem nearB_13R (u : Bool) : trackedWith? (tempStateB 13 RS.R u) nearB 13 =
    some { positions := [1, 2, 3, 0], unique := true, pseudoComparisons := 0 } := by
  cases u <;> decide +kernel
theorem nearB_13S (u : Bool) : trackedWith? (tempStateB 13 RS.S u) nearB 13 =
    some { positions := [2, 1, 3, 0], unique := true, pseudoComparisons := 0 } := by
  cases u <;> decide +kernel

theorem nearAtomsB_11R (u : Bool) : rankedAtomsWith? (tempStateB 11 RS.R u) nearB 11 =
    some [12, 13, 11, 0] := by
  unfold rankedAtomsWith?; rw [nearB_frameAtoms, nearB_11R]; rfl
theorem nearAtomsB_11S (u : Bool) : rankedAtomsWith? (tempStateB 11 RS.S u) nearB 11 =
    some [13, 12, 11, 0] := by
  unfold rankedAtomsWith?; rw [nearB_frameAtoms, nearB_11S]; rfl
theorem nearAtomsB_12R (u : Bool) : rankedAtomsWith? (tempStateB 12 RS.R u) nearB 12 =
    some [11, 13, 12, 0] := by
  unfold rankedAtomsWith?; rw [nearB_frameAtoms, nearB_12R]; rfl
theorem nearAtomsB_12S (u : Bool) : rankedAtomsWith? (tempStateB 12 RS.S u) nearB 12 =
    some [13, 11, 12, 0] := by
  unfold rankedAtomsWith?; rw [nearB_frameAtoms, nearB_12S]; rfl
theorem nearAtomsB_13R (u : Bool) : rankedAtomsWith? (tempStateB 13 RS.R u) nearB 13 =
    some [11, 12, 13, 0] := by
  unfold rankedAtomsWith?; rw [nearB_frameAtoms, nearB_13R]; rfl
theorem nearAtomsB_13S (u : Bool) : rankedAtomsWith? (tempStateB 13 RS.S u) nearB 13 =
    some [12, 11, 13, 0] := by
  unfold rankedAtomsWith?; rw [nearB_frameAtoms, nearB_13S]; rfl

section FamilyNearB

variable (P : List CartesianPoint3) (len : P.length = 15)

theorem volB_12_13_11_0 : orientedVolume (posWith P len 12) (posWith P len 13) (posWith P len 11)
    (posWith P len 0) = - ligandVolumeWith P len k9 := by
  rw [vol9_canonical]; simp only [orientedVolume]; ring
theorem volB_13_12_11_0 : orientedVolume (posWith P len 13) (posWith P len 12) (posWith P len 11)
    (posWith P len 0) = ligandVolumeWith P len k9 := by
  rw [vol9_canonical]; simp only [orientedVolume]; ring
theorem volB_11_13_12_0 : orientedVolume (posWith P len 11) (posWith P len 13) (posWith P len 12)
    (posWith P len 0) = ligandVolumeWith P len k9 := by
  rw [vol9_canonical]; simp only [orientedVolume]; ring
theorem volB_13_11_12_0 : orientedVolume (posWith P len 13) (posWith P len 11) (posWith P len 12)
    (posWith P len 0) = - ligandVolumeWith P len k9 := by
  rw [vol9_canonical]; simp only [orientedVolume]; ring
theorem volB_11_12_13_0 : orientedVolume (posWith P len 11) (posWith P len 12) (posWith P len 13)
    (posWith P len 0) = - ligandVolumeWith P len k9 := by
  rw [vol9_canonical]; simp only [orientedVolume]; ring
theorem volB_12_11_13_0 : orientedVolume (posWith P len 12) (posWith P len 11) (posWith P len 13)
    (posWith P len 0) = ligandVolumeWith P len k9 := by
  rw [vol9_canonical]; simp only [orientedVolume]; ring

theorem nearReadbackB_11R (u : Bool) : readbackWith? P len (tempStateB 11 RS.R u) nearB 11 =
    descriptorOfOrientedVolume? (- ligandVolumeWith P len k9) := by
  unfold readbackWith?
  rw [nearAtomsB_11R]
  show descriptorOfOrientedVolume? (orientedVolume (posWith P len 12) (posWith P len 13)
    (posWith P len 11) (posWith P len 0)) = _
  rw [volB_12_13_11_0]
theorem nearReadbackB_11S (u : Bool) : readbackWith? P len (tempStateB 11 RS.S u) nearB 11 =
    descriptorOfOrientedVolume? (ligandVolumeWith P len k9) := by
  unfold readbackWith?
  rw [nearAtomsB_11S]
  show descriptorOfOrientedVolume? (orientedVolume (posWith P len 13) (posWith P len 12)
    (posWith P len 11) (posWith P len 0)) = _
  rw [volB_13_12_11_0]
theorem nearReadbackB_12R (u : Bool) : readbackWith? P len (tempStateB 12 RS.R u) nearB 12 =
    descriptorOfOrientedVolume? (ligandVolumeWith P len k9) := by
  unfold readbackWith?
  rw [nearAtomsB_12R]
  show descriptorOfOrientedVolume? (orientedVolume (posWith P len 11) (posWith P len 13)
    (posWith P len 12) (posWith P len 0)) = _
  rw [volB_11_13_12_0]
theorem nearReadbackB_12S (u : Bool) : readbackWith? P len (tempStateB 12 RS.S u) nearB 12 =
    descriptorOfOrientedVolume? (- ligandVolumeWith P len k9) := by
  unfold readbackWith?
  rw [nearAtomsB_12S]
  show descriptorOfOrientedVolume? (orientedVolume (posWith P len 13) (posWith P len 11)
    (posWith P len 12) (posWith P len 0)) = _
  rw [volB_13_11_12_0]
theorem nearReadbackB_13R (u : Bool) : readbackWith? P len (tempStateB 13 RS.R u) nearB 13 =
    descriptorOfOrientedVolume? (- ligandVolumeWith P len k9) := by
  unfold readbackWith?
  rw [nearAtomsB_13R]
  show descriptorOfOrientedVolume? (orientedVolume (posWith P len 11) (posWith P len 12)
    (posWith P len 13) (posWith P len 0)) = _
  rw [volB_11_12_13_0]
theorem nearReadbackB_13S (u : Bool) : readbackWith? P len (tempStateB 13 RS.S u) nearB 13 =
    descriptorOfOrientedVolume? (ligandVolumeWith P len k9) := by
  unfold readbackWith?
  rw [nearAtomsB_13S]
  show descriptorOfOrientedVolume? (orientedVolume (posWith P len 12) (posWith P len 11)
    (posWith P len 13) (posWith P len 0)) = _
  rw [volB_12_11_13_0]

/-- The joint bridgehead bit of cage B as a letter. -/
noncomputable abbrev jointLetterB : RS :=
  letterOfVolume (ligandVolumeWith P len k9 * ligandVolumeWith P len k14)

/-- **The mark-indexed near recalculation of cage B reads its joint bridgehead bit.** -/
theorem nearRecalcB (nondeg : Nondegenerate P len) (r : Nat) (hr : r ∈ [11, 12, 13]) (u : Bool) :
    readbackWith? P len (computedStateB P len r u) nearB r = some (jointLetterB P len) := by
  have n9 := nondeg k9
  have n14 := nondeg k14
  have cases : r = 11 ∨ r = 12 ∨ r = 13 := by simpa using hr
  have neg9 : - ligandVolumeWith P len k9 ≠ 0 := neg_ne_zero.mpr n9
  rcases lt_or_gt_of_ne n14 with h14 | h14
  · have far : farLetterB P len = RS.R := by simp [farLetterB, letterOfVolume, h14]
    have joint : jointLetterB P len = letterOfVolume (- ligandVolumeWith P len k9) :=
      letterOfVolume_mul_of_neg n9 h14
    rcases cases with rfl | rfl | rfl
    · simp only [computedStateB, far]
      rw [nearReadbackB_11R, descriptorOfOrientedVolume?_of_ne neg9, joint]
    · simp only [computedStateB, far, RS.swap]
      rw [nearReadbackB_12S, descriptorOfOrientedVolume?_of_ne neg9, joint]
    · simp only [computedStateB, far]
      rw [nearReadbackB_13R, descriptorOfOrientedVolume?_of_ne neg9, joint]
  · have far : farLetterB P len = RS.S := by
      simp [farLetterB, letterOfVolume, not_lt.mpr h14.le]
    have joint : jointLetterB P len = letterOfVolume (ligandVolumeWith P len k9) :=
      letterOfVolume_mul_of_pos n9 h14
    rcases cases with rfl | rfl | rfl
    · simp only [computedStateB, far]
      rw [nearReadbackB_11S, descriptorOfOrientedVolume?_of_ne n9, joint]
    · simp only [computedStateB, far, RS.swap]
      rw [nearReadbackB_12R, descriptorOfOrientedVolume?_of_ne n9, joint]
    · simp only [computedStateB, far]
      rw [nearReadbackB_13S, descriptorOfOrientedVolume?_of_ne n9, joint]

/-! ## The connection to the joint sign product and the formal physical classification -/

/-- **The two near recalculated letters agree iff the arms admit a (proper or mirror) branch
transport**, i.e. iff the bridgehead sign products agree (`arms_transport_iff`), for every
nondegenerate table, every pair of marks and both case policies. -/
theorem nearRecalc_agree_iff_transport (nondeg : Nondegenerate P len)
    (rA : Nat) (hA : rA ∈ [5, 6, 7]) (rB : Nat) (hB : rB ∈ [11, 12, 13]) (uA uB : Bool)
    (mirror : Bool) :
    readbackWith? P len (computedStateA P len rA uA) nearA rA =
        readbackWith? P len (computedStateB P len rB uB) nearB rB ↔
      BranchTransport cageCanon (cfgWith P len) k0 2 3 mirror := by
  rw [nearRecalcA P len nondeg rA hA uA, nearRecalcB P len nondeg rB hB uB,
    arms_transport_iff (cfgWith P len) mirror, signProducts_eq_iff_volumes P len nondeg]
  simp only [Option.some.injEq, jointLetterA, jointLetterB, letterOfVolume_eq_iff]

/-- **The two near recalculated letters differ iff the root is pairwise properly
distinguishable** in the formal calibrated domain (`family_root_classification`). -/
theorem nearRecalc_ne_iff_pairwise (nondeg : Nondegenerate P len)
    (rA : Nat) (hA : rA ∈ [5, 6, 7]) (rB : Nat) (hB : rB ∈ [11, 12, 13]) (uA uB : Bool) :
    readbackWith? P len (computedStateA P len rA uA) nearA rA ≠
        readbackWith? P len (computedStateB P len rB uB) nearB rB ↔
      MultiCenterMolecule.PairwiseProperDistinguishable
        (certifiedWith P len).detectedMultiCenterMolecule (detectedCfgWith P len)
        (rootWith P len) := by
  rw [Ne, nearRecalc_agree_iff_transport P len nondeg rA hA rB hB uA uB false,
    detectedPairwiseWith_iff, root_pairwise_iff]
  exact not_congr (arms_transport_iff (cfgWith P len) false)

end FamilyNearB

/-! ## The root fed with both near letters: mark-independent order iff the letters differ -/

/-- Temporary near facts at the exact keys `[3, 0]` and `[9, 0]` of the two arms. -/
def rootTemp (letterA letterB : RS) (uppercase : Bool) : OccurrenceAuxState :=
  [tempFact nearA letterA uppercase, tempFact nearB letterB uppercase]

theorem rootTemp_reads (letterA letterB : RS) (uppercase : Bool) :
    (rootTemp letterA letterB uppercase).factAt? nearA =
        some (tempFact nearA letterA uppercase) ∧
      (rootTemp letterA letterB uppercase).factAt? nearB =
        some (tempFact nearB letterB uppercase) ∧
      (rootTemp letterA letterB uppercase).factAt? root0 = none := by
  cases letterA <;> cases letterB <;> cases uppercase <;> decide

/-! Differing letters: both arm marks give the same strict order with no marker decision. -/

theorem root_RS_3 (u : Bool) : trackedWith? (rootTemp RS.R RS.S u) root0 3 =
    some { positions := [1, 2, 3, 0], unique := true, pseudoComparisons := 0 } := by
  cases u <;> decide +kernel
theorem root_RS_9 (u : Bool) : trackedWith? (rootTemp RS.R RS.S u) root0 9 =
    some { positions := [1, 2, 3, 0], unique := true, pseudoComparisons := 0 } := by
  cases u <;> decide +kernel
theorem root_SR_3 (u : Bool) : trackedWith? (rootTemp RS.S RS.R u) root0 3 =
    some { positions := [1, 3, 2, 0], unique := true, pseudoComparisons := 0 } := by
  cases u <;> decide +kernel
theorem root_SR_9 (u : Bool) : trackedWith? (rootTemp RS.S RS.R u) root0 9 =
    some { positions := [1, 3, 2, 0], unique := true, pseudoComparisons := 0 } := by
  cases u <;> decide +kernel

/-! Equal letters: the Rule-6 marker decides (`pseudoComparisons = 1`) and the two arm marks give
opposite orders, so an all-reference consensus must refuse. -/

theorem root_RR_3 (u : Bool) : trackedWith? (rootTemp RS.R RS.R u) root0 3 =
    some { positions := [1, 2, 3, 0], unique := true, pseudoComparisons := 1 } := by
  cases u <;> decide +kernel
theorem root_RR_9 (u : Bool) : trackedWith? (rootTemp RS.R RS.R u) root0 9 =
    some { positions := [1, 3, 2, 0], unique := true, pseudoComparisons := 1 } := by
  cases u <;> decide +kernel
theorem root_SS_3 (u : Bool) : trackedWith? (rootTemp RS.S RS.S u) root0 3 =
    some { positions := [1, 2, 3, 0], unique := true, pseudoComparisons := 1 } := by
  cases u <;> decide +kernel
theorem root_SS_9 (u : Bool) : trackedWith? (rootTemp RS.S RS.S u) root0 9 =
    some { positions := [1, 3, 2, 0], unique := true, pseudoComparisons := 1 } := by
  cases u <;> decide +kernel

theorem rootAtoms_RS_3 (u : Bool) : rankedAtomsWith? (rootTemp RS.R RS.S u) root0 3 =
    some [2, 3, 9, 1] := by unfold rankedAtomsWith?; rw [root0_frameAtoms, root_RS_3]; rfl
theorem rootAtoms_RS_9 (u : Bool) : rankedAtomsWith? (rootTemp RS.R RS.S u) root0 9 =
    some [2, 3, 9, 1] := by unfold rankedAtomsWith?; rw [root0_frameAtoms, root_RS_9]; rfl
theorem rootAtoms_SR_3 (u : Bool) : rankedAtomsWith? (rootTemp RS.S RS.R u) root0 3 =
    some [2, 9, 3, 1] := by unfold rankedAtomsWith?; rw [root0_frameAtoms, root_SR_3]; rfl
theorem rootAtoms_SR_9 (u : Bool) : rankedAtomsWith? (rootTemp RS.S RS.R u) root0 9 =
    some [2, 9, 3, 1] := by unfold rankedAtomsWith?; rw [root0_frameAtoms, root_SR_9]; rfl
theorem rootAtoms_RR_3 (u : Bool) : rankedAtomsWith? (rootTemp RS.R RS.R u) root0 3 =
    some [2, 3, 9, 1] := by unfold rankedAtomsWith?; rw [root0_frameAtoms, root_RR_3]; rfl
theorem rootAtoms_RR_9 (u : Bool) : rankedAtomsWith? (rootTemp RS.R RS.R u) root0 9 =
    some [2, 9, 3, 1] := by unfold rankedAtomsWith?; rw [root0_frameAtoms, root_RR_9]; rfl
theorem rootAtoms_SS_3 (u : Bool) : rankedAtomsWith? (rootTemp RS.S RS.S u) root0 3 =
    some [2, 3, 9, 1] := by unfold rankedAtomsWith?; rw [root0_frameAtoms, root_SS_3]; rfl
theorem rootAtoms_SS_9 (u : Bool) : rankedAtomsWith? (rootTemp RS.S RS.S u) root0 9 =
    some [2, 9, 3, 1] := by unfold rankedAtomsWith?; rw [root0_frameAtoms, root_SS_9]; rfl

section FamilyRoot

variable (P : List CartesianPoint3) (len : P.length = 15)

theorem vol0_canonical :
    ligandVolumeWith P len k0 =
      orientedVolume (posWith P len 1) (posWith P len 2) (posWith P len 3) (posWith P len 9) := by
  simp only [ligandVolumeWith, lig0.1, lig0.2.1, lig0.2.2.1, lig0.2.2.2]

theorem vol_2391 : orientedVolume (posWith P len 2) (posWith P len 3) (posWith P len 9)
    (posWith P len 1) = - ligandVolumeWith P len k0 := by
  rw [vol0_canonical]; simp only [orientedVolume]; ring

theorem vol_2931 : orientedVolume (posWith P len 2) (posWith P len 9) (posWith P len 3)
    (posWith P len 1) = ligandVolumeWith P len k0 := by
  rw [vol0_canonical]; simp only [orientedVolume]; ring

/-- Root readbacks. With `R` on arm A both marks read `-vol0`; with `R` on arm B both read `vol0`;
with equal letters the two marks read opposite volumes. -/
theorem rootReadback_RS (u : Bool) (mark : Nat) (hm : mark ∈ [3, 9]) :
    readbackWith? P len (rootTemp RS.R RS.S u) root0 mark =
      descriptorOfOrientedVolume? (- ligandVolumeWith P len k0) := by
  have cases : mark = 3 ∨ mark = 9 := by simpa using hm
  rcases cases with rfl | rfl
  · unfold readbackWith?
    rw [rootAtoms_RS_3]
    show descriptorOfOrientedVolume? (orientedVolume (posWith P len 2) (posWith P len 3)
      (posWith P len 9) (posWith P len 1)) = _
    rw [vol_2391]
  · unfold readbackWith?
    rw [rootAtoms_RS_9]
    show descriptorOfOrientedVolume? (orientedVolume (posWith P len 2) (posWith P len 3)
      (posWith P len 9) (posWith P len 1)) = _
    rw [vol_2391]

theorem rootReadback_SR (u : Bool) (mark : Nat) (hm : mark ∈ [3, 9]) :
    readbackWith? P len (rootTemp RS.S RS.R u) root0 mark =
      descriptorOfOrientedVolume? (ligandVolumeWith P len k0) := by
  have cases : mark = 3 ∨ mark = 9 := by simpa using hm
  rcases cases with rfl | rfl
  · unfold readbackWith?
    rw [rootAtoms_SR_3]
    show descriptorOfOrientedVolume? (orientedVolume (posWith P len 2) (posWith P len 9)
      (posWith P len 3) (posWith P len 1)) = _
    rw [vol_2931]
  · unfold readbackWith?
    rw [rootAtoms_SR_9]
    show descriptorOfOrientedVolume? (orientedVolume (posWith P len 2) (posWith P len 9)
      (posWith P len 3) (posWith P len 1)) = _
    rw [vol_2931]

theorem rootReadback_equal (letter : RS) (u : Bool) :
    readbackWith? P len (rootTemp letter letter u) root0 3 =
        descriptorOfOrientedVolume? (- ligandVolumeWith P len k0) ∧
      readbackWith? P len (rootTemp letter letter u) root0 9 =
        descriptorOfOrientedVolume? (ligandVolumeWith P len k0) := by
  cases letter
  · constructor
    · unfold readbackWith?
      rw [rootAtoms_RR_3]
      show descriptorOfOrientedVolume? (orientedVolume (posWith P len 2) (posWith P len 3)
        (posWith P len 9) (posWith P len 1)) = _
      rw [vol_2391]
    · unfold readbackWith?
      rw [rootAtoms_RR_9]
      show descriptorOfOrientedVolume? (orientedVolume (posWith P len 2) (posWith P len 9)
        (posWith P len 3) (posWith P len 1)) = _
      rw [vol_2931]
  · constructor
    · unfold readbackWith?
      rw [rootAtoms_SS_3]
      show descriptorOfOrientedVolume? (orientedVolume (posWith P len 2) (posWith P len 3)
        (posWith P len 9) (posWith P len 1)) = _
      rw [vol_2391]
    · unfold readbackWith?
      rw [rootAtoms_SS_9]
      show descriptorOfOrientedVolume? (orientedVolume (posWith P len 2) (posWith P len 9)
        (posWith P len 3) (posWith P len 1)) = _
      rw [vol_2931]

/-- **Two-mark root consensus of the recalculated near letters**: the common readback of the two
arm marks, refused when they disagree. This is an experimental composition using the existing
tracked call under both arm references; it is not the production `rule6Result?` constructor. -/
noncomputable def rootConsensus? (u : Bool) : Option RS :=
  match readbackWith? P len (rootTemp (jointLetterA P len) (jointLetterB P len) u) root0 3,
      readbackWith? P len (rootTemp (jointLetterA P len) (jointLetterB P len) u) root0 9 with
  | some a, some b => if a = b then some a else none
  | _, _ => none

theorem swap_ne_self (letter : RS) : letter.swap ≠ letter := by cases letter <;> decide

/-- With differing near letters the consensus exists and is the root's geometric reading with the
`R`-bit arm first; with equal near letters the two marks disagree and the consensus refuses. -/
theorem rootConsensus_cases (nondeg : Nondegenerate P len) (u : Bool) :
    (jointLetterA P len ≠ jointLetterB P len →
      rootConsensus? P len u = some (letterOfVolume
        (if jointLetterA P len = RS.R then - ligandVolumeWith P len k0
          else ligandVolumeWith P len k0))) ∧
    (jointLetterA P len = jointLetterB P len → rootConsensus? P len u = none) := by
  have n0 := nondeg k0
  have neg0 : - ligandVolumeWith P len k0 ≠ 0 := neg_ne_zero.mpr n0
  have opposite := letterOfVolume_neg n0
  constructor
  · intro distinct
    unfold rootConsensus?
    rcases hA : jointLetterA P len with _ | _ <;> rcases hB : jointLetterB P len with _ | _
    · exact absurd rfl (hA ▸ hB ▸ distinct)
    · rw [rootReadback_RS P len u 3 (by decide), rootReadback_RS P len u 9 (by decide),
        descriptorOfOrientedVolume?_of_ne neg0]
      simp
    · rw [rootReadback_SR P len u 3 (by decide), rootReadback_SR P len u 9 (by decide),
        descriptorOfOrientedVolume?_of_ne n0]
      simp
    · exact absurd rfl (hA ▸ hB ▸ distinct)
  · intro equal
    unfold rootConsensus?
    rw [← equal, (rootReadback_equal P len (jointLetterA P len) u).1,
      (rootReadback_equal P len (jointLetterA P len) u).2,
      descriptorOfOrientedVolume?_of_ne neg0, descriptorOfOrientedVolume?_of_ne n0, opposite]
    simp [swap_ne_self]

/-- **The recalculated root consensus exists iff the root is pairwise properly distinguishable**
in the formal calibrated domain, for every nondegenerate table and both case policies. -/
theorem rootConsensus_isSome_iff_pairwise (nondeg : Nondegenerate P len) (u : Bool) :
    (rootConsensus? P len u).isSome = true ↔
      MultiCenterMolecule.PairwiseProperDistinguishable
        (certifiedWith P len).detectedMultiCenterMolecule (detectedCfgWith P len)
        (rootWith P len) := by
  have pairwise : MultiCenterMolecule.PairwiseProperDistinguishable
      (certifiedWith P len).detectedMultiCenterMolecule (detectedCfgWith P len)
      (rootWith P len) ↔ jointLetterA P len ≠ jointLetterB P len := by
    rw [detectedPairwiseWith_iff, root_pairwise_iff]
    simp only [jointLetterA, jointLetterB, letterOfVolume_eq_iff, Ne,
      signProducts_eq_iff_volumes P len nondeg]
  rw [pairwise]
  constructor
  · intro isSome equal
    rw [(rootConsensus_cases P len nondeg u).2 equal] at isSome
    cases isSome
  · intro distinct
    rw [(rootConsensus_cases P len nondeg u).1 distinct]
    rfl

end FamilyRoot

#print axioms trackedWith?
#print axioms readbackWith?

end TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback

assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback.pointOf?_spatial
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback.rankingReadback?_sound
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback.far_o5_mark7
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback.far_o7_mark6
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback.farRankedAtoms_56
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback.visitReadback?_eq_generic
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback.vol_5674
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback.farReadbackA_letters
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback.tempStateA5_reads
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback.tempStateA6_reads
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback.tempStateA7_reads
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback.tempStateA_near_root_none
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback.nearA_5R
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback.nearA_7S
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback.nearAtomsA_5R
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback.nearReadbackA_5R
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback.nearRecalcA
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback.farB_o11_mark12
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback.nearB_mark11_empty
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback.farReadbackB_letters
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback.tempStateB11_reads
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback.nearB_11R
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback.nearAtomsB_13S
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback.nearRecalcB
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback.nearRecalc_agree_iff_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback.nearRecalc_ne_iff_pairwise
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback.rootTemp_reads
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback.root_RS_3
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback.root_RR_9
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback.rootAtoms_SR_9
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback.rootReadback_RS
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback.rootReadback_equal
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback.rootConsensus_cases
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback.rootConsensus_isSome_iff_pairwise
