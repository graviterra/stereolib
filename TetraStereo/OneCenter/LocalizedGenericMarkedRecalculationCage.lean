import TetraStereo.OneCenter.LocalizedGenericMarkedRecalculation
import TetraStereo.OneCenter.LocalizedHiddenParityMirrorDerivedPipeline
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 0

/-!
# The generic marked recalculation instantiated on the accepted cage

The generic constructor is applied to the accepted cage adapter `cageRaw`, its atom count as
comparator fuel, and the certified coordinates of the physical family. No mark, visit, schedule,
letter or case is supplied: the eligible references `{3,9}`, `{5,6,7}`, `{11,12,13}` and the far
tied pairs are generated from actual ordinary comparisons, the schedule descends the actual
canonical expansion, and every temporary fact is mirror-recomputed.

Main result: `assignCenter_eq_assign` — the generic center-0 result equals the accepted
mirror-derived pipeline `assign? P len rA rB` for every nondegenerate family geometry and every
accepted mark pair; hence it exists iff the root is pairwise properly distinguishable
(`assignCenter_isSome_iff_pairwise`). The cost is kept to a few kernel pins of single-occurrence
calls; all composed values are derived by rewriting with the accepted equalities.
-/

namespace TetraStereo.OneCenter.LocalizedGenericMarkedRecalculationCage

open TetraStereo.OneCenter
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCompletion
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation
open TetraStereo.OneCenter.LocalizedHiddenParityMarkedProbe
open TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback
open TetraStereo.OneCenter.LocalizedHiddenParityPromotedPipeline
open TetraStereo.OneCenter.LocalizedHiddenParityPromotedReflection
open TetraStereo.OneCenter.LocalizedHiddenParityMirrorDerivedPipeline
open TetraStereo.OneCenter.LocalizedGenericMarkedRecalculation hiding frameAtoms? rankedAtoms?

/-! ## Geometry of the family and the generic projections on the cage adapter -/

/-- Certified coordinate of a runtime atom identifier, as the generic geometry. -/
def geomOf (P : List CartesianPoint3) (len : P.length = 15) : Geometry := pointOf? P len

theorem geomOf_mirror (P : List CartesianPoint3) (len : P.length = 15) :
    mirror (geomOf P len) = geomOf (mirrorPoints P) (mirrorLength P len) := by
  funext atom
  show (pointOf? P len atom).map CartesianPoint3.reflectX = _
  exact (pointOf_mirror P len atom).symm

theorem gFrame_eq (node : RawMolecule.CanonicalBranchNode) :
    LocalizedGenericMarkedRecalculation.frameAtoms? cageRaw node = frameAtoms? node := rfl

theorem marked_eq_tracked (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (mark : Nat) : marked? cageRaw 16 state node mark = trackedWith? state node mark := rfl

theorem gRanked_eq (atoms : List Nat) (ranking : Rule6TrackedRanking) :
    LocalizedGenericMarkedRecalculation.rankedAtoms? atoms ranking =
      rankedAtomsOf? atoms ranking := rfl

/-- The generic marked readback on the family geometry is the accepted readback call. -/
theorem markedReadback_eq (P : List CartesianPoint3) (len : P.length = 15)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode) (mark : Nat) :
    markedReadback? cageRaw 16 (geomOf P len) state node mark =
      readbackWith? P len state node mark := by
  unfold markedReadback? readbackWith? rankedAtomsWith?
  rw [gFrame_eq, marked_eq_tracked]
  cases frameAtoms? node with
  | none => rfl
  | some atoms =>
      cases trackedWith? state node mark with
      | none => rfl
      | some ranking => rfl

theorem markedReadback_empty (P : List CartesianPoint3) (len : P.length = 15)
    (node : RawMolecule.CanonicalBranchNode) (mark : Nat) :
    markedReadback? cageRaw 16 (geomOf P len) [] node mark = visitReadback? P len node mark := by
  rw [markedReadback_eq]
  rfl

/-! ## Occurrences of the two arms below the near centers -/

def oxA (o : Nat) : RawMolecule.CanonicalBranchNode :=
  { atom := o, parent := 3, history := [o, 3, 0], provenance := .realAtom }

def oxB (o : Nat) : RawMolecule.CanonicalBranchNode :=
  { atom := o, parent := 9, history := [o, 9, 0], provenance := .realAtom }

/-! ## Kernel pins of single-occurrence runtime calls -/

theorem root_ordinary : ordinary? cageRaw 16 [] root0 =
    some ([1, 2, 3, 0], [some .gt, some .eq, some .gt]) := by decide +kernel

theorem nearA_ordinary : ordinary? cageRaw 16 [] nearA =
    some ([1, 2, 3, 0], [some .eq, some .eq, some .gt]) := by decide +kernel

theorem nearB_ordinary : ordinary? cageRaw 16 [] nearB =
    some ([1, 2, 3, 0], [some .eq, some .eq, some .gt]) := by decide +kernel

theorem farA_ordinary (o : Nat) (h : o ∈ [5, 6, 7]) : ordinary? cageRaw 16 [] (farA o) =
    some ([0, 2, 3, 1], [some .gt, some .eq, some .gt]) := by
  have cases : o = 5 ∨ o = 6 ∨ o = 7 := by simpa using h
  rcases cases with rfl | rfl | rfl <;> decide +kernel

theorem farB_ordinary (o : Nat) (h : o ∈ [11, 12, 13]) : ordinary? cageRaw 16 [] (farB o) =
    some ([0, 2, 3, 1], [some .gt, some .eq, some .gt]) := by
  have cases : o = 11 ∨ o = 12 ∨ o = 13 := by simpa using h
  rcases cases with rfl | rfl | rfl <;> decide +kernel

theorem farA6_diag : tracked? (farA 6) 6 =
    some { positions := [0, 2, 3, 1], unique := false, pseudoComparisons := 0 } := by
  decide +kernel

theorem farA7_diag : tracked? (farA 7) 7 =
    some { positions := [0, 2, 3, 1], unique := false, pseudoComparisons := 0 } := by
  decide +kernel

theorem farB11_diag : tracked? (farB 11) 11 =
    some { positions := [0, 2, 3, 1], unique := false, pseudoComparisons := 0 } := by
  decide +kernel

theorem farB12_diag : tracked? (farB 12) 12 =
    some { positions := [0, 2, 3, 1], unique := false, pseudoComparisons := 0 } := by
  decide +kernel

theorem farB13_diag : tracked? (farB 13) 13 =
    some { positions := [0, 2, 3, 1], unique := false, pseudoComparisons := 0 } := by
  decide +kernel

/-- The diagonal visit (mark equal to the path-back oxygen) refuses on every geometry. -/
theorem diagA (P : List CartesianPoint3) (len : P.length = 15) (o : Nat) (h : o ∈ [5, 6, 7]) :
    visitReadback? P len (farA o) o = none := by
  have cases : o = 5 ∨ o = 6 ∨ o = 7 := by simpa using h
  unfold visitReadback? visitRankedAtoms?
  rcases cases with rfl | rfl | rfl
  · rw [farA5_frameAtoms, far_o5_mark5_tracked_output]; rfl
  · rw [farA6_frameAtoms, farA6_diag]; rfl
  · rw [farA7_frameAtoms, farA7_diag]; rfl

theorem diagB (P : List CartesianPoint3) (len : P.length = 15) (o : Nat)
    (h : o ∈ [11, 12, 13]) : visitReadback? P len (farB o) o = none := by
  have cases : o = 11 ∨ o = 12 ∨ o = 13 := by simpa using h
  unfold visitReadback? visitRankedAtoms?
  rcases cases with rfl | rfl | rfl
  · rw [farB11_frameAtoms, farB11_diag]; rfl
  · rw [farB12_frameAtoms, farB12_diag]; rfl
  · rw [farB13_frameAtoms, farB13_diag]; rfl

/-! ## Generated schedule: tied children and the actual canonical expansion -/

theorem tiedChildren_root : tiedChildren cageRaw 16 [] root0 = [nearA, nearB] := by
  unfold tiedChildren
  rw [gFrame_eq, root0_frameAtoms, root_ordinary]
  decide +kernel

theorem tiedChildren_nearA : tiedChildren cageRaw 16 [] nearA = [oxA 5, oxA 6, oxA 7] := by
  unfold tiedChildren
  rw [gFrame_eq, nearA_frameAtoms, nearA_ordinary]
  decide +kernel

theorem tiedChildren_nearB : tiedChildren cageRaw 16 [] nearB = [oxB 11, oxB 12, oxB 13] := by
  unfold tiedChildren
  rw [gFrame_eq, nearB_frameAtoms, nearB_ordinary]
  decide +kernel

theorem children_nearA : cageRaw.canonicalChildren nearA = [oxA 5, oxA 6, oxA 7] := by
  decide +kernel

theorem children_nearB : cageRaw.canonicalChildren nearB = [oxB 11, oxB 12, oxB 13] := by
  decide +kernel

theorem children_oxA (o : Nat) (h : o ∈ [5, 6, 7]) :
    cageRaw.canonicalChildren (oxA o) = [farA o] := by
  have cases : o = 5 ∨ o = 6 ∨ o = 7 := by simpa using h
  rcases cases with rfl | rfl | rfl <;> decide +kernel

theorem children_oxB (o : Nat) (h : o ∈ [11, 12, 13]) :
    cageRaw.canonicalChildren (oxB o) = [farB o] := by
  have cases : o = 11 ∨ o = 12 ∨ o = 13 := by simpa using h
  rcases cases with rfl | rfl | rfl <;> decide +kernel

theorem oxA_noFrame (o : Nat) (h : o ∈ [5, 6, 7]) :
    LocalizedGenericMarkedRecalculation.frameAtoms? cageRaw (oxA o) = none := by
  have cases : o = 5 ∨ o = 6 ∨ o = 7 := by simpa using h
  rcases cases with rfl | rfl | rfl <;> decide +kernel

theorem oxB_noFrame (o : Nat) (h : o ∈ [11, 12, 13]) :
    LocalizedGenericMarkedRecalculation.frameAtoms? cageRaw (oxB o) = none := by
  have cases : o = 11 ∨ o = 12 ∨ o = 13 := by simpa using h
  rcases cases with rfl | rfl | rfl <;> decide +kernel

/-- Below a far bridgehead only a hydrogen and two oxygens follow, whose children are ring
duplicates: nothing framed remains. -/
theorem farA_leafy (o : Nat) (h : o ∈ [5, 6, 7]) :
    ∀ n ∈ cageRaw.canonicalChildren (farA o),
      LocalizedGenericMarkedRecalculation.frameAtoms? cageRaw n = none ∧
        ∀ c ∈ cageRaw.canonicalChildren n, c.forcedLeaf = true := by
  have cases : o = 5 ∨ o = 6 ∨ o = 7 := by simpa using h
  rcases cases with rfl | rfl | rfl <;> decide +kernel

theorem farB_leafy (o : Nat) (h : o ∈ [11, 12, 13]) :
    ∀ n ∈ cageRaw.canonicalChildren (farB o),
      LocalizedGenericMarkedRecalculation.frameAtoms? cageRaw n = none ∧
        ∀ c ∈ cageRaw.canonicalChildren n, c.forcedLeaf = true := by
  have cases : o = 11 ∨ o = 12 ∨ o = 13 := by simpa using h
  rcases cases with rfl | rfl | rfl <;> decide +kernel

theorem key_farA67 : canonicalOccurrenceKey (farA 6) ≠ canonicalOccurrenceKey (farA 7) := by
  decide
theorem key_farA57 : canonicalOccurrenceKey (farA 5) ≠ canonicalOccurrenceKey (farA 7) := by
  decide
theorem key_farA56 : canonicalOccurrenceKey (farA 5) ≠ canonicalOccurrenceKey (farA 6) := by
  decide
theorem key_farB1213 : canonicalOccurrenceKey (farB 12) ≠ canonicalOccurrenceKey (farB 13) := by
  decide
theorem key_farB1113 : canonicalOccurrenceKey (farB 11) ≠ canonicalOccurrenceKey (farB 13) := by
  decide
theorem key_farB1112 : canonicalOccurrenceKey (farB 11) ≠ canonicalOccurrenceKey (farB 12) := by
  decide
theorem key_nearAB : canonicalOccurrenceKey nearA ≠ canonicalOccurrenceKey nearB := by decide

/-! ## Fact flow along the arms, for every depth, geometry and context -/

theorem facts_oxA (o : Nat) (h : o ∈ [5, 6, 7]) (d : Nat) (g : Geometry)
    (s : OccurrenceAuxState) (x : Option Nat) :
    facts cageRaw 16 (d + 1) g s x (oxA o) = facts cageRaw 16 d g s x (farA o) := by
  rw [facts_succ_noFrame cageRaw 16 d g s x (oxA o) (oxA_noFrame o h), children_oxA o h]
  simp

theorem facts_oxB (o : Nat) (h : o ∈ [11, 12, 13]) (d : Nat) (g : Geometry)
    (s : OccurrenceAuxState) (x : Option Nat) :
    facts cageRaw 16 (d + 1) g s x (oxB o) = facts cageRaw 16 d g s x (farB o) := by
  rw [facts_succ_noFrame cageRaw 16 d g s x (oxB o) (oxB_noFrame o h), children_oxB o h]
  simp

theorem facts_farA (o : Nat) (h : o ∈ [5, 6, 7]) (d : Nat) (g : Geometry)
    (s : OccurrenceAuxState) (x : Option Nat) :
    facts cageRaw 16 (d + 1) g s x (farA o) =
      (descriptor? cageRaw 16 d g s x (farA o)).toList.map (factOf (farA o)) := by
  rw [facts_succ, flatMap_facts_eq_nil cageRaw 16 d g s x _ (farA_leafy o h)]
  simp

theorem facts_farB (o : Nat) (h : o ∈ [11, 12, 13]) (d : Nat) (g : Geometry)
    (s : OccurrenceAuxState) (x : Option Nat) :
    facts cageRaw 16 (d + 1) g s x (farB o) =
      (descriptor? cageRaw 16 d g s x (farB o)).toList.map (factOf (farB o)) := by
  rw [facts_succ, flatMap_facts_eq_nil cageRaw 16 d g s x _ (farB_leafy o h)]
  simp

/-- The tied children of a far bridgehead contribute no temporary fact. -/
theorem underFarA (o : Nat) (h : o ∈ [5, 6, 7]) (d : Nat) (g : Geometry)
    (s : OccurrenceAuxState) (r : Nat) :
    underWith cageRaw 16 g s (farA o) (facts cageRaw 16 d) r = [] := by
  unfold underWith
  exact flatMap_facts_eq_nil cageRaw 16 d g s (some r) _ fun n member =>
    farA_leafy o h n (mem_tiedChildren cageRaw 16 s (farA o) n member)

theorem underFarB (o : Nat) (h : o ∈ [11, 12, 13]) (d : Nat) (g : Geometry)
    (s : OccurrenceAuxState) (r : Nat) :
    underWith cageRaw 16 g s (farB o) (facts cageRaw 16 d) r = [] := by
  unfold underWith
  exact flatMap_facts_eq_nil cageRaw 16 d g s (some r) _ fun n member =>
    farB_leafy o h n (mem_tiedChildren cageRaw 16 s (farB o) n member)

section Family

variable (P : List CartesianPoint3) (len : P.length = 15)

/-! ### Far occurrences: carried near mark → the accepted marked far readback -/

theorem rawFarA (d o r : Nat) (ho : o ∈ [5, 6, 7]) (hr : r ∈ [5, 6, 7]) :
    raw? cageRaw 16 d (geomOf P len) [] (some r) (farA o) = visitReadback? P len (farA o) r := by
  have hr' : r = 5 ∨ r = 6 ∨ r = 7 := by simpa using hr
  have ho' : o = 5 ∨ o = 6 ∨ o = 7 := by simpa using ho
  unfold raw? rawWith?
  rcases ho' with rfl | rfl | rfl
  · rw [rawStep?_carried cageRaw 16 (geomOf P len) [] r (farA 5) _ [5, 4, 6, 7] [0, 2, 3, 1]
        [some .gt, some .eq, some .gt] (by rw [gFrame_eq]; exact farA5_frameAtoms)
        (farA_ordinary 5 (by decide)) (by decide) (by decide) (by decide)
        (by rcases hr' with rfl | rfl | rfl <;> decide),
      underFarA 5 (by decide)]
    exact markedReadback_empty P len (farA 5) r
  · rw [rawStep?_carried cageRaw 16 (geomOf P len) [] r (farA 6) _ [6, 4, 5, 7] [0, 2, 3, 1]
        [some .gt, some .eq, some .gt] (by rw [gFrame_eq]; exact farA6_frameAtoms)
        (farA_ordinary 6 (by decide)) (by decide) (by decide) (by decide)
        (by rcases hr' with rfl | rfl | rfl <;> decide),
      underFarA 6 (by decide)]
    exact markedReadback_empty P len (farA 6) r
  · rw [rawStep?_carried cageRaw 16 (geomOf P len) [] r (farA 7) _ [7, 4, 5, 6] [0, 2, 3, 1]
        [some .gt, some .eq, some .gt] (by rw [gFrame_eq]; exact farA7_frameAtoms)
        (farA_ordinary 7 (by decide)) (by decide) (by decide) (by decide)
        (by rcases hr' with rfl | rfl | rfl <;> decide),
      underFarA 7 (by decide)]
    exact markedReadback_empty P len (farA 7) r

theorem rawFarB (d o r : Nat) (ho : o ∈ [11, 12, 13]) (hr : r ∈ [11, 12, 13]) :
    raw? cageRaw 16 d (geomOf P len) [] (some r) (farB o) = visitReadback? P len (farB o) r := by
  have hr' : r = 11 ∨ r = 12 ∨ r = 13 := by simpa using hr
  have ho' : o = 11 ∨ o = 12 ∨ o = 13 := by simpa using ho
  unfold raw? rawWith?
  rcases ho' with rfl | rfl | rfl
  · rw [rawStep?_carried cageRaw 16 (geomOf P len) [] r (farB 11) _ [11, 10, 12, 13] [0, 2, 3, 1]
        [some .gt, some .eq, some .gt] (by rw [gFrame_eq]; exact farB11_frameAtoms)
        (farB_ordinary 11 (by decide)) (by decide) (by decide) (by decide)
        (by rcases hr' with rfl | rfl | rfl <;> decide),
      underFarB 11 (by decide)]
    exact markedReadback_empty P len (farB 11) r
  · rw [rawStep?_carried cageRaw 16 (geomOf P len) [] r (farB 12) _ [12, 10, 11, 13] [0, 2, 3, 1]
        [some .gt, some .eq, some .gt] (by rw [gFrame_eq]; exact farB12_frameAtoms)
        (farB_ordinary 12 (by decide)) (by decide) (by decide) (by decide)
        (by rcases hr' with rfl | rfl | rfl <;> decide),
      underFarB 12 (by decide)]
    exact markedReadback_empty P len (farB 12) r
  · rw [rawStep?_carried cageRaw 16 (geomOf P len) [] r (farB 13) _ [13, 10, 11, 12] [0, 2, 3, 1]
        [some .gt, some .eq, some .gt] (by rw [gFrame_eq]; exact farB13_frameAtoms)
        (farB_ordinary 13 (by decide)) (by decide) (by decide) (by decide)
        (by rcases hr' with rfl | rfl | rfl <;> decide),
      underFarB 13 (by decide)]
    exact markedReadback_empty P len (farB 13) r

/-- The mirror-cased far fact is the uppercase marked far readback. -/
theorem descriptorFarA (d o r : Nat) (ho : o ∈ [5, 6, 7]) (hr : r ∈ [5, 6, 7]) :
    descriptor? cageRaw 16 d (geomOf P len) [] (some r) (farA o) =
      (visitReadback? P len (farA o) r).map LocalizedTetrahedralRSPseudoDescriptor.chiral := by
  unfold descriptor? descriptorWith?
  have original : rawWith? cageRaw 16 (geomOf P len) [] (some r) (farA o) (facts cageRaw 16 d) =
      visitReadback? P len (farA o) r := rawFarA P len d o r ho hr
  have reflected : rawWith? cageRaw 16 (mirror (geomOf P len)) [] (some r) (farA o)
      (facts cageRaw 16 d) = visitReadback? (mirrorPoints P) (mirrorLength P len) (farA o) r := by
    rw [geomOf_mirror]
    exact rawFarA _ _ d o r ho hr
  rw [original, reflected, visitReadback_mirror P len]
  cases visitReadback? P len (farA o) r with
  | none => rfl
  | some raw => exact caseFromMirror?_eq_swap raw

theorem descriptorFarB (d o r : Nat) (ho : o ∈ [11, 12, 13]) (hr : r ∈ [11, 12, 13]) :
    descriptor? cageRaw 16 d (geomOf P len) [] (some r) (farB o) =
      (visitReadback? P len (farB o) r).map LocalizedTetrahedralRSPseudoDescriptor.chiral := by
  unfold descriptor? descriptorWith?
  have original : rawWith? cageRaw 16 (geomOf P len) [] (some r) (farB o) (facts cageRaw 16 d) =
      visitReadback? P len (farB o) r := rawFarB P len d o r ho hr
  have reflected : rawWith? cageRaw 16 (mirror (geomOf P len)) [] (some r) (farB o)
      (facts cageRaw 16 d) = visitReadback? (mirrorPoints P) (mirrorLength P len) (farB o) r := by
    rw [geomOf_mirror]
    exact rawFarB _ _ d o r ho hr
  rw [original, reflected, visitReadback_mirror P len]
  cases visitReadback? P len (farB o) r with
  | none => rfl
  | some raw => exact caseFromMirror?_eq_swap raw

/-! ### Far occurrences under a root reference: own context, refused by disagreement -/

theorem rawFarA_root (nondeg : Nondegenerate P len) (d o ρ : Nat) (ho : o ∈ [5, 6, 7])
    (hρ : ρ = 3 ∨ ρ = 9) :
    raw? cageRaw 16 d (geomOf P len) [] (some ρ) (farA o) = none := by
  obtain ⟨h65, h75, h56, h76, h57, h67⟩ := farReadbackA_letters P len nondeg
  have ho' : o = 5 ∨ o = 6 ∨ o = 7 := by simpa using ho
  unfold raw? rawWith?
  rcases ho' with rfl | rfl | rfl
  · rw [rawStep?_consensus cageRaw 16 (geomOf P len) [] (some ρ) (farA 5) _ [5, 4, 6, 7]
        [0, 2, 3, 1] [some .gt, some .eq, some .gt] (by rw [gFrame_eq]; exact farA5_frameAtoms)
        (farA_ordinary 5 (by decide)) (by decide) (by decide) (by decide)
        (fun r h => by cases h; rcases hρ with rfl | rfl <;> decide)]
    simp only [underFarA 5 (by decide), appendFacts?_nil, Option.bind_some]
    show consensus [markedReadback? cageRaw 16 (geomOf P len) [] (farA 5) 6,
      markedReadback? cageRaw 16 (geomOf P len) [] (farA 5) 7] = none
    rw [markedReadback_empty, markedReadback_empty, h56, h57]
    generalize farLetterA P len = a
    cases a <;> rfl
  · rw [rawStep?_consensus cageRaw 16 (geomOf P len) [] (some ρ) (farA 6) _ [6, 4, 5, 7]
        [0, 2, 3, 1] [some .gt, some .eq, some .gt] (by rw [gFrame_eq]; exact farA6_frameAtoms)
        (farA_ordinary 6 (by decide)) (by decide) (by decide) (by decide)
        (fun r h => by cases h; rcases hρ with rfl | rfl <;> decide)]
    simp only [underFarA 6 (by decide), appendFacts?_nil, Option.bind_some]
    show consensus [markedReadback? cageRaw 16 (geomOf P len) [] (farA 6) 5,
      markedReadback? cageRaw 16 (geomOf P len) [] (farA 6) 7] = none
    rw [markedReadback_empty, markedReadback_empty, h65, h67]
    generalize farLetterA P len = a
    cases a <;> rfl
  · rw [rawStep?_consensus cageRaw 16 (geomOf P len) [] (some ρ) (farA 7) _ [7, 4, 5, 6]
        [0, 2, 3, 1] [some .gt, some .eq, some .gt] (by rw [gFrame_eq]; exact farA7_frameAtoms)
        (farA_ordinary 7 (by decide)) (by decide) (by decide) (by decide)
        (fun r h => by cases h; rcases hρ with rfl | rfl <;> decide)]
    simp only [underFarA 7 (by decide), appendFacts?_nil, Option.bind_some]
    show consensus [markedReadback? cageRaw 16 (geomOf P len) [] (farA 7) 5,
      markedReadback? cageRaw 16 (geomOf P len) [] (farA 7) 6] = none
    rw [markedReadback_empty, markedReadback_empty, h75, h76]
    generalize farLetterA P len = a
    cases a <;> rfl

theorem rawFarB_root (nondeg : Nondegenerate P len) (d o ρ : Nat) (ho : o ∈ [11, 12, 13])
    (hρ : ρ = 3 ∨ ρ = 9) :
    raw? cageRaw 16 d (geomOf P len) [] (some ρ) (farB o) = none := by
  obtain ⟨h1211, h1311, h1112, h1312, h1113, h1213⟩ := farReadbackB_letters P len nondeg
  have ho' : o = 11 ∨ o = 12 ∨ o = 13 := by simpa using ho
  unfold raw? rawWith?
  rcases ho' with rfl | rfl | rfl
  · rw [rawStep?_consensus cageRaw 16 (geomOf P len) [] (some ρ) (farB 11) _ [11, 10, 12, 13]
        [0, 2, 3, 1] [some .gt, some .eq, some .gt] (by rw [gFrame_eq]; exact farB11_frameAtoms)
        (farB_ordinary 11 (by decide)) (by decide) (by decide) (by decide)
        (fun r h => by cases h; rcases hρ with rfl | rfl <;> decide)]
    simp only [underFarB 11 (by decide), appendFacts?_nil, Option.bind_some]
    show consensus [markedReadback? cageRaw 16 (geomOf P len) [] (farB 11) 12,
      markedReadback? cageRaw 16 (geomOf P len) [] (farB 11) 13] = none
    rw [markedReadback_empty, markedReadback_empty, h1112, h1113]
    generalize farLetterB P len = a
    cases a <;> rfl
  · rw [rawStep?_consensus cageRaw 16 (geomOf P len) [] (some ρ) (farB 12) _ [12, 10, 11, 13]
        [0, 2, 3, 1] [some .gt, some .eq, some .gt] (by rw [gFrame_eq]; exact farB12_frameAtoms)
        (farB_ordinary 12 (by decide)) (by decide) (by decide) (by decide)
        (fun r h => by cases h; rcases hρ with rfl | rfl <;> decide)]
    simp only [underFarB 12 (by decide), appendFacts?_nil, Option.bind_some]
    show consensus [markedReadback? cageRaw 16 (geomOf P len) [] (farB 12) 11,
      markedReadback? cageRaw 16 (geomOf P len) [] (farB 12) 13] = none
    rw [markedReadback_empty, markedReadback_empty, h1211, h1213]
    generalize farLetterB P len = a
    cases a <;> rfl
  · rw [rawStep?_consensus cageRaw 16 (geomOf P len) [] (some ρ) (farB 13) _ [13, 10, 11, 12]
        [0, 2, 3, 1] [some .gt, some .eq, some .gt] (by rw [gFrame_eq]; exact farB13_frameAtoms)
        (farB_ordinary 13 (by decide)) (by decide) (by decide) (by decide)
        (fun r h => by cases h; rcases hρ with rfl | rfl <;> decide)]
    simp only [underFarB 13 (by decide), appendFacts?_nil, Option.bind_some]
    show consensus [markedReadback? cageRaw 16 (geomOf P len) [] (farB 13) 11,
      markedReadback? cageRaw 16 (geomOf P len) [] (farB 13) 12] = none
    rw [markedReadback_empty, markedReadback_empty, h1311, h1312]
    generalize farLetterB P len = a
    cases a <;> rfl

theorem descriptorFarA_root (nondeg : Nondegenerate P len) (d o ρ : Nat) (ho : o ∈ [5, 6, 7])
    (hρ : ρ = 3 ∨ ρ = 9) :
    descriptor? cageRaw 16 d (geomOf P len) [] (some ρ) (farA o) = none := by
  unfold descriptor? descriptorWith?
  rw [show rawWith? cageRaw 16 (geomOf P len) [] (some ρ) (farA o) (facts cageRaw 16 d) = none
    from rawFarA_root P len nondeg d o ρ ho hρ]
  rfl

theorem descriptorFarB_root (nondeg : Nondegenerate P len) (d o ρ : Nat)
    (ho : o ∈ [11, 12, 13]) (hρ : ρ = 3 ∨ ρ = 9) :
    descriptor? cageRaw 16 d (geomOf P len) [] (some ρ) (farB o) = none := by
  unfold descriptor? descriptorWith?
  rw [show rawWith? cageRaw 16 (geomOf P len) [] (some ρ) (farB o) (facts cageRaw 16 d) = none
    from rawFarB_root P len nondeg d o ρ ho hρ]
  rfl

/-! ### Near occurrences: generated references `{5,6,7}` / `{11,12,13}`, generated far facts -/

/-- The generated temporary state under a near reference is the accepted computed snapshot. -/
theorem underNearA (nondeg : Nondegenerate P len) (d r : Nat) (hr : r ∈ [5, 6, 7]) :
    underWith cageRaw 16 (geomOf P len) [] nearA (facts cageRaw 16 (d + 2)) r =
      computedStateA P len r true := by
  obtain ⟨h65, h75, h56, h76, h57, h67⟩ := farReadbackA_letters P len nondeg
  unfold underWith
  rw [tiedChildren_nearA]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [facts_oxA 5 (by decide), facts_oxA 6 (by decide), facts_oxA 7 (by decide),
    facts_farA 5 (by decide), facts_farA 6 (by decide), facts_farA 7 (by decide),
    descriptorFarA P len d 5 r (by decide) hr, descriptorFarA P len d 6 r (by decide) hr,
    descriptorFarA P len d 7 r (by decide) hr]
  have hr' : r = 5 ∨ r = 6 ∨ r = 7 := by simpa using hr
  rcases hr' with rfl | rfl | rfl
  · rw [diagA P len 5 (by decide), h65, h75]
    rfl
  · rw [diagA P len 6 (by decide), h56, h76]
    show _ = tempStateA 6 (farLetterA P len).swap true
    generalize farLetterA P len = a
    cases a <;> rfl
  · rw [diagA P len 7 (by decide), h57, h67]
    rfl

theorem underNearB (nondeg : Nondegenerate P len) (d r : Nat) (hr : r ∈ [11, 12, 13]) :
    underWith cageRaw 16 (geomOf P len) [] nearB (facts cageRaw 16 (d + 2)) r =
      computedStateB P len r true := by
  obtain ⟨h1211, h1311, h1112, h1312, h1113, h1213⟩ := farReadbackB_letters P len nondeg
  unfold underWith
  rw [tiedChildren_nearB]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [facts_oxB 11 (by decide), facts_oxB 12 (by decide), facts_oxB 13 (by decide),
    facts_farB 11 (by decide), facts_farB 12 (by decide), facts_farB 13 (by decide),
    descriptorFarB P len d 11 r (by decide) hr, descriptorFarB P len d 12 r (by decide) hr,
    descriptorFarB P len d 13 r (by decide) hr]
  have hr' : r = 11 ∨ r = 12 ∨ r = 13 := by simpa using hr
  rcases hr' with rfl | rfl | rfl
  · rw [diagB P len 11 (by decide), h1211, h1311]
    rfl
  · rw [diagB P len 12 (by decide), h1112, h1312]
    show _ = tempStateB 12 (farLetterB P len).swap true
    generalize farLetterB P len = a
    cases a <;> rfl
  · rw [diagB P len 13 (by decide), h1113, h1213]
    rfl

theorem appendStateA (r : Nat) (hr : r ∈ [5, 6, 7]) :
    appendFacts? [] (computedStateA P len r true) = some (computedStateA P len r true) := by
  have hr' : r = 5 ∨ r = 6 ∨ r = 7 := by simpa using hr
  rcases hr' with rfl | rfl | rfl
  · exact appendFacts?_two _ _ key_farA67
  · exact appendFacts?_two _ _ key_farA57
  · exact appendFacts?_two _ _ key_farA56

theorem appendStateB (r : Nat) (hr : r ∈ [11, 12, 13]) :
    appendFacts? [] (computedStateB P len r true) = some (computedStateB P len r true) := by
  have hr' : r = 11 ∨ r = 12 ∨ r = 13 := by simpa using hr
  rcases hr' with rfl | rfl | rfl
  · exact appendFacts?_two _ _ key_farB1213
  · exact appendFacts?_two _ _ key_farB1113
  · exact appendFacts?_two _ _ key_farB1112

/-- Under a root reference the near occurrence opens its own context; the consensus over its
three generated references is the joint bridgehead letter (accepted `nearRecalcA`). -/
theorem rawNearA (nondeg : Nondegenerate P len) (d ρ : Nat) (hρ : ρ = 3 ∨ ρ = 9) :
    rawWith? cageRaw 16 (geomOf P len) [] (some ρ) nearA (facts cageRaw 16 (d + 2)) =
      some (jointLetterA P len) := by
  unfold rawWith?
  rw [rawStep?_consensus cageRaw 16 (geomOf P len) [] (some ρ) nearA _ [0, 5, 6, 7] [1, 2, 3, 0]
      [some .eq, some .eq, some .gt] (by rw [gFrame_eq]; exact nearA_frameAtoms) nearA_ordinary
      (by decide) (by decide) (by decide)
      (fun r h => by cases h; rcases hρ with rfl | rfl <;> decide)]
  show consensus [(appendFacts? [] (underWith cageRaw 16 (geomOf P len) [] nearA
      (facts cageRaw 16 (d + 2)) 5)).bind fun temp =>
        markedReadback? cageRaw 16 (geomOf P len) temp nearA 5,
    (appendFacts? [] (underWith cageRaw 16 (geomOf P len) [] nearA
      (facts cageRaw 16 (d + 2)) 6)).bind fun temp =>
        markedReadback? cageRaw 16 (geomOf P len) temp nearA 6,
    (appendFacts? [] (underWith cageRaw 16 (geomOf P len) [] nearA
      (facts cageRaw 16 (d + 2)) 7)).bind fun temp =>
        markedReadback? cageRaw 16 (geomOf P len) temp nearA 7] = _
  rw [underNearA P len nondeg d 5 (by decide), underNearA P len nondeg d 6 (by decide),
    underNearA P len nondeg d 7 (by decide), appendStateA P len 5 (by decide),
    appendStateA P len 6 (by decide), appendStateA P len 7 (by decide)]
  show consensus [markedReadback? cageRaw 16 (geomOf P len) (computedStateA P len 5 true) nearA 5,
    markedReadback? cageRaw 16 (geomOf P len) (computedStateA P len 6 true) nearA 6,
    markedReadback? cageRaw 16 (geomOf P len) (computedStateA P len 7 true) nearA 7] = _
  rw [markedReadback_eq, markedReadback_eq, markedReadback_eq,
    nearRecalcA P len nondeg 5 (by decide) true, nearRecalcA P len nondeg 6 (by decide) true,
    nearRecalcA P len nondeg 7 (by decide) true]
  exact consensus_three_same _

theorem rawNearB (nondeg : Nondegenerate P len) (d ρ : Nat) (hρ : ρ = 3 ∨ ρ = 9) :
    rawWith? cageRaw 16 (geomOf P len) [] (some ρ) nearB (facts cageRaw 16 (d + 2)) =
      some (jointLetterB P len) := by
  unfold rawWith?
  rw [rawStep?_consensus cageRaw 16 (geomOf P len) [] (some ρ) nearB _ [0, 11, 12, 13]
      [1, 2, 3, 0] [some .eq, some .eq, some .gt] (by rw [gFrame_eq]; exact nearB_frameAtoms)
      nearB_ordinary (by decide) (by decide) (by decide)
      (fun r h => by cases h; rcases hρ with rfl | rfl <;> decide)]
  show consensus [(appendFacts? [] (underWith cageRaw 16 (geomOf P len) [] nearB
      (facts cageRaw 16 (d + 2)) 11)).bind fun temp =>
        markedReadback? cageRaw 16 (geomOf P len) temp nearB 11,
    (appendFacts? [] (underWith cageRaw 16 (geomOf P len) [] nearB
      (facts cageRaw 16 (d + 2)) 12)).bind fun temp =>
        markedReadback? cageRaw 16 (geomOf P len) temp nearB 12,
    (appendFacts? [] (underWith cageRaw 16 (geomOf P len) [] nearB
      (facts cageRaw 16 (d + 2)) 13)).bind fun temp =>
        markedReadback? cageRaw 16 (geomOf P len) temp nearB 13] = _
  rw [underNearB P len nondeg d 11 (by decide), underNearB P len nondeg d 12 (by decide),
    underNearB P len nondeg d 13 (by decide), appendStateB P len 11 (by decide),
    appendStateB P len 12 (by decide), appendStateB P len 13 (by decide)]
  show consensus [
    markedReadback? cageRaw 16 (geomOf P len) (computedStateB P len 11 true) nearB 11,
    markedReadback? cageRaw 16 (geomOf P len) (computedStateB P len 12 true) nearB 12,
    markedReadback? cageRaw 16 (geomOf P len) (computedStateB P len 13 true) nearB 13] = _
  rw [markedReadback_eq, markedReadback_eq, markedReadback_eq,
    nearRecalcB P len nondeg 11 (by decide) true, nearRecalcB P len nondeg 12 (by decide) true,
    nearRecalcB P len nondeg 13 (by decide) true]
  exact consensus_three_same _

/-- Mirror recomputation leaves the near letter unchanged: the generated near fact is lowercase. -/
theorem descriptorNearA (nondeg : Nondegenerate P len) (d ρ : Nat) (hρ : ρ = 3 ∨ ρ = 9) :
    descriptor? cageRaw 16 (d + 2) (geomOf P len) [] (some ρ) nearA =
      some (.pseudoasymmetric (pseudoRSOfRS (jointLetterA P len))) := by
  unfold descriptor? descriptorWith?
  rw [rawNearA P len nondeg d ρ hρ, geomOf_mirror,
    rawNearA _ _ (nondegenerate_mirror P len nondeg) d ρ hρ, jointA_mirror]
  exact caseFromMirror?_eq_same _

theorem descriptorNearB (nondeg : Nondegenerate P len) (d ρ : Nat) (hρ : ρ = 3 ∨ ρ = 9) :
    descriptor? cageRaw 16 (d + 2) (geomOf P len) [] (some ρ) nearB =
      some (.pseudoasymmetric (pseudoRSOfRS (jointLetterB P len))) := by
  unfold descriptor? descriptorWith?
  rw [rawNearB P len nondeg d ρ hρ, geomOf_mirror,
    rawNearB _ _ (nondegenerate_mirror P len nondeg) d ρ hρ, jointB_mirror]
  exact caseFromMirror?_eq_same _

/-- Facts flowing from a near center to the root: exactly one lowercase fact at the near key; the
far occurrences refuse under the root reference and contribute nothing. -/
theorem factsNearA (nondeg : Nondegenerate P len) (d ρ : Nat) (hρ : ρ = 3 ∨ ρ = 9) :
    facts cageRaw 16 (d + 3) (geomOf P len) [] (some ρ) nearA =
      [tempFact nearA (jointLetterA P len) false] := by
  rw [facts_succ, children_nearA]
  have descent : ∀ o ∈ [5, 6, 7],
      facts cageRaw 16 (d + 2) (geomOf P len) [] (some ρ) (oxA o) = [] := by
    intro o ho
    rw [facts_oxA o ho, facts_farA o ho, descriptorFarA_root P len nondeg d o ρ ho hρ]
    rfl
  rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_cons, List.flatMap_nil,
    descent 5 (by decide), descent 6 (by decide), descent 7 (by decide),
    descriptorNearA P len nondeg d ρ hρ]
  generalize jointLetterA P len = j
  cases j <;> rfl

theorem factsNearB (nondeg : Nondegenerate P len) (d ρ : Nat) (hρ : ρ = 3 ∨ ρ = 9) :
    facts cageRaw 16 (d + 3) (geomOf P len) [] (some ρ) nearB =
      [tempFact nearB (jointLetterB P len) false] := by
  rw [facts_succ, children_nearB]
  have descent : ∀ o ∈ [11, 12, 13],
      facts cageRaw 16 (d + 2) (geomOf P len) [] (some ρ) (oxB o) = [] := by
    intro o ho
    rw [facts_oxB o ho, facts_farB o ho, descriptorFarB_root P len nondeg d o ρ ho hρ]
    rfl
  rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_cons, List.flatMap_nil,
    descent 11 (by decide), descent 12 (by decide), descent 13 (by decide),
    descriptorNearB P len nondeg d ρ hρ]
  generalize jointLetterB P len = j
  cases j <;> rfl

/-! ### Root: generated references `{3, 9}`, generated near facts, two-reference consensus -/

theorem underRoot (nondeg : Nondegenerate P len) (ρ : Nat) (hρ : ρ = 3 ∨ ρ = 9) :
    underWith cageRaw 16 (geomOf P len) [] root0 (facts cageRaw 16 (12 + 3)) ρ =
      rootTemp (jointLetterA P len) (jointLetterB P len) false := by
  unfold underWith
  rw [tiedChildren_root, List.flatMap_cons, List.flatMap_cons, List.flatMap_nil,
    factsNearA P len nondeg 12 ρ hρ, factsNearB P len nondeg 12 ρ hρ]
  rfl

theorem appendRoot :
    appendFacts? [] (rootTemp (jointLetterA P len) (jointLetterB P len) false) =
      some (rootTemp (jointLetterA P len) (jointLetterB P len) false) :=
  appendFacts?_two _ _ key_nearAB

theorem rawRoot (nondeg : Nondegenerate P len) :
    rawWith? cageRaw 16 (geomOf P len) [] none root0 (facts cageRaw 16 (12 + 3)) =
      rootConsensus? P len false := by
  unfold rawWith?
  rw [rawStep?_consensus cageRaw 16 (geomOf P len) [] none root0 _ [1, 2, 3, 9] [1, 2, 3, 0]
      [some .gt, some .eq, some .gt] (by rw [gFrame_eq]; exact root0_frameAtoms) root_ordinary
      (by decide) (by decide) (by decide) (fun r h => by cases h)]
  show consensus [(appendFacts? [] (underWith cageRaw 16 (geomOf P len) [] root0
      (facts cageRaw 16 (12 + 3)) 3)).bind fun temp =>
        markedReadback? cageRaw 16 (geomOf P len) temp root0 3,
    (appendFacts? [] (underWith cageRaw 16 (geomOf P len) [] root0
      (facts cageRaw 16 (12 + 3)) 9)).bind fun temp =>
        markedReadback? cageRaw 16 (geomOf P len) temp root0 9] = _
  rw [underRoot P len nondeg 3 (Or.inl rfl), underRoot P len nondeg 9 (Or.inr rfl), appendRoot]
  show consensus [markedReadback? cageRaw 16 (geomOf P len)
      (rootTemp (jointLetterA P len) (jointLetterB P len) false) root0 3,
    markedReadback? cageRaw 16 (geomOf P len)
      (rootTemp (jointLetterA P len) (jointLetterB P len) false) root0 9] = _
  rw [markedReadback_eq, markedReadback_eq, consensus_pair]
  unfold rootConsensus?
  cases readbackWith? P len (rootTemp (jointLetterA P len) (jointLetterB P len) false) root0 3 <;>
    cases readbackWith? P len (rootTemp (jointLetterA P len) (jointLetterB P len) false)
      root0 9 <;> rfl

/-- **The generic recalculation of the cage root from its actual graph and geometry** is the
uppercase accepted two-reference root consensus. Fuel and depth are generated from the atom
count; no mark, visit, letter or case is supplied. -/
theorem assignCenter_eq_rootConsensus (nondeg : Nondegenerate P len) :
    assignCenter? cageRaw (comparatorFuel cageRaw) (geomOf P len) 0 =
      (rootConsensus? P len false).map LocalizedTetrahedralRSPseudoDescriptor.chiral := by
  show descriptorWith? cageRaw 16 (geomOf P len) [] none root0 (facts cageRaw 16 (12 + 3)) = _
  unfold descriptorWith?
  rw [rawRoot P len nondeg, geomOf_mirror, rawRoot _ _ (nondegenerate_mirror P len nondeg),
    rootConsensus_mirror P len nondeg false]
  cases rootConsensus? P len false with
  | none => rfl
  | some raw => exact caseFromMirror?_eq_swap raw

/-- **The generic construction reproduces the accepted mirror-derived pipeline** for every
nondegenerate family geometry and every accepted mark pair, with generated references and
schedule and no supplied auxiliary labels or case flags. -/
theorem assignCenter_eq_assign (nondeg : Nondegenerate P len) (rA rB : Nat)
    (hA : rA ∈ [5, 6, 7]) (hB : rB ∈ [11, 12, 13]) :
    assignCenter? cageRaw (comparatorFuel cageRaw) (geomOf P len) 0 = assign? P len rA rB := by
  rw [assignCenter_eq_rootConsensus P len nondeg, assign_eq_chiral P len nondeg rA rB hA hB,
    pipeline_eq_rootConsensus P len nondeg rA rB hA hB true true false]

/-- The generic result exists iff the root is pairwise properly distinguishable in the formal
calibrated domain. -/
theorem assignCenter_isSome_iff_pairwise (nondeg : Nondegenerate P len) :
    (assignCenter? cageRaw (comparatorFuel cageRaw) (geomOf P len) 0).isSome = true ↔
      MultiCenterMolecule.PairwiseProperDistinguishable
        (certifiedWith P len).detectedMultiCenterMolecule (detectedCfgWith P len)
        (rootWith P len) := by
  rw [assignCenter_eq_rootConsensus P len nondeg]
  simpa using rootConsensus_isSome_iff_pairwise P len nondeg false

end Family

/-- The accepted fixture table is a demonstrated input of the generic construction. -/
theorem fixture_eq_assign :
    assignCenter? cageRaw (comparatorFuel cageRaw) (geomOf positions positions_length) 0 =
      assign? positions positions_length 5 11 :=
  assignCenter_eq_assign positions positions_length inNondegenerate 5 11 (by decide) (by decide)

/-- Stage-1 runtime observation retained as evidence: one far occurrence under a carried near
reference, actual interpreter execution on the fixture coordinates. -/
def fixtureGeom : Geometry := fun atom => positions[atom]?

#eval descriptor? cageRaw (comparatorFuel cageRaw) 0 fixtureGeom [] (some 6) (farA 5)

end TetraStereo.OneCenter.LocalizedGenericMarkedRecalculationCage

assert_kernel_only TetraStereo.OneCenter.LocalizedGenericMarkedRecalculationCage.markedReadback_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedGenericMarkedRecalculationCage.diagA
assert_kernel_only TetraStereo.OneCenter.LocalizedGenericMarkedRecalculationCage.diagB
assert_kernel_only TetraStereo.OneCenter.LocalizedGenericMarkedRecalculationCage.tiedChildren_root
assert_kernel_only TetraStereo.OneCenter.LocalizedGenericMarkedRecalculationCage.tiedChildren_nearA
assert_kernel_only TetraStereo.OneCenter.LocalizedGenericMarkedRecalculationCage.tiedChildren_nearB
assert_kernel_only TetraStereo.OneCenter.LocalizedGenericMarkedRecalculationCage.descriptorFarA
assert_kernel_only TetraStereo.OneCenter.LocalizedGenericMarkedRecalculationCage.descriptorFarB
assert_kernel_only TetraStereo.OneCenter.LocalizedGenericMarkedRecalculationCage.descriptorFarA_root
assert_kernel_only TetraStereo.OneCenter.LocalizedGenericMarkedRecalculationCage.descriptorFarB_root
assert_kernel_only TetraStereo.OneCenter.LocalizedGenericMarkedRecalculationCage.underNearA
assert_kernel_only TetraStereo.OneCenter.LocalizedGenericMarkedRecalculationCage.underNearB
assert_kernel_only TetraStereo.OneCenter.LocalizedGenericMarkedRecalculationCage.descriptorNearA
assert_kernel_only TetraStereo.OneCenter.LocalizedGenericMarkedRecalculationCage.descriptorNearB
assert_kernel_only TetraStereo.OneCenter.LocalizedGenericMarkedRecalculationCage.factsNearA
assert_kernel_only TetraStereo.OneCenter.LocalizedGenericMarkedRecalculationCage.factsNearB
assert_kernel_only TetraStereo.OneCenter.LocalizedGenericMarkedRecalculationCage.rawRoot
assert_kernel_only TetraStereo.OneCenter.LocalizedGenericMarkedRecalculationCage.assignCenter_eq_rootConsensus
assert_kernel_only TetraStereo.OneCenter.LocalizedGenericMarkedRecalculationCage.assignCenter_eq_assign
assert_kernel_only TetraStereo.OneCenter.LocalizedGenericMarkedRecalculationCage.assignCenter_isSome_iff_pairwise
assert_kernel_only TetraStereo.OneCenter.LocalizedGenericMarkedRecalculationCage.fixture_eq_assign
