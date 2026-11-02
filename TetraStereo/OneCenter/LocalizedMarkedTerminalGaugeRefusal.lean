import TetraStereo.OneCenter.LocalizedMarkedTerminalGaugeFrame
import TetraStereo.OneCenter.LocalizedMarkedOperationSimulation
import TetraStereo.OneCenter.CIPAuthoritativeRule6Scheduler
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Own-reference cancellation at an outward terminal-twin center

On the actual uncapped recursive constructor (`LocalizedMarkedUncappedEvaluator.operations`,
input state `[]`), an occurrence with two outward terminal twins produces no descriptor when
it opens its own context or carries a mark different from both twins:

* the ordinary branch is never strict (the twins tie through the actual comparator and the
  adjacent chain is transitive);
* both twin atoms are generated eligible references (same tied run);
* a non-twin eligible reference leaves the twins tied under promotion bits and the uncapped
  ranking non-unique (root's law), so its reading refuses;
* when all eligible references are twins, the generated snapshot is empty (terminal leaves have
  no frame and no children), the two readings are complements by the comparator symmetry, and
  the consensus refuses;
* a carried non-twin reference inside the frame refuses by the same tie.

Hence the mirror-cased descriptor refuses for every geometry in these contexts, and the center's
own assignment refuses. For an actual generated promotion snapshot, ancestry and source-frame
selection exclude a carried twin mark; the final theorem derives that no fact is keyed at such
a center. No coordinate nondegeneracy, calibration or totality is assumed.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedTerminalGaugeRefusal

open LocalizedMarkedTerminalGaugeKeys LocalizedMarkedTerminalGaugeSwap
open LocalizedMarkedTerminalGaugeFrame LocalizedMarkedTerminalGaugeFrame.TwinCenter
open LocalizedMarkedTerminalReferenceScope LocalizedMarkedTerminalCursor
open LocalizedMarkedTerminalComparison LocalizedMarkedReachedFrameNeighbors
open LocalizedMarkedReachableConfigurations LocalizedMarkedUncappedOperations
open LocalizedMarkedOperationEvaluator LocalizedMarkedOperationSimulation
open LocalizedMarkedUncappedEvaluator (operations)
open LocalizedGenericMarkedRecalculation (Geometry frameAtomsOf consistent strict tiedPositions
  atomsAt eligibleOf consensus appendFacts? caseFromMirror? factOf)
open AuthoritativeCIPRule6Scheduler
open AuthoritativeCIPOccurrenceDescriptorComparatorLaws
open AuthoritativeCIPMoleculeCursorRanking

abbrev Cursor := CanonicalRerootCursor
abbrev Node := RawMolecule.CanonicalBranchNode

/-! ## Consensus -/

theorem consensus_eq_some : ∀ (L : List (Option RS)) (a : RS), consensus L = some a →
    ∀ x ∈ L, x = some a
  | [], _, h, _, member => by simp at member
  | [x], a, h, y, member => by
      simp only [List.mem_singleton] at member
      subst member
      simpa [consensus] using h
  | x :: y :: rest, a, h, z, member => by
      simp only [consensus] at h
      cases hx : x with
      | none => rw [hx] at h; simp at h
      | some b =>
          rw [hx] at h
          cases hr : consensus (y :: rest) with
          | none => rw [hr] at h; simp at h
          | some c =>
              rw [hr] at h
              by_cases bc : b = c
              · simp only [bc, ↓reduceIte, Option.some.injEq] at h
                subst h
                rcases List.mem_cons.mp member with rfl | tailMember
                · rw [hx, bc]
                · exact consensus_eq_some (y :: rest) c hr z tailMember
              · simp [bc] at h

theorem consensus_none_of_mem_none (L : List (Option RS)) (member : none ∈ L) :
    consensus L = none := by
  cases h : consensus L with
  | none => rfl
  | some a => cases consensus_eq_some L a h none member

theorem consensus_none_of_two (L : List (Option RS)) (x y : Option RS) (hx : x ∈ L) (hy : y ∈ L)
    (ne : x ≠ y) : consensus L = none := by
  cases h : consensus L with
  | none => rfl
  | some a =>
      have := consensus_eq_some L a h
      exact absurd ((this x hx).trans (this y hy).symm) ne

/-! ## Membership in generated tied runs -/

theorem tied_cons_cons (prev : Bool) (p q : Nat) (rest : List Nat) (d : Option Ordering)
    (ds : List (Option Ordering)) :
    tiedPositions prev (p :: q :: rest) (d :: ds) =
      (if prev || (d == some Ordering.eq) then [p] else []) ++
        tiedPositions (d == some Ordering.eq) (q :: rest) ds := rfl

theorem head_mem_tied_true (q : Nat) (rest : List Nat) (ds : List (Option Ordering)) :
    q ∈ tiedPositions true (q :: rest) ds := by
  cases rest with
  | nil => simp [tiedPositions]
  | cons r rest =>
      cases ds with
      | nil => simp [tiedPositions]
      | cons d ds => simp [tied_cons_cons]

theorem mem_tied_of_next : ∀ (prev : Bool) (sorted : List Nat) (adjacent : List (Option Ordering))
    (k : Nat) (hk : k + 1 < sorted.length), adjacent[k]? = some (some Ordering.eq) →
    sorted[k] ∈ tiedPositions prev sorted adjacent
  | _, [], _, k, hk, _ => by simp at hk
  | _, [_], _, k, hk, _ => by simp at hk
  | prev, p :: q :: rest, [], k, _, h => by simp at h
  | prev, p :: q :: rest, d :: ds, 0, _, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp [tied_cons_cons]
  | prev, p :: q :: rest, d :: ds, k + 1, hk, h => by
      simp only [List.getElem?_cons_succ] at h
      rw [tied_cons_cons]
      apply List.mem_append_right
      exact mem_tied_of_next (d == some Ordering.eq) (q :: rest) ds k (by simpa using hk) h

theorem mem_tied_of_prev : ∀ (prev : Bool) (sorted : List Nat) (adjacent : List (Option Ordering))
    (k : Nat) (hk : k + 1 < sorted.length), adjacent[k]? = some (some Ordering.eq) →
    sorted[k + 1] ∈ tiedPositions prev sorted adjacent
  | _, [], _, k, hk, _ => by simp at hk
  | _, [_], _, k, hk, _ => by simp at hk
  | prev, p :: q :: rest, [], k, _, h => by simp at h
  | prev, p :: q :: rest, d :: ds, 0, _, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      rw [tied_cons_cons]
      apply List.mem_append_right
      simpa using head_mem_tied_true q rest ds
  | prev, p :: q :: rest, d :: ds, k + 1, hk, h => by
      simp only [List.getElem?_cons_succ] at h
      rw [tied_cons_cons]
      apply List.mem_append_right
      exact mem_tied_of_prev (d == some Ordering.eq) (q :: rest) ds k (by simpa using hk) h

/-! ## The actual ordinary adjacent chain -/

section Chain

variable (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat) (roots : List Cursor)

/-- A fixed cursor used only to total the position lookup; never read at valid positions. -/
def dummy : Cursor := { node := canonicalCenterRoot 0 }

/-- The ordinary projected key of the cursor at a frame position. -/
def keyAt (p : Nat) : FailClosedOccurrenceBranchProjectedKey :=
  buildFailClosedOccurrenceBranchProjectedKey mol state fuel (roots.getD p dummy)

theorem getD_eq (p : Nat) (bound : p < roots.length) : roots[p]? = some (roots.getD p dummy) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem bound]
  rfl

theorem decision_key (p q : Nat) (hp : p < roots.length) (hq : q < roots.length)
    (d : OccurrenceComparison)
    (computed : compareAuthoritativeRule6InitialPositions? mol state fuel roots p q = some d) :
    compareFailClosedOccurrenceBranchProjectedKeys (keyAt mol state fuel roots p)
      (keyAt mol state fuel roots q) = d.ordering := by
  unfold compareAuthoritativeRule6InitialPositions? at computed
  rw [getD_eq roots p hp, getD_eq roots q hq] at computed
  simp only [Option.bind_eq_bind, Option.bind_some] at computed
  exact compareOccurrenceBranchesUnrestricted_ordering_success_factors mol state fuel _ _ d computed

theorem adjacent_decision : ∀ (sorted : List Nat) (adjacent : List (Option Ordering)),
    compareAuthoritativeRule6InitialAdjacent? mol state fuel roots sorted = some adjacent →
    ∀ k (hk : k + 1 < sorted.length), ∃ d,
      compareAuthoritativeRule6InitialPositions? mol state fuel roots sorted[k] sorted[k + 1] =
        some d ∧ adjacent[k]? = some (some d.ordering)
  | [], _, _, k, hk => by simp at hk
  | [_], _, _, k, hk => by simp at hk
  | p :: q :: rest, adjacent, computed, k, hk => by
      simp only [compareAuthoritativeRule6InitialAdjacent?, Option.bind_eq_bind,
        Option.bind_eq_some_iff, Option.some.injEq] at computed
      obtain ⟨d, dEq, deeper, deeperEq, rfl⟩ := computed
      cases k with
      | zero => exact ⟨d, dEq, rfl⟩
      | succ k =>
          obtain ⟨d', d'Eq, idx⟩ := adjacent_decision (q :: rest) deeper deeperEq k (by simpa using hk)
          exact ⟨d', d'Eq, by simpa using idx⟩

theorem consistent_entry (adjacent : List (Option Ordering)) (cons : consistent adjacent = true)
    (k : Nat) (d : Option Ordering) (idx : adjacent[k]? = some d) :
    d = some Ordering.gt ∨ d = some Ordering.eq := by
  unfold consistent at cons
  have member : d ∈ adjacent := List.mem_of_getElem? idx
  have := List.all_eq_true.mp cons d member
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  exact this

/-- Keys never increase along the actual consistent adjacent chain. -/
theorem chain_isLE (sorted : List Nat) (adjacent : List (Option Ordering))
    (computed : compareAuthoritativeRule6InitialAdjacent? mol state fuel roots sorted = some adjacent)
    (cons : consistent adjacent = true) (inRange : ∀ p ∈ sorted, p < roots.length) :
    ∀ k l, (hkl : k ≤ l) → (hl : l < sorted.length) →
      (compareFailClosedOccurrenceBranchProjectedKeys
        (keyAt mol state fuel roots sorted[l])
        (keyAt mol state fuel roots sorted[k])).isLE = true := by
  letI := compareFailClosedOccurrenceBranchProjectedKeys_transCmp
  intro k l le
  induction l, le using Nat.le_induction with
  | base =>
      intro hl
      rw [orientedCmp_refl compareFailClosedOccurrenceBranchProjectedKeys]
      rfl
  | succ l _ ih =>
      intro hl
      have hl' : l < sorted.length := Nat.lt_of_succ_lt hl
      obtain ⟨d, dEq, idx⟩ := adjacent_decision mol state fuel roots sorted adjacent computed l hl
      have keyEq := decision_key mol state fuel roots sorted[l] sorted[l + 1]
        (inRange _ (List.getElem_mem hl')) (inRange _ (List.getElem_mem hl)) d dEq
      have step : (compareFailClosedOccurrenceBranchProjectedKeys
          (keyAt mol state fuel roots sorted[l + 1]) (keyAt mol state fuel roots sorted[l])).isLE = true := by
        rw [Std.OrientedCmp.eq_swap (cmp := compareFailClosedOccurrenceBranchProjectedKeys), keyEq]
        rcases consistent_entry adjacent cons l _ idx with gt | eq
        · simp only [Option.some.injEq] at gt
          rw [gt]; rfl
        · simp only [Option.some.injEq] at eq
          rw [eq]; rfl
      exact Std.TransCmp.isLE_trans step (ih hl')

/-- A strict decision inside the chain makes the endpoints strictly ordered. -/
theorem chain_lt_of_gt (sorted : List Nat) (adjacent : List (Option Ordering))
    (computed : compareAuthoritativeRule6InitialAdjacent? mol state fuel roots sorted = some adjacent)
    (cons : consistent adjacent = true) (inRange : ∀ p ∈ sorted, p < roots.length)
    (k m l : Nat) (km : k ≤ m) (ml : m + 1 ≤ l) (hl : l < sorted.length)
    (gt : adjacent[m]? = some (some Ordering.gt)) :
    compareFailClosedOccurrenceBranchProjectedKeys
      (keyAt mol state fuel roots sorted[l]) (keyAt mol state fuel roots sorted[k]) = .lt := by
  letI := compareFailClosedOccurrenceBranchProjectedKeys_transCmp
  have hm1 : m + 1 < sorted.length := Nat.lt_of_le_of_lt ml hl
  have hm : m < sorted.length := Nat.lt_of_succ_lt hm1
  obtain ⟨d, dEq, idx⟩ := adjacent_decision mol state fuel roots sorted adjacent computed m hm1
  rw [idx] at gt
  simp only [Option.some.injEq] at gt
  have keyEq := decision_key mol state fuel roots sorted[m] sorted[m + 1]
    (inRange _ (List.getElem_mem hm)) (inRange _ (List.getElem_mem hm1)) d dEq
  have stepLt : compareFailClosedOccurrenceBranchProjectedKeys
      (keyAt mol state fuel roots sorted[m + 1]) (keyAt mol state fuel roots sorted[m]) = .lt := by
    rw [Std.OrientedCmp.eq_swap (cmp := compareFailClosedOccurrenceBranchProjectedKeys), keyEq, gt]
    rfl
  have upper := chain_isLE mol state fuel roots sorted adjacent computed cons inRange (m + 1) l ml hl
  have lower := chain_isLE mol state fuel roots sorted adjacent computed cons inRange k m km hm
  have mid := Std.TransCmp.lt_of_lt_of_isLE stepLt lower
  exact Std.TransCmp.lt_of_isLE_of_lt upper mid

end Chain

/-! ## Twin eligibility and non-strictness from the actual ordinary partition -/

section Ordinary

variable {mol : RawMolecule} {target : Node} {left right : Cursor}
  (tc : TwinCenter mol target left right) (wellFormed : mol.WellFormed) (single : SingleBonded mol)
  (unique : mol.BondRecordsUnique) (reached : Reached mol target)
  (roots : List Cursor) (frame : occurrenceLigandFrame? mol target = some roots)
  (sorted : List Nat) (adjacent : List (Option Ordering))
  (ord : LocalizedMarkedUncappedOperations.ordinary? mol [] target = some (sorted, adjacent))
  (cons : consistent adjacent = true)

include frame ord in
theorem ordinary_parts :
    sortAuthoritativeRule6InitialPositions? mol [] (comparisonFuel mol) roots
        (List.range roots.length) = some sorted ∧
      compareAuthoritativeRule6InitialAdjacent? mol [] (comparisonFuel mol) roots sorted =
        some adjacent := by
  unfold LocalizedMarkedUncappedOperations.ordinary? at ord
  rw [frame] at ord
  simp only [Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.mk.injEq] at ord
  obtain ⟨s, sEq, a, aEq, rfl, rfl⟩ := ord
  exact ⟨sEq, aEq⟩

include frame ord in
theorem sorted_perm : sorted.Perm (List.range roots.length) :=
  sortAuthoritativeRule6InitialPositions?_perm mol [] _ roots _ sorted (ordinary_parts roots frame sorted adjacent ord).1

include frame ord in
theorem sorted_inRange : ∀ p ∈ sorted, p < roots.length := by
  intro p member
  exact List.mem_range.mp ((sorted_perm roots frame sorted adjacent ord).mem_iff.mp member)

include frame ord in
theorem adjacent_length : adjacent.length = sorted.length - 1 :=
  compareAuthoritativeRule6InitialAdjacent?_length mol [] _ roots sorted adjacent
    (ordinary_parts roots frame sorted adjacent ord).2

include tc wellFormed single unique reached in
/-- The twins' ordinary keys tie. -/
theorem twin_keys_tie (i j : Nat) (hi : roots[i]? = some left) (hj : roots[j]? = some right) :
    compareFailClosedOccurrenceBranchProjectedKeys (keyAt mol [] (comparisonFuel mol) roots i)
      (keyAt mol [] (comparisonFuel mol) roots j) = .eq := by
  have lt := tc.leftTerminalCursor wellFormed single unique reached
  have rt := tc.rightTerminalCursor wellFormed single unique reached
  have tie := ordinary_tie mol [] (comparisonFuel mol) left right lt rt tc.leftReal tc.rightReal
    tc.sameZ tc.sameDepth tc.sameMass rfl rfl
  have factored := compareOccurrenceBranchesUnrestricted_ordering_success_factors mol []
    (comparisonFuel mol) left right _ tie
  have hi' : roots.getD i dummy = left := by
    rw [List.getD_eq_getElem?_getD, hi]; rfl
  have hj' : roots.getD j dummy = right := by
    rw [List.getD_eq_getElem?_getD, hj]; rfl
  unfold keyAt
  rw [hi', hj']
  exact factored

include tc wellFormed single unique reached frame ord cons in
/-- Both twins are eligible references and the ordinary order is not strict. -/
theorem twins_eligible_not_strict (i j : Nat) (hi : roots[i]? = some left) (hj : roots[j]? = some right) :
    i ∈ tiedPositions false sorted adjacent ∧ j ∈ tiedPositions false sorted adjacent ∧
      strict adjacent = false := by
  letI := compareFailClosedOccurrenceBranchProjectedKeys_transCmp
  have parts := ordinary_parts roots frame sorted adjacent ord
  have inRange := sorted_inRange roots frame sorted adjacent ord
  have perm := sorted_perm roots frame sorted adjacent ord
  have tie := twin_keys_tie tc wellFormed single unique reached roots i j hi hj
  have ij : i ≠ j := by
    intro same
    rw [same, hj] at hi
    exact tc.cursor_ne (Option.some.inj hi).symm
  have iLt : i < roots.length := by
    obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp hi
    exact bound
  have jLt : j < roots.length := by
    obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp hj
    exact bound
  have iMem : i ∈ sorted := perm.mem_iff.mpr (List.mem_range.mpr iLt)
  have jMem : j ∈ sorted := perm.mem_iff.mpr (List.mem_range.mpr jLt)
  obtain ⟨u, hu, iEq⟩ := List.mem_iff_getElem.mp iMem
  obtain ⟨v, hv, jEq⟩ := List.mem_iff_getElem.mp jMem
  have uv : u ≠ v := by
    intro same
    subst same
    exact ij (iEq.symm.trans jEq)
  have adjLen := adjacent_length roots frame sorted adjacent ord
  -- every decision between the two twin positions is a tie
  have between : ∀ a b, (hab : a < b) → (hb : b < sorted.length) →
      compareFailClosedOccurrenceBranchProjectedKeys
        (keyAt mol [] (comparisonFuel mol) roots sorted[a])
        (keyAt mol [] (comparisonFuel mol) roots sorted[b]) = .eq →
      ∀ m, a ≤ m → m < b → adjacent[m]? = some (some Ordering.eq) := by
    intro a b ab hb tieAB m am mb
    have hm : m < adjacent.length := by omega
    obtain ⟨d, dIdx⟩ : ∃ d, adjacent[m]? = some d := ⟨adjacent[m], List.getElem?_eq_getElem hm⟩
    rcases consistent_entry adjacent cons m d dIdx with gt | eq
    · exfalso
      rw [gt] at dIdx
      have lt := chain_lt_of_gt mol [] (comparisonFuel mol) roots sorted adjacent parts.2 cons inRange
        a m b am (Nat.succ_le_of_lt mb) hb dIdx
      rw [Std.OrientedCmp.eq_swap (cmp := compareFailClosedOccurrenceBranchProjectedKeys), tieAB] at lt
      cases lt
    · rw [eq] at dIdx
      exact dIdx
  rcases Nat.lt_or_gt_of_ne uv with lt | gt
  · have tieUV : compareFailClosedOccurrenceBranchProjectedKeys
        (keyAt mol [] (comparisonFuel mol) roots sorted[u]) (keyAt mol [] (comparisonFuel mol) roots sorted[v]) = .eq := by
      rw [iEq, jEq]; exact tie
    have first := between u v lt hv tieUV u (Nat.le_refl u) lt
    have last := between u v lt hv tieUV (v - 1) (by omega) (by omega)
    have vEq : v - 1 + 1 = v := by omega
    refine ⟨?_, ?_, ?_⟩
    · rw [← iEq]
      exact mem_tied_of_next false sorted adjacent u (by omega) first
    · rw [← jEq]
      have := mem_tied_of_prev false sorted adjacent (v - 1) (by omega) last
      simpa [vEq] using this
    · unfold strict
      by_contra allGt
      have allGt' := List.all_eq_true.mp (Bool.eq_true_of_not_eq_false allGt) _ (List.mem_of_getElem? first)
      simp at allGt'
  · have tieVU : compareFailClosedOccurrenceBranchProjectedKeys
        (keyAt mol [] (comparisonFuel mol) roots sorted[v]) (keyAt mol [] (comparisonFuel mol) roots sorted[u]) = .eq := by
      rw [iEq, jEq, Std.OrientedCmp.eq_swap (cmp := compareFailClosedOccurrenceBranchProjectedKeys), tie]
      rfl
    have first := between v u gt hu tieVU v (Nat.le_refl v) gt
    have last := between v u gt hu tieVU (u - 1) (by omega) (by omega)
    have uEq : u - 1 + 1 = u := by omega
    refine ⟨?_, ?_, ?_⟩
    · rw [← iEq]
      have := mem_tied_of_prev false sorted adjacent (u - 1) (by omega) last
      simpa [uEq] using this
    · rw [← jEq]
      exact mem_tied_of_next false sorted adjacent v (by omega) first
    · unfold strict
      by_contra allGt
      have allGt' := List.all_eq_true.mp (Bool.eq_true_of_not_eq_false allGt) _ (List.mem_of_getElem? first)
      simp at allGt'

end Ordinary

/-! ## The generated snapshot at a twin leaf is empty -/

theorem facts_twin_nil {mol : RawMolecule} {target : Node} {left right : Cursor}
    (tc : TwinCenter mol target left right) (wellFormed : mol.WellFormed) (single : SingleBonded mol)
    (unique : mol.BondRecordsUnique) (reached : Reached mol target) (ops : Operations)
    (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState) (ctx : Option Nat) (twin : Node)
    (which : twin = left.node ∨ twin = right.node) :
    facts mol ops depth geom state ctx twin = [] := by
  have child : twin ∈ mol.canonicalChildren target := by
    rcases which with rfl | rfl
    · exact tc.leftChild
    · exact tc.rightChild
  have terminal : TerminalNeighbor mol target.atom twin.atom := by
    rcases which with rfl | rfl
    · exact tc.leftTerminal
    · exact tc.rightTerminal
  have twinReached := reached_child mol target twin reached child
  have noFrame := terminal_no_frame mol wellFormed single unique twin twinReached target.atom terminal
  have noChildren := terminal_children_nil mol wellFormed single unique target twin child terminal
  cases depth with
  | zero => rfl
  | succ depth =>
      rw [facts_succ]
      unfold descriptor?
      rw [descriptor_none_of_frame mol ops geom state ctx twin (facts mol ops depth) noFrame,
        noChildren]
      rfl

/-! ## Readings at the center -/

section Center

variable {mol : RawMolecule} {target : Node} {left right : Cursor}
  (tc : TwinCenter mol target left right) (wellFormed : mol.WellFormed) (single : SingleBonded mol)
  (unique : mol.BondRecordsUnique) (reached : Reached mol target) (depth : Nat) (geom : Geometry)

/-- The actual temporary extension under a reference. -/
abbrev under (r : Nat) : OccurrenceAuxState :=
  underWith mol (operations mol) geom [] target (facts mol (operations mol) depth) r

/-- The reading evaluated by the consensus branch for one reference. -/
abbrev evaluate (r : Nat) : Option RS :=
  (appendFacts? [] (under (mol := mol) (target := target) depth geom r)).bind fun temp =>
    markedReading? mol (operations mol) geom temp target r

include tc wellFormed single unique reached in
/-- A non-twin reference, carried or eligible, leaves the twins tied and refuses. -/
theorem evaluate_nonTwin_none (r : Nat) (notLeft : r ≠ left.node.atom)
    (notRight : r ≠ right.node.atom) :
    evaluate (mol := mol) (target := target) depth geom r = none := by
  have extension := LocalizedMarkedGeneratedFactUniqueness.generated_extension_succeeds mol
    (operations mol) wellFormed single unique depth geom target r
  have compared := generated_promoted_bits mol (operations mol) wellFormed single unique depth
    (comparisonFuel mol) geom [] target target reached reached r left right tc.leftSlot tc.rightSlot
    tc.leftTerminal tc.rightTerminal tc.leftReal tc.rightReal tc.sameZ tc.sameDepth tc.sameMass
  have tied : (promotionBitsDecision r left.node.atom right.node.atom).ordering = .eq := by
    simp [promotionBitsDecision, Ne.symm notLeft, Ne.symm notRight]
  simp only [evaluate, under, extension, Option.bind_some]
  exact LocalizedMarkedTerminalMarkedRefusal.markedReading_none_of_slot_tie mol geom _ target r
    left right tc.leftSlot tc.rightSlot tc.cursor_ne _ compared tied

include tc wellFormed single unique reached in
/-- Under a twin reference whose tied children are only the twin leaves, the snapshot is empty. -/
theorem under_twin_nil (eligible : List Nat) (onlyTwins : ∀ a ∈ eligible, a = left.node.atom ∨ a = right.node.atom)
    (tiedEq : tiedChildren mol (operations mol) [] target =
      (mol.canonicalChildren target).filter fun child => eligible.contains child.atom) (r : Nat) :
    under (mol := mol) (target := target) depth geom r = [] := by
  unfold under underWith
  rw [tiedEq]
  apply List.flatMap_eq_nil_iff.mpr
  intro child member
  obtain ⟨childMem, inEligible⟩ := List.mem_filter.mp member
  have atomIn : child.atom ∈ eligible := List.contains_iff_mem.mp inEligible
  have nodup := LocalizedMarkedGeneratedFactUniqueness.child_atoms_nodup mol wellFormed single
    unique target
  have injective := List.inj_on_of_nodup_map nodup
  rcases onlyTwins child.atom atomIn with isLeft | isRight
  · exact facts_twin_nil tc wellFormed single unique reached (operations mol) depth geom [] (some r)
      child (Or.inl (injective childMem tc.leftChild isLeft))
  · exact facts_twin_nil tc wellFormed single unique reached (operations mol) depth geom [] (some r)
      child (Or.inr (injective childMem tc.rightChild isRight))

include tc wellFormed single unique reached in
/-- With empty snapshots, successful own-twin readings are complements. -/
theorem twin_readings_complement (roots : List Cursor)
    (frame : occurrenceLigandFrame? mol target = some roots) (ℓ₁ ℓ₂ : RS)
    (read₁ : markedReading? mol (operations mol) geom [] target left.node.atom = some ℓ₁)
    (read₂ : markedReading? mol (operations mol) geom [] target right.node.atom = some ℓ₂) :
    ℓ₂ = ℓ₁.swap := by
  obtain ⟨atomsNodup, nodup⟩ := frame_nodup mol wellFormed single unique target reached roots frame
  have leftMem := LocalizedMarkedTerminalMarkedRefusal.physical_slots_mem_frame mol target roots
    frame left tc.leftSlot
  have rightMem := LocalizedMarkedTerminalMarkedRefusal.physical_slots_mem_frame mol target roots
    frame right tc.rightSlot
  exact readings_complement mol geom target roots frame nodup atomsNodup left right
    (roots.idxOf left) (roots.idxOf right) (List.getElem?_idxOf leftMem) (List.getElem?_idxOf rightMem)
    tc.cursor_ne (tc.symmetry wellFormed single unique reached roots frame (comparisonFuel mol))
    ℓ₁ ℓ₂ read₁ read₂

end Center

/-! ## Main refusal theorems -/

section Main

variable {mol : RawMolecule} {target : Node} {left right : Cursor}
  (tc : TwinCenter mol target left right) (wellFormed : mol.WellFormed) (single : SingleBonded mol)
  (unique : mol.BondRecordsUnique) (reached : Reached mol target) (depth : Nat) (geom : Geometry)

include tc wellFormed single unique reached in
/-- **Own-reference cancellation and carried-reference tie.** For every geometry and every
context that does not promote a twin itself, the actual recursive step at an outward
terminal-twin center refuses. -/
theorem rawWith_none (ctx : Option Nat)
    (notTwin : ∀ r, ctx = some r → r ≠ left.node.atom ∧ r ≠ right.node.atom) :
    rawWith? mol (operations mol) geom [] ctx target (facts mol (operations mol) depth) = none := by
  unfold rawWith? rawStep?
  cases frame : occurrenceLigandFrame? mol target with
  | none => simp [LocalizedGenericMarkedRecalculation.frameAtoms?, frame]
  | some roots =>
  have frameAtoms : LocalizedGenericMarkedRecalculation.frameAtoms? mol target =
      some (frameAtomsOf roots) := by
    simp [LocalizedGenericMarkedRecalculation.frameAtoms?, frame]
  rw [frameAtoms]
  cases ord : (operations mol).ordinary [] target with
  | none => rfl
  | some pair =>
  obtain ⟨sorted, adjacent⟩ := pair
  have ord' : LocalizedMarkedUncappedOperations.ordinary? mol [] target = some (sorted, adjacent) := ord
  simp only [Option.bind_eq_bind, Option.bind_some]
  by_cases bad : ¬ (frameAtomsOf roots).Nodup ∨ consistent adjacent = false
  · simp [bad]
  simp only [bad, ↓reduceIte]
  have cons : consistent adjacent = true := by
    cases h : consistent adjacent with
    | true => rfl
    | false => exact absurd (Or.inr h) bad
  have leftMem := LocalizedMarkedTerminalMarkedRefusal.physical_slots_mem_frame mol target roots
    frame left tc.leftSlot
  have rightMem := LocalizedMarkedTerminalMarkedRefusal.physical_slots_mem_frame mol target roots
    frame right tc.rightSlot
  obtain ⟨iTied, jTied, notStrict⟩ := twins_eligible_not_strict tc wellFormed single unique reached
    roots frame sorted adjacent ord' cons (roots.idxOf left) (roots.idxOf right)
    (List.getElem?_idxOf leftMem) (List.getElem?_idxOf rightMem)
  simp only [notStrict, Bool.false_eq_true, ↓reduceIte]
  -- the generated eligible references contain both twins
  have leftAtom : (frameAtomsOf roots)[roots.idxOf left]? = some left.node.atom := by
    rw [frameAtoms_getElem?, List.getElem?_idxOf leftMem]; rfl
  have rightAtom : (frameAtomsOf roots)[roots.idxOf right]? = some right.node.atom := by
    rw [frameAtoms_getElem?, List.getElem?_idxOf rightMem]; rfl
  have leftEligible : left.node.atom ∈ eligibleOf (frameAtomsOf roots) sorted adjacent :=
    List.mem_filterMap.mpr ⟨_, iTied, leftAtom⟩
  have rightEligible : right.node.atom ∈ eligibleOf (frameAtomsOf roots) sorted adjacent :=
    List.mem_filterMap.mpr ⟨_, jTied, rightAtom⟩
  -- consensus over the generated references refuses
  have consensusNone : consensus ((eligibleOf (frameAtomsOf roots) sorted adjacent).map
      fun r => evaluate (mol := mol) (target := target) depth geom r) = none := by
    by_cases other : ∃ r ∈ eligibleOf (frameAtomsOf roots) sorted adjacent,
        r ≠ left.node.atom ∧ r ≠ right.node.atom
    · obtain ⟨r, rMem, notLeft, notRight⟩ := other
      apply consensus_none_of_mem_none
      rw [List.mem_map]
      exact ⟨r, rMem, evaluate_nonTwin_none tc wellFormed single unique reached depth geom r notLeft
        notRight⟩
    · have onlyTwins : ∀ a ∈ eligibleOf (frameAtomsOf roots) sorted adjacent,
          a = left.node.atom ∨ a = right.node.atom := by
        intro a aMem
        by_contra neither
        exact other ⟨a, aMem, fun h => neither (Or.inl h), fun h => neither (Or.inr h)⟩
      have tiedEq : tiedChildren mol (operations mol) [] target =
          (mol.canonicalChildren target).filter fun child =>
            (eligibleOf (frameAtomsOf roots) sorted adjacent).contains child.atom := by
        unfold tiedChildren
        rw [frameAtoms, ord]
      have emptyL := under_twin_nil tc wellFormed single unique reached depth geom _ onlyTwins tiedEq
        left.node.atom
      have emptyR := under_twin_nil tc wellFormed single unique reached depth geom _ onlyTwins tiedEq
        right.node.atom
      have evalL : evaluate (mol := mol) (target := target) depth geom left.node.atom =
          markedReading? mol (operations mol) geom [] target left.node.atom := by
        simp only [evaluate]
        rw [emptyL]
        rfl
      have evalR : evaluate (mol := mol) (target := target) depth geom right.node.atom =
          markedReading? mol (operations mol) geom [] target right.node.atom := by
        simp only [evaluate]
        rw [emptyR]
        rfl
      have memL : evaluate (mol := mol) (target := target) depth geom left.node.atom ∈
          (eligibleOf (frameAtomsOf roots) sorted adjacent).map
            fun r => evaluate (mol := mol) (target := target) depth geom r :=
        List.mem_map.mpr ⟨_, leftEligible, rfl⟩
      have memR : evaluate (mol := mol) (target := target) depth geom right.node.atom ∈
          (eligibleOf (frameAtomsOf roots) sorted adjacent).map
            fun r => evaluate (mol := mol) (target := target) depth geom r :=
        List.mem_map.mpr ⟨_, rightEligible, rfl⟩
      cases readL : markedReading? mol (operations mol) geom [] target left.node.atom with
      | none =>
          apply consensus_none_of_mem_none
          rw [← readL, ← evalL]
          exact memL
      | some ℓ₁ =>
      cases readR : markedReading? mol (operations mol) geom [] target right.node.atom with
      | none =>
          apply consensus_none_of_mem_none
          rw [← readR, ← evalR]
          exact memR
      | some ℓ₂ =>
          have complement := twin_readings_complement tc wellFormed single unique reached geom
            roots frame ℓ₁ ℓ₂ readL readR
          apply consensus_none_of_two _ _ _ memL memR
          rw [evalL, evalR, readL, readR, complement]
          intro same
          have := Option.some.inj same
          cases ℓ₁ <;> cases this
  cases ctx with
  | none => exact consensusNone
  | some r =>
      by_cases inFrame : r ∈ frameAtomsOf roots
      · have := notTwin r rfl
        simp only [List.contains_iff_mem, inFrame, ↓reduceIte]
        exact evaluate_nonTwin_none tc wellFormed single unique reached depth geom r this.1 this.2
      · simp only [List.contains_iff_mem, inFrame, ↓reduceIte]
        exact consensusNone

include tc wellFormed single unique reached in
/-- The mirror-cased descriptor refuses as well: both raw runs refuse for every geometry. -/
theorem descriptor_none (ctx : Option Nat)
    (notTwin : ∀ r, ctx = some r → r ≠ left.node.atom ∧ r ≠ right.node.atom) :
    descriptor? mol (operations mol) depth geom [] ctx target = none := by
  unfold descriptor? descriptorWith?
  rw [rawWith_none tc wellFormed single unique reached depth geom ctx notTwin]
  rfl

end Main

/-! ## The center's own assignment refuses -/

/-- **Terminal-twin centers receive no descriptor from the uncapped recursion.** -/
theorem assignCenter_none (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (single : SingleBonded mol) (unique : mol.BondRecordsUnique) (center : Nat)
    (valid : center < mol.atomCount) (left right : Cursor)
    (tc : TwinCenter mol (canonicalCenterRoot center) left right) (geom : Geometry) :
    LocalizedMarkedUncappedEvaluator.assignCenter? mol geom center = none := by
  unfold LocalizedMarkedUncappedEvaluator.assignCenter? LocalizedMarkedOperationEvaluator.assignCenter?
  exact descriptor_none tc wellFormed single unique (reached_root mol center valid) _ geom none
    (fun _ h => by cases h)

/-! ## No generated snapshot carries a fact at such a center -/

theorem generated_eq_of_key {mol : RawMolecule} {root root' : Nat} {n n' : Node}
    (gen : CanonicalCenterTreeNode mol root n) (gen' : CanonicalCenterTreeNode mol root' n')
    (keys : canonicalOccurrenceKey n = canonicalOccurrenceKey n') : n = n' := by
  have history : n.history = n'.history := congrArg CanonicalOccurrenceKey.history keys
  have provenance : n.provenance = n'.provenance := congrArg CanonicalOccurrenceKey.provenance keys
  have atom : n.atom = n'.atom := by
    have h := gen.history_head
    have h' := gen'.history_head
    rw [history] at h
    exact Option.some.inj (h.symm.trans h')
  have parent : n.parent = n'.parent := by
    cases gen with
    | root =>
        cases gen' with
        | root =>
            simp [canonicalCenterRoot] at history
            simp [canonicalCenterRoot, history]
        | child pg member =>
            have := mol.canonicalChildren_history _ _ member
            rw [this] at history
            simp [canonicalCenterRoot] at history
            have pHead := pg.history_head
            rw [history.2] at pHead
            simp at pHead
    | child pg member =>
        cases gen' with
        | root =>
            have := mol.canonicalChildren_history _ _ member
            rw [this] at history
            simp [canonicalCenterRoot] at history
            have pHead := pg.history_head
            rw [history.2] at pHead
            simp at pHead
        | child pg' member' =>
            rw [child_parent mol _ _ member, child_parent mol _ _ member']
            have h := mol.canonicalChildren_history _ _ member
            have h' := mol.canonicalChildren_history _ _ member'
            rw [h, h'] at history
            simp only [List.cons.injEq] at history
            have pHead := pg.history_head
            have pHead' := pg'.history_head
            rw [history.2] at pHead
            exact Option.some.inj (pHead.symm.trans pHead')
  cases n
  cases n'
  simp only at atom parent history provenance
  simp [atom, parent, history, provenance]

/-- Every fact passed upward is the actual mirror-cased descriptor at some real descendant,
evaluated under the carried reference at the depth remaining there. -/
theorem snapshot_fact_source (mol : RawMolecule) (ops : Operations) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) :
    ∀ depth source fact, fact ∈ facts mol ops depth geom state ctx source →
      ∃ target descriptor remaining, Descends mol source target ∧
        descriptorWith? mol ops geom state ctx target (facts mol ops remaining) = some descriptor ∧
        fact = factOf target descriptor
  | 0, source, fact, member => by simp [facts] at member
  | depth + 1, source, fact, member => by
      rw [facts_succ] at member
      rcases List.mem_append.mp member with own | deeper
      · obtain ⟨descriptor, present, rfl⟩ := List.mem_map.mp own
        exact ⟨source, descriptor, depth, .refl, Option.mem_toList.mp present, rfl⟩
      · obtain ⟨child, edge, member⟩ := List.mem_flatMap.mp deeper
        obtain ⟨target, descriptor, remaining, path, value, fact⟩ :=
          snapshot_fact_source mol ops geom state ctx depth child fact member
        exact ⟨target, descriptor, remaining, (Relation.ReflTransGen.single edge).trans path, value,
          fact⟩

/-- **No generated promotion snapshot carries a fact at an outward terminal-twin center.** The
snapshot is the actual one passed upward from a framed occurrence `A` under a reference selected
in `A`'s own frame; the lookup is the actual occurrence-key lookup. -/
theorem snapshot_factAt_twinCenter_none (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (single : SingleBonded mol) (unique : mol.BondRecordsUnique) (depth : Nat) (geom : Geometry)
    (A : Node) (reachedA : Reached mol A) (atomsA : List Nat)
    (frameA : LocalizedGenericMarkedRecalculation.frameAtoms? mol A = some atomsA)
    (mark : Nat) (selected : mark ∈ atomsA) (target : Node) (reached : Reached mol target)
    (left right : Cursor) (tc : TwinCenter mol target left right) :
    (underWith mol (operations mol) geom [] A (facts mol (operations mol) depth) mark).factAt?
      target = none := by
  unfold OccurrenceAuxState.factAt?
  apply List.find?_eq_none.mpr
  intro fact member keyMatch
  have keys : fact.key = canonicalOccurrenceKey target := by simpa using keyMatch
  obtain ⟨child, childEdge, member⟩ := List.mem_flatMap.mp member
  have childMem := mem_tiedChildren_actual mol (operations mol) [] A child childEdge
  obtain ⟨target', descriptor, remaining, path, value, factEq⟩ :=
    snapshot_fact_source mol (operations mol) geom [] (some mark) depth child fact member
  have target'Reached : Reached mol target' :=
    descendant_reached (reached_child mol A child reachedA childMem) path
  obtain ⟨root', valid', path'⟩ := target'Reached
  obtain ⟨root, valid, pathT⟩ := reached
  have gen' := generated_of_reachedFrom mol root' target' path'
  have gen := generated_of_reachedFrom mol root target pathT
  have keys' : canonicalOccurrenceKey target' = canonicalOccurrenceKey target := by
    rw [factEq, LocalizedMarkedGeneratedFactUniqueness.factOf_key] at keys
    exact keys
  have same : target' = target := generated_eq_of_key gen' gen keys'
  subst same
  -- the carried reference is not one of the twins
  have real : target'.forcedLeaf = false := by
    cases leaf : target'.forcedLeaf with
    | false => rfl
    | true =>
        have child := tc.leftChild
        rw [LocalizedGenericMarkedRecalculation.canonicalChildren_forcedLeaf mol target' leaf] at child
        simp at child
  have exclude := carried_not_terminal mol wellFormed single A target' reachedA
    ⟨child, childMem, path⟩ real atomsA frameA mark selected
  have notLeft : mark ≠ left.node.atom := fun h => exclude (h ▸ tc.leftTerminal)
  have notRight : mark ≠ right.node.atom := fun h => exclude (h ▸ tc.rightTerminal)
  have refused := descriptor_none tc wellFormed single unique ⟨root, valid, pathT⟩ remaining geom
    (some mark) (fun r h => by cases h; exact ⟨notLeft, notRight⟩)
  unfold descriptor? at refused
  rw [refused] at value
  cases value

end TetraStereo.OneCenter.LocalizedMarkedTerminalGaugeRefusal

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalGaugeRefusal.twins_eligible_not_strict
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalGaugeRefusal.facts_twin_nil
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalGaugeRefusal.evaluate_nonTwin_none
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalGaugeRefusal.twin_readings_complement
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalGaugeRefusal.rawWith_none
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalGaugeRefusal.descriptor_none
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalGaugeRefusal.assignCenter_none
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalGaugeRefusal.snapshot_fact_source
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalGaugeRefusal.snapshot_factAt_twinCenter_none
