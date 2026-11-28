import TetraStereo.Engine.RingEqualPathHandCounts

/-! Uppercase donor counts grouped by parent occurrence at a selected sphere. -/
set_option autoImplicit false

namespace TetraStereo.Engine.RingParentHandCounts
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader Frame)
open RingActivePairReport (Slot)
open RingGroupedCentre (cursor)
open RingGeometryExchange (Carrier Frozen)
open RingResidualPairDecision (Table TableExact classify)

private def layer {i : Input} {α : Type} (observe : Arm i → α) : Nat → Arm i → List α
  | 0,q => [observe q]
  | d+1,q => (i.certified.executableLocalizedRerootChildren q).flatMap (layer observe d)

private theorem layer_perm {i j : Input} {α : Type} (c : Carrier i j)
    (l : Arm i → α) (r : Arm j → α) (agree : ∀ q, c.domain q → l q = r (c.image q))
    (d : Nat) (q : Arm i) (on : c.domain q) :
    (layer l d q).Perm (layer r d (c.image q)) := by
  induction d generalizing q with
  | zero => simp [layer,agree q on]
  | succ d ih =>
    have perm := (c.children q on).flatMap_right (layer r d)
    rw [List.flatMap_map] at perm
    apply List.Perm.trans _ perm
    apply List.Perm.flatMap_left
    intro t ht
    exact ih t (c.below q on t ht)

/-- At each parent at depth p, count donors of the requested uppercase hand
exactly t more edges away. Zero counts retain the parent in the inventory. -/
def counts {i : Input} (r : Reader i) (rev : Bool) (h : RS) (p t : Nat) (q : Arm i) : List Nat :=
  layer (fun u => (layer (RingFullPathPairs.handAt i r rev) t u).count (some h)) p q

theorem transport {i j : Input} {l : Reader i} {r : Reader j} (c : Carrier i j)
    (frozen : Frozen c l r) (rev : Bool) (h : RS) (p t : Nat) (q : Arm i) (on : c.domain q) :
    (counts l rev h p t q).Perm (counts r rev h p t (c.image q)) := by
  apply layer_perm c _ _ _ p q on
  intro u hu
  apply List.Perm.count_eq
  exact layer_perm c _ _ (fun v hv => by simp [RingFullPathPairs.handAt,frozen v hv]) t u hu

/-- A discrepancy in the distribution excludes a frozen exchange even when
the total donor count agrees. -/
theorem excludes {i : Input} {f : Site i} {fr : Frame i f} {r : Reader i} {a b : Slot}
    {rev : Bool} {h : RS} {p t : Nat}
    (different : ¬ (counts r rev h p t (cursor fr a)).Perm (counts r rev h p t (cursor fr b))) :
    ¬ Nonempty (RingObservedTreeMatch.Unmarked fr r a b) := by
  rintro ⟨e⟩
  exact different (e.target ▸ transport e.carrier e.frozen rev h p t _ e.start)

open RingEqualPathHandCounts (Population ordinary_entry verdict stepVerdict)

/-- With equal hand populations, an unequal per-parent distribution certifies
a complete ordinary comparison tie with no exchange on the frozen reader. -/
theorem ordinary_noExchangeTie {i : Input} {f : Site i} (fr : Frame i f) {r : Reader i}
    (ready : RingGroupedStereo.Ready f r) (c : Carrier i i)
    (same : Frozen c (RingSplitLigandTie.markingReader r) (RingSplitLigandTie.markingReader r))
    (a b : Slot) (on : c.domain (cursor fr a)) (image : c.image (cursor fr a) = cursor fr b)
    {rev : Bool} {nr ns : Nat} (left : Population i r rev (cursor fr a) nr ns)
    (right : Population i r rev (cursor fr b) nr ns) {table : Table}
    (exactTable : TableExact fr r rev none table) {h : RS} {p t : Nat}
    (different : ¬ (counts r rev h p t (cursor fr a)).Perm (counts r rev h p t (cursor fr b))) :
    classify fr r none a b table[a.val][b.val] = .noExchangeTie := by
  apply (RingResidualPairDecision.classify_iff fr ready exactTable a b _).mpr
  constructor
  · simpa [verdict,stepVerdict,RingResidualPairDecision.Classification.verdict] using
      ordinary_entry fr ready c same a b on image left right exactTable
  · exact ⟨fun present => (excludes different present).elim, fun no => by cases no⟩

end TetraStereo.Engine.RingParentHandCounts

assert_kernel_only TetraStereo.Engine.RingParentHandCounts.transport
assert_kernel_only TetraStereo.Engine.RingParentHandCounts.excludes
assert_kernel_only TetraStereo.Engine.RingParentHandCounts.ordinary_noExchangeTie
