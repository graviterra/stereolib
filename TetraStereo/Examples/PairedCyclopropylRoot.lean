import TetraStereo.Examples.PairedCyclopropylEarlierTie
import TetraStereo.Examples.PairedCyclopropylComparison
import TetraStereo.Examples.CrossParentPublicReport

/-! Public ballot at the central carbon from the signed occurrence census on each arm. -/
set_option autoImplicit false
namespace TetraStereo.Examples.PairedCyclopropylRoot
open OneCenter Engine LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingGroupedTrials (atom)
open RingGroupedCentre (cursor)
open RingGroupedReport (origin)
open RingFullPathEligibility (Key Reads)
open RingFullPathTrialReadings (trialKey trials Outcome)
open RingNestedActivePair (Frame Labels)
open RingFullPathPublication (Ballots)
open PairedCyclopropylPaths (molecule)
open PairedCyclopropylComparison (Hands Complete verdict)
open RingWrittenPHReadings (geometry)
open CrossParentClasses (publicRead)
open AntipodalCyclohexaneRanking (slotNumber compare_distinct_atoms)
open private frame_perm from TetraStereo.Examples.DecalinFrames
open private keys_exact from TetraStereo.Engine.RingFullPathPublication
open private slot_injective from TetraStereo.Engine.RingAtomicFramePriority
open private strict_ballot from TetraStereo.Examples.AntipodalCyclohexaneReport
attribute [local instance] lexOrd

def onSide (hands : Bool → Hands) (side rev : Bool) := if rev then (hands side).mirror else hands side
def order (h : Bool → Hands) (rev : Bool) := (verdict (onSide h false rev) (onSide h true rev)).order
private def rank (h : Bool → Hands) (rev : Bool) (n : Nat) :=
  if n = 1 then 4 else if n = 2 then 0 else if n = 3 then (if order h rev = .lt then 1 else 2)
  else (if order h rev = .gt then 1 else 2)
private theorem compare_carbons (h : Bool → Hands) (rev : Bool) :
    compare (rank h rev 3) (rank h rev 14) = order h rev := by
  cases eqn : order h rev <;> simp only [rank,eqn] <;> decide
def ArmCensus {i : Input} (v : i.certified.Atom) (h : Bool → Hands) : Prop :=
  ∀ (fr : Frame i (origin i v)) (s : Fin 4) (side rev : Bool), atom fr s = (if side then 14 else 3) →
    Complete (publicRead i v) rev (cursor fr s) (onSide h side rev)

def rootFrame : List Nat := [1,3,14,2]
theorem neighbors0 : (RingAtomicNeighborOrder.neighbors molecule 0).Perm rootFrame := by
  exact (RingStereoSiblingPass.legal_order _ _).perm.trans (by decide +kernel)

theorem frameIds {i : Input} (raw : i.molecule = molecule) {v : i.certified.Atom}
    (hz : v.val = 0) (fr : RingNestedActivePair.Frame i (origin i v)) :
    (fr.atoms (List.finRange 4)).Perm rootFrame := by
  have all := frame_perm fr
  have focus : v = fr.center.val := Option.some.inj
    ((i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff _ _).mp fr.recognized).2
  rw [raw,←focus,hz] at all
  exact all.trans neighbors0

private abbrev z := RingAtomicNeighborOrder.atomicNumber molecule

private theorem numbers (h : Bool → Hands) (rev : Bool) (a b : Nat) (ha : a ∈ rootFrame) (hb : b ∈ rootFrame) :
    (z a ≠ z b → compare (z a) (z b) = compare (rank h rev a) (rank h rev b)) ∧
    (a ≠ b → z a = z b → (a = 3 ∧ b = 14) ∨ (a = 14 ∧ b = 3)) := by
  simp only [rootFrame,List.mem_cons,List.mem_nil_iff,or_false] at ha hb
  rcases ha with rfl|rfl|rfl|rfl <;> rcases hb with rfl|rfl|rfl|rfl <;>
    cases ho : order h rev <;> simp only [rank,ho] <;> decide +kernel

theorem frame_order {i : Input} (graph : i.molecule = molecule)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (root : i.certified.Atom) (zero : root.val = 0)
    (fr : RingNestedActivePair.Frame i (origin i root)) (hands : Bool → Hands)
    (census : ArmCensus root hands)
    (rev : Bool) (ks : Fin 4 → Key) (got : RingFullPathPublication.keys? fr (publicRead i root) rev = some ks)
    (a b : Fin 4) : compare (trialKey (ks a) []) (trialKey (ks b) []) =
      compare (rank hands rev (atom fr a)) (rank hands rev (atom fr b)) := by
  have key (s : Fin 4) : RingFullPathEligibility.key? i (publicRead i root) rev (cursor fr s) = some (ks s) :=
    RingActivePairReport.four_at got s
  have reads (s : Fin 4) : Reads i (publicRead i root) rev (cursor fr s) (ks s) := by
    obtain ⟨k,hk,exactK⟩ := RingFullPathEligibility.key_exact (RingChemicalGraphProof.ready geom _)
      rev (cursor fr s) (RingGroupedCentre.valid fr s) (fr.direction s).property.1
    exact (exactK _).mpr (Option.some.inj ((key s).symm.trans hk))
  have forward (u v : Fin 4) (U : atom fr u = 3) (V : atom fr v = 14) :
      compare (trialKey (ks u) []) (trialKey (ks v) []) = compare (rank hands rev (atom fr u)) (rank hands rev (atom fr v)) := by
    obtain ⟨x,y,hx,hy,early,lower⟩ := PairedCyclopropylEarlierTie.earlier graph geom root zero fr u v (by rw [U,V]; decide) rev
    obtain rfl : x = ks u := Option.some.inj (hx.symm.trans (key u))
    obtain rfl : y = ks v := Option.some.inj (hy.symm.trans (key v))
    have ordered := PairedCyclopropylComparison.native_order (census fr u false rev U)
      (census fr v true rev V) (key u) (key v) early lower
    rw [U,V,compare_carbons]
    exact ordered
  by_cases same : atom fr a = atom fr b
  · have eq : a = b := slot_injective fr (Subtype.ext (Fin.ext (by simpa only [RingAtomicFramePriority.slotNeighbor_val] using same)))
    subst b; simp
  have mem (s : Fin 4) := (frameIds graph zero fr).mem_iff.mp (List.mem_map_of_mem (f := atom fr) (List.mem_finRange s))
  have pos := numbers hands rev _ _ (mem a) (mem b)
  by_cases diff : z (atom fr a) ≠ z (atom fr b)
  · have different : slotNumber fr a ≠ slotNumber fr b := by unfold slotNumber; rw [graph]; exact diff
    have out := compare_distinct_atoms fr (reads a) (reads b) different [] []
    unfold slotNumber at out
    rw [graph] at out
    exact out.trans (pos.1 diff)
  rcases pos.2 same (of_not_not diff) with ⟨A,B⟩|⟨B,A⟩
  · exact forward a b A B
  · calc
      _ = (compare (trialKey (ks b) []) (trialKey (ks a) [])).swap := Std.OrientedCmp.eq_swap ..
      _ = _ := congrArg Ordering.swap (forward b a A B)
      _ = _ := (Std.OrientedCmp.eq_swap ..).symm

private def row (o : Ordering) := if o = .lt then [1,14,3,2] else rootFrame

private theorem strict_ranks (h : Bool → Hands) (rev : Bool) (o : Ordering)
    (eqn : order h rev = o) (strict : o ≠ .eq) (a b : Nat) (ha : a ∈ rootFrame) (hb : b ∈ rootFrame) :
    compare (rank h rev a) (rank h rev b) = compare ((row o).idxOf b) ((row o).idxOf a) := by
  simp only [rootFrame,List.mem_cons,List.mem_nil_iff,or_false] at ha hb
  rcases ha with rfl|rfl|rfl|rfl <;> rcases hb with rfl|rfl|rfl|rfl <;> cases o
    <;> first | contradiction | (simp only [rank,eqn]; decide +kernel)

private theorem tie_pair (h : Bool → Hands) (rev : Bool) (_eqn : order h rev = .eq)
    (a b : Nat) (ha : a ∈ rootFrame) (hb : b ∈ rootFrame) (diff : a ≠ b)
    (eqrank : rank h rev a = rank h rev b) : a ∈ [3,14] := by
  simp only [rootFrame,List.mem_cons,List.mem_nil_iff,or_false] at ha hb
  rcases ha with rfl|rfl|rfl|rfl <;> rcases hb with rfl|rfl|rfl|rfl <;>
    cases ho : order h rev <;> simp_all [rank]

/-- Exactly one indistinguishable pair schedules only an ordinary ballot,
even if a marked-atom comparison could separate its members. -/
private theorem tied_ballot {i : Input} {v : i.certified.Atom} (fr : Frame i (origin i v))
    (inventory : (fr.atoms (List.finRange 4)).Perm rootFrame)
    (ready : RingGroupedStereo.Ready (origin i v) (publicRead i v)) (rev : Bool) (h : Bool → Hands)
    (tied : order h rev = .eq)
    (cmp : ∀ ks, RingFullPathPublication.keys? fr (publicRead i v) rev = some ks → ∀ a b,
      compare (trialKey (ks a) []) (trialKey (ks b) []) = compare (rank h rev (atom fr a)) (rank h rev (atom fr b))) :
    ∃ ks, Ballots fr (publicRead i v) rev ks [none] := by
  obtain ⟨ks,got,reads⟩ := keys_exact fr ready rev
  have ids : ((List.finRange 4).map (atom fr)).Perm rootFrame := inventory
  have unique : ((List.finRange 4).map (atom fr)).Nodup := ids.nodup_iff.mpr (by decide)
  have inj := (List.nodup_map_iff_inj_on (List.nodup_finRange 4)).mp unique
  have member (a : Fin 4) : atom fr a ∈ rootFrame :=
    ids.mem_iff.mp (List.mem_map.mpr ⟨a,List.mem_finRange _,rfl⟩)
  let ts := RingFullPathEligibility.tiedSlots ks
  have subset : ts.map (atom fr) ⊆ [3,14] := by
    intro n hn
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hn
    obtain ⟨u,ne,e⟩ := (RingFullPathEligibility.mem_tied ks s).mp hs
    have eqn := cmp ks got s u
    rw [e,Std.ReflOrd.compare_self] at eqn
    exact tie_pair h rev tied _ _ (member s) (member u)
      (fun same => ne (inj s (List.mem_finRange _) u (List.mem_finRange _) same))
      (Std.compare_eq_eq_iff_eq.mp eqn.symm)
  have sub : ts.Sublist (List.finRange 4) := List.filter_sublist
  have lim := (List.subperm_of_subset (unique.sublist (sub.map _)) subset).length_le
  have short : ¬ 3 ≤ ts.length := by simpa using (show ts.length < 3 by simpa using Nat.lt_succ_of_le (by simpa using lim : ts.length ≤ 2))
  have ordinary : trials ks = [none] := by simp [trials,RingFullPathEligibility.candidates,show ¬ 3 ≤ (RingFullPathEligibility.tiedSlots ks).length from short]
  obtain ⟨a,_,ha⟩ := List.mem_map.mp (ids.mem_iff.mpr (by decide : 3 ∈ rootFrame))
  obtain ⟨b,_,hb⟩ := List.mem_map.mp (ids.mem_iff.mpr (by decide : 14 ∈ rootFrame))
  have different : a ≠ b := by rintro rfl; omega
  have same := cmp ks got a b
  rw [ha,hb,compare_carbons,tied] at same
  refine ⟨ks,(reads _).mpr rfl,?_⟩
  rw [ordinary]
  exact .cons ⟨fun _ => [],fun _ => rfl,Outcome.tie different (Std.compare_eq_eq_iff_eq.mp same)⟩ .nil

private def vote (h : RS) (rev : Bool) : Ordering → Option RS
  | .eq => none
  | .gt => some (if rev then h.swap else h)
  | .lt => some (if rev then h else h.swap)

private theorem ballots {i : Input} {v : i.certified.Atom} (fr : Frame i (origin i v))
    (inventory : (fr.atoms (List.finRange 4)).Perm rootFrame)
    (ready : RingGroupedStereo.Ready (origin i v) (publicRead i v)) (rev : Bool) (h : Bool → Hands)
    (c : RS) (seen : readback? (geometry i.spatial) rootFrame = some c)
    (cmp : ∀ ks, RingFullPathPublication.keys? fr (publicRead i v) rev = some ks → ∀ a b,
      compare (trialKey (ks a) []) (trialKey (ks b) []) = compare (rank h rev (atom fr a)) (rank h rev (atom fr b))) :
    ∃ ks, Ballots fr (publicRead i v) rev ks [vote c rev (order h rev)] := by
  by_cases tie : order h rev = .eq
  · rw [tie]
    exact tied_ballot fr inventory ready rev h tie cmp
  · let o := order h rev
    have perms : (row o).Perm rootFrame ∧ (row o).Pairwise (fun a b => (row o).idxOf a < (row o).idxOf b) := by
      cases o <;> decide
    have ids : ((List.finRange 4).map (atom fr)).Perm rootFrame := inventory
    have mem (s : Fin 4) := ids.mem_iff.mp (List.mem_map_of_mem (f := atom fr) (List.mem_finRange s))
    have comparisons (ks) (got : RingFullPathPublication.keys? fr (publicRead i v) rev = some ks) (a b : Fin 4) :=
      (cmp ks got a b).trans (strict_ranks h rev o rfl tie _ _ (mem a) (mem b))
    obtain ⟨voted,hv⟩ : ∃ voted, vote c rev o = some voted ∧
        readback? (if rev then mirror (geometry i.spatial) else geometry i.spatial) (row o) = some voted := by
      have swapped := LocalizedMarkedTerminalGaugeSwap.readback_swap23 (geometry i.spatial) 1 3 14 2
      change readback? _ [1,3,14,2] = some c at seen
      rw [seen] at swapped
      change order h rev ≠ .eq at tie
      cases ho : order h rev <;> cases rev <;> cases c <;>
        simp_all [o,row,rootFrame,vote,RS.swap,readback_mirror]
    change ∃ ks, Ballots fr _ rev ks [vote c rev o]
    rw [hv.1]
    exact strict_ballot fr _ ready rev _ (perms.1.trans inventory.symm) perms.2 comparisons voted hv.2

/-- The root determinant uses fluorine, arm 3, arm 14, hydrogen. -/
def outcome (a b : Hands) (c : RS) : Option Labels :=
  if a = b then none else
    let k := if (verdict a b).order = .gt then c else c.swap
    if b = a.mirror then some (.pseudoasymmetric (pseudoRSOfRS k),.pseudoasymmetric (pseudoRSOfRS k))
    else some (.chiral k,.chiral k.swap)

private theorem crossed (h : Bool → Hands) (c : RS) :
    RingFullPathPublication.crossed [vote c false (order h false)] [vote c true (order h true)] =
      outcome (h false) (h true) c := by
  unfold order onSide
  generalize h false = a
  generalize h true = b
  obtain ⟨(_|_),(_|_),(_|_)⟩ := a <;> obtain ⟨(_|_),(_|_),(_|_)⟩ := b <;> cases c <;> decide

theorem root {i : Input} (raw : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (v : i.certified.Atom) (zero : v.val = 0)
    (h : Bool → Hands) (census : ArmCensus v h)
    (c : RS) (seen : readback? (geometry i.spatial) rootFrame = some c) :
    RingChemicalGraphProof.root i v = some (outcome (h false) (h true) c) := by
  let q := origin i v
  have degree : Fintype.card (i.certified.moleculeGraph.Neighbor v) = 4 := by
    rw [RingAtomicNeighborOrder.degree_eq,raw,zero]
    exact neighbors0.length_eq.trans rfl
  let center : i.certified.TetrahedralCenter := ⟨v,(i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mpr degree⟩
  have recg := (i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff q center).mpr ⟨rfl,rfl⟩
  obtain ⟨fr,_⟩ := RingGroupedGeometry.frame_exists recg
  have one (rev : Bool) := ballots fr (frameIds raw zero fr) (RingChemicalGraphProof.ready ok _) rev h c seen
    (frame_order raw ok v zero fr h census rev)
  obtain ⟨x,hx⟩ := one false
  obtain ⟨y,hy⟩ := one true
  have both := RingFullPathPublication.TwoGeometry.centre hx hy
  rw [crossed] at both
  have off := RingHydrogenLeafGeometry.notP_of_degree_four (i := i) v degree
  have noP : RingPyramidalPublication.focusP i q = none := by
    change (some v).filter (RingPyramidalPublication.phosphorus i) = none
    simp [off]
  rw [RingChemicalGraphProof.root,RingEligibleGraph.root_exact _ (RingChemicalGraphProof.skips i),←RingChemicalGraphProof.state,
    RingChemicalGraphProof.state_eq,RingPyramidalPublication.publish,noP,
    RingFullPathConstitution.fast_local ok (RingChemicalGraphProof.ready ok _)]
  exact (RingFullPathPublication.two_geometry_iff ok _ _ (RingChemicalGraphProof.ready ok _) _).mpr both

end TetraStereo.Examples.PairedCyclopropylRoot
assert_kernel_only TetraStereo.Examples.PairedCyclopropylRoot.root
