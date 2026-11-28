import TetraStereo.Examples.CrossParentPublicRanking
import TetraStereo.Examples.CrossParentDonorStore
import TetraStereo.Examples.AntipodalCyclohexaneReport

/-! Complete publication at atom 0 of the 41-atom eight-donor comparison. -/
set_option autoImplicit false
namespace TetraStereo.Examples.CrossParentPublicReport
open OneCenter Engine LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingGroupedTrials (atom)
open RingGroupedReport (origin)
open RingFullPathTrialReadings (trialKey trials Outcome)
open RingNestedActivePair (Frame Labels)
open RingFullPathPublication (Ballots)
open CrossParentDonorStore (molecule ligandRow)
open CrossParentRootOrder (rank order rCount majority compareCounts)
open RingWrittenPHReadings (geometry)
open private keys_exact from TetraStereo.Engine.RingFullPathPublication
open private frame_perm canonical_perm from TetraStereo.Examples.DecalinFrames
open private strict_ballot from TetraStereo.Examples.AntipodalCyclohexaneReport
open private calibrated from TetraStereo.Engine.RingRetainedAuxiliary
open private toAtom from TetraStereo.Engine.RingAtomicNeighborOrder
open private row? from TetraStereo.Engine.RingChemicalReport
open private shell incident from TetraStereo.Examples.CrossParentDonorStore

open CrossParentPublicRanking (rootFrame neighbors0 frameIds)
open CrossParentClasses (publicRead)
private def row (o : Ordering) := if o = .lt then [40,39,2,1] else rootFrame

private theorem strict_ranks (h : Fin 8 → RS) (rev : Bool) (o : Ordering)
    (eqn : order h rev = o) (strict : o ≠ .eq) (a b : Nat) (ha : a ∈ rootFrame) (hb : b ∈ rootFrame) :
    compare (rank h rev a) (rank h rev b) = compare ((row o).idxOf b) ((row o).idxOf a) := by
  simp only [rootFrame,List.mem_cons,List.mem_nil_iff,or_false] at ha hb
  rcases ha with rfl|rfl|rfl|rfl <;> rcases hb with rfl|rfl|rfl|rfl <;> cases o
    <;> first | contradiction | (simp only [rank,eqn]; decide +kernel)

private theorem tie_pair (h : Fin 8 → RS) (rev : Bool) (_eqn : order h rev = .eq)
    (a b : Nat) (ha : a ∈ rootFrame) (hb : b ∈ rootFrame) (diff : a ≠ b)
    (eqrank : rank h rev a = rank h rev b) : a ∈ [1,2] := by
  simp only [rootFrame,List.mem_cons,List.mem_nil_iff,or_false] at ha hb
  rcases ha with rfl|rfl|rfl|rfl <;> rcases hb with rfl|rfl|rfl|rfl <;>
    simp_all [rank]

/-- Exactly one indistinguishable pair schedules only an ordinary ballot,
even if a marked-atom comparison could separate its members. -/
private theorem tied_ballot {i : Input} {v : i.certified.Atom} (fr : Frame i (origin i v))
    (inventory : (fr.atoms (List.finRange 4)).Perm rootFrame)
    (ready : RingGroupedStereo.Ready (origin i v) (publicRead i v)) (rev : Bool) (h : Fin 8 → RS)
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
  have subset : ts.map (atom fr) ⊆ [1,2] := by
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
  obtain ⟨a,_,ha⟩ := List.mem_map.mp (ids.mem_iff.mpr (by decide : 1 ∈ rootFrame))
  obtain ⟨b,_,hb⟩ := List.mem_map.mp (ids.mem_iff.mpr (by decide : 2 ∈ rootFrame))
  have different : a ≠ b := by rintro rfl; omega
  have same := cmp ks got a b
  rw [ha,hb,CrossParentRootOrder.compare_nitrogens,tied] at same
  refine ⟨ks,(reads _).mpr rfl,?_⟩
  rw [ordinary]
  exact .cons ⟨fun _ => [],fun _ => rfl,Outcome.tie different (Std.compare_eq_eq_iff_eq.mp same)⟩ .nil

private def vote (h : RS) (rev : Bool) : Ordering → Option RS
  | .eq => none
  | .gt => some (if rev then h.swap else h)
  | .lt => some (if rev then h else h.swap)

private theorem ballots {i : Input} {v : i.certified.Atom} (fr : Frame i (origin i v))
    (inventory : (fr.atoms (List.finRange 4)).Perm rootFrame)
    (ready : RingGroupedStereo.Ready (origin i v) (publicRead i v)) (rev : Bool) (h : Fin 8 → RS)
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
      have swapped := LocalizedMarkedTerminalGaugeSwap.readback_swap34 (geometry i.spatial) 40 39 1 2
      change readback? _ [40,39,1,2] = some c at seen
      rw [seen] at swapped
      change order h rev ≠ .eq at tie
      cases ho : order h rev <;> cases rev <;> cases c <;>
        simp_all [o,row,rootFrame,vote,RS.swap,readback_mirror]
    change ∃ ks, Ballots fr _ rev ks [vote c rev o]
    rw [hv.1]
    exact strict_ballot fr _ ready rev _ (perms.1.trans inventory.symm) perms.2 comparisons voted hv.2

/-- The signed root outcome from the two four-donor populations. -/
def outcome (left right : Nat) (c : RS) : Option Labels :=
  if left = right then none else
    let k := if compareCounts left right = .gt then c else c.swap
    if majority left = majority right then
      some (.pseudoasymmetric (pseudoRSOfRS k),.pseudoasymmetric (pseudoRSOfRS k))
    else some (.chiral k,.chiral k.swap)

/-- After equal counts have been excluded, equal Rule 4b majorities mean
that the two four-donor populations are complementary. -/
theorem equal_majority_iff (a b : Fin 5) :
    majority a = majority b ↔ a = b ∨ a.val+b.val = 4 := by
  fin_cases a <;> fin_cases b <;> decide +kernel

/-- Count each of the 256 numbered donor-sign assignments once, holding the
root determinant fixed. Reversing that determinant preserves these counts. -/
theorem class_sizes (c : RS) :
    let results := (List.finRange 256).map fun mask =>
      let h (j : Fin 8) : RS := if mask.val.testBit j.val then .R else .S
      outcome (rCount h true false) (rCount h false false) c
    results.count none = 70 ∧
    (results.count (some (.pseudoasymmetric .r,.pseudoasymmetric .r)) +
      results.count (some (.pseudoasymmetric .s,.pseudoasymmetric .s))) = 34 ∧
    (results.count (some (.chiral .R,.chiral .S)) + results.count (some (.chiral .S,.chiral .R))) = 152 := by
  cases c <;> decide +kernel

private theorem crossed_counts (h : Fin 8 → RS) (c : RS) :
    RingFullPathPublication.crossed [vote c false (order h false)] [vote c true (order h true)] =
      outcome (rCount h true false) (rCount h false false) c := by
  have table (a b : Fin 5) (c : RS) :
      RingFullPathPublication.crossed [vote c false (compareCounts a b)] [vote c true (compareCounts (4-a.val) (4-b.val))] =
        outcome a b c := by fin_cases a <;> fin_cases b <;> cases c <;> decide +kernel
  exact table ⟨_,Nat.lt_succ_of_le (CrossParentRootOrder.bound h true false)⟩
    ⟨_,Nat.lt_succ_of_le (CrossParentRootOrder.bound h false false)⟩ c

private theorem raw_nonflat {i : Input} (raw : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (v : i.certified.Atom) (ids : List Nat) (four : ids.length = 4)
    (perm : (RingAtomicNeighborOrder.neighbors molecule v.val).Perm ids) :
    (readback? (geometry i.spatial) ids).isSome = true := by
  have degree : Fintype.card (i.certified.moleculeGraph.Neighbor v) = 4 := by
    rw [RingAtomicNeighborOrder.degree_eq,raw,perm.length_eq,four]
  let center : i.certified.TetrahedralCenter := ⟨v,(i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mpr degree⟩
  have rows := canonical_perm i center
  rw [raw] at rows
  rw [←RingWrittenPHReadings.inputGeometry_eq]
  exact calibrated i ok center _ ((rows.trans perm).symm)

theorem root {i : Input} (raw : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (v : i.certified.Atom) (zero : v.val = 0)
    (h : Fin 8 → RS) (signs : ∀ j, readback? (geometry i.spatial) (ligandRow j) = some (h j))
    (c : RS) (seen : readback? (geometry i.spatial) rootFrame = some c) :
    RingChemicalGraphProof.root i v = some (outcome (rCount h true false) (rCount h false false) c) := by
  let q := origin i v
  have degree : Fintype.card (i.certified.moleculeGraph.Neighbor v) = 4 := by
    rw [RingAtomicNeighborOrder.degree_eq,raw,zero]
    exact neighbors0.length_eq.trans rfl
  let center : i.certified.TetrahedralCenter := ⟨v,(i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mpr degree⟩
  have recg := (i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff q center).mpr ⟨rfl,rfl⟩
  obtain ⟨fr,_⟩ := RingGroupedGeometry.frame_exists recg
  have one (rev : Bool) := ballots fr (frameIds raw zero fr) (RingChemicalGraphProof.ready ok _) rev h c seen
    (CrossParentPublicRanking.frame_order raw ok v zero fr h signs rev)
  obtain ⟨x,hx⟩ := one false
  obtain ⟨y,hy⟩ := one true
  have both := RingFullPathPublication.TwoGeometry.centre hx hy
  rw [crossed_counts] at both
  have off := RingHydrogenLeafGeometry.notP_of_degree_four (i := i) v degree
  have noP : RingPyramidalPublication.focusP i q = none := by
    change (some v).filter (RingPyramidalPublication.phosphorus i) = none
    simp [off]
  rw [RingChemicalGraphProof.root,RingEligibleGraph.root_exact _ (RingChemicalGraphProof.skips i),←RingChemicalGraphProof.state,
    RingChemicalGraphProof.state_eq,RingPyramidalPublication.publish,noP,
    RingFullPathConstitution.fast_local ok (RingChemicalGraphProof.ready ok _)]
  exact (RingFullPathPublication.two_geometry_iff ok _ _ (RingChemicalGraphProof.ready ok _) _).mpr both

/-- Compute the answer from nine geometric determinants. Equal four-donor
populations give a completed refusal. -/
def expected? (x : SpatialConfiguration) : Option RingGroupedReport.Report := do
  let c ← readback? (geometry x) rootFrame
  if present : ∀ j : Fin 8, (readback? (geometry x) (ligandRow j)).isSome = true then
    let h j := (readback? (geometry x) (ligandRow j)).get (present j)
    return [(0,outcome (rCount h true false) (rCount h false false) c)]
  else none

theorem raw_root (i : Input) (raw : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    RingHydrogenReport.fromRaw? molecule i.spatial [0] = expected? i.spatial := by
  let v := toAtom i 0 (by rw [raw]; decide)
  obtain ⟨c,seen⟩ := Option.isSome_iff_exists.mp (raw_nonflat raw ok v rootFrame rfl neighbors0)
  have present (j : Fin 8) : (readback? (geometry i.spatial) (ligandRow j)).isSome = true := by
    let d := toAtom i (7+j.val) (by rw [raw]; change 7+j.val < 41; omega)
    have ns := (show (RingAtomicNeighborOrder.neighbors molecule (7+j.val)).Perm (incident (7+j.val)) from
      (RingStereoSiblingPass.legal_order _ _).perm).trans (shell j).1.symm
    exact raw_nonflat raw ok d _ rfl ns
  let h j := (readback? (geometry i.spatial) (ligandRow j)).get (present j)
  have out := root raw ok v rfl h (fun _ => (Option.some_get _).symm) c seen
  have closed : RingHydrogenCompletion.plan molecule = [] := by decide +kernel
  have bridge := RingWrittenPHReadings.fromRaw_closed_report i (raw ▸ closed) ok [v]
  rw [raw] at bridge
  change RingHydrogenReport.fromRaw? molecule i.spatial ([v].map Fin.val) = _
  rw [bridge]
  simp [expected?,seen,present,RingChemicalReport.report?,row?,List.mapM_cons,out,h]
  rfl

/-- Base geometry, single F/Cl swap, then the second F/Cl swap. -/
def fixtureLabel (v : Fin 3) : Option Labels :=
  if v.val = 0 then none else if v.val = 1 then some (.chiral .R,.chiral .S)
  else some (.pseudoasymmetric .r,.pseudoasymmetric .r)

theorem three_controls (v : Fin 3) :
    RingHydrogenReport.fromRaw? molecule (CrossParentDonorStore.geometry v) [0] = some [(0,fixtureLabel v)] := by
  have raw := raw_root (CrossParentDonorStore.input v) rfl (CrossParentDonorStore.admitted v)
  refine raw.trans ?_
  change expected? (CrossParentDonorStore.geometry v) = _
  fin_cases v <;> decide +kernel

end TetraStereo.Examples.CrossParentPublicReport
assert_kernel_only TetraStereo.Examples.CrossParentPublicReport.root
assert_kernel_only TetraStereo.Examples.CrossParentPublicReport.raw_root
assert_kernel_only TetraStereo.Examples.CrossParentPublicReport.three_controls
assert_kernel_only TetraStereo.Examples.CrossParentPublicReport.class_sizes
