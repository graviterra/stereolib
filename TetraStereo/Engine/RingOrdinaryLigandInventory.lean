import TetraStereo.Engine.RingStereoStageProjection
import TetraStereo.Engine.RingSignedInventoryLayers
import TetraStereo.Engine.RingRule5Tie
import TetraStereo.Engine.RingGlobalComparison

/-! A molecular characterization of a complete ordinary ligand tie. Keep
the through-4c type of the root and the unordered signed paths at each
distance. All four ordinary priority fields can be recovered from these. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOrdinaryLigandInventory
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader)
open RingRetainedChemicalTrace (Word)
open RingStereoSphereInventory (Inventory inventory? inventoryWith reading)
open RingRetainedStereoRefinement (priority)
open RingFullPathEligibility (Key)
open RingRule5Shape (Valid On)
open private rank_projects from TetraStereo.Engine.RingStereoStageProjection

abbrev Observation := List Word × Inventory

def observe? (i : Input) (r : Reader i) (rev : Bool) (q : Arm i) : Option Observation := do
  let k ← priority i r rev [.lowercase] q
  let signed ← inventory? i r rev [.lowercase] q
  return (k.deep,signed)

private def indexed (i : Input) (r : Reader i) (rev : Bool) (q : Arm i) : Option Observation :=
  RingOccurrenceStereo.withRankReaders i r rev [.lowercase] q fun edges rank => do
    let k ← rank q
    let signed ← inventoryWith r rev edges rank q
    return (k.deep,signed)

@[csimp] private theorem indexed_exact : @observe? = @indexed := by
  funext i r rev q
  unfold indexed
  rw [RingOccurrenceStereo.withRankReaders_eq]
  rfl

def assemble (obs : Observation) : Key :=
  let base := RingStereoStageProjection.inventory obs.2
  ⟨obs.1.dropLast,max (reading .R base) (reading .S base),
    obs.1.getLast?.getD [],reading .R obs.2⟩

def key? (i : Input) (r : Reader i) (rev : Bool) (q : Arm i) :=
  (observe? i r rev q).map assemble

/-- One rank reader and one signed inventory produce all ordinary fields.
The equation includes failure on arbitrary readers. -/
theorem key_exact (i : Input) (r : Reader i) (rev : Bool) (q : Arm i) :
    key? i r rev q = RingFullPathEligibility.key? i r rev q := by
  rw [← RingStereoStageProjection.key_exact]
  unfold key? observe? RingStereoStageProjection.key?
  cases hl : priority i r rev [.lowercase] q with
  | none => cases priority i r rev [] q <;> rfl
  | some l =>
    obtain ⟨u,hu,drop⟩ := rank_projects i r rev q l hl
    rw [hu]
    cases inventory? i r rev [.lowercase] q with
    | none => rfl
    | some fine =>
      simp [assemble,RingStereoSiblingPass.Branch.deep]
      simpa [RingStereoSiblingPass.Branch.deep] using drop

/-- The observation retains exactly the distinctions of a complete ordinary
trial key on comparable molecular arms of a ready root. -/
theorem tie_iff {i : Input} {f : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready f r)
    (rev : Bool) (a b : Arm i) (va : Valid a) (vb : Valid b) (oa : On f a) (ob : On f b) :
    RingFullPathEligibility.key? i r rev a = RingFullPathEligibility.key? i r rev b ↔
      observe? i r rev a = observe? i r rev b := by
  constructor
  · intro same
    obtain ⟨k,ka,sa⟩ := RingFullPathEligibility.key_exact ready rev a va oa
    obtain ⟨l,kb,sb⟩ := RingFullPathEligibility.key_exact ready rev b vb ob
    obtain rfl := Option.some.inj (ka.symm.trans (same.trans kb))
    have ra := (sa _).mpr rfl
    have rb := (sb _).mpr rfl
    have types := (RingRule5Tie.reading_key ready va oa ra).trans
      (RingRule5Tie.reading_key ready vb ob rb).symm
    have fixed {p : Arm i} (h : RingFullPathEligibility.Reads i r rev p k) :
        RingFullPathRule5.Word i r rev .R p k.fixedR := by
      obtain ⟨_,_,_,_,_,_,_,_,_,out,rfl⟩ := h
      exact out
    have inv := RingSignedInventoryLayers.lower_inventory_eq ready va vb oa ob types (fixed ra) (fixed rb)
    obtain ⟨u,hu⟩ := RingOccurrenceStereo.rank_total ready rev [.lowercase] a va oa
    obtain ⟨v,hv⟩ := RingOccurrenceStereo.rank_total ready rev [.lowercase] b vb ob
    change priority i r rev [.lowercase] a = some u at hu
    change priority i r rev [.lowercase] b = some v at hv
    simp only [RingRule5Shape.key,hu,hv,Option.map_some,Option.getD_some] at types
    simp only [observe?,hu,hv,inv]
    cases inventory? i r rev [.lowercase] b with
    | none => rfl
    | some signed => exact congrArg (fun d => some (d,signed)) types
  · intro same
    simpa only [← key_exact,key?] using congrArg (Option.map assemble) same

/-- Applies to the actual prior store used at each scheduled publication,
including the original root's final comparison. -/
theorem public_tie_iff {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {root : i.certified.Atom} {k : Nat} {f : Site i} (called : RingGlobalComparison.Called i root k f)
    (rev : Bool) (a b : Arm i) (va : Valid a) (vb : Valid b) (oa : On f a) (ob : On f b) :
    let r := RingGlobalComparison.prior i root k
    RingFullPathEligibility.key? i r rev a = RingFullPathEligibility.key? i r rev b ↔
      observe? i r rev a = observe? i r rev b := by
  dsimp only
  rw [RingGlobalComparison.prior_exact called]
  exact tie_iff (RingChemicalGraphProof.ready geom f) rev a b va vb oa ob

/-- Tied slots tested by the public Rule 6 promotion gate are exactly
the slots with a second copy of their complete molecular observation. -/
theorem tied_slot {i f r rev} (fr : @RingNestedActivePair.Frame i f)
    (ready : RingGroupedStereo.Ready f r) {ks : RingActivePairReport.Slot → Key}
    (computed : RingFullPathPublication.keys? fr r rev = some ks) (s : RingActivePairReport.Slot) :
    s ∈ RingFullPathEligibility.tiedSlots ks ↔
      ∃ j, s ≠ j ∧ observe? i r rev (RingGroupedCentre.cursor fr s) =
        observe? i r rev (RingGroupedCentre.cursor fr j) := by
  rw [RingFullPathEligibility.mem_tied]
  apply exists_congr
  intro j
  apply and_congr_right'
  have law := tie_iff ready rev _ _ (RingGroupedCentre.valid fr s) (RingGroupedCentre.valid fr j)
    (fr.direction s).property.1 (fr.direction j).property.1
  have atSlot (n : RingActivePairReport.Slot) : RingFullPathEligibility.key? i r rev
      (RingGroupedCentre.cursor fr n) = some (ks n) := RingActivePairReport.four_at computed n
  simpa only [atSlot,Option.some.injEq] using law

open RingUnorderedSphereReading (layers?)
open private start nextWith eraseVisits from TetraStereo.Engine.RingStereoSphereInventory

private theorem layers_nonempty {α : Type} (next : α → Option (List α)) :
    ∀ n row out, layers? next n row = some out → ∀ xs ∈ out, xs ≠ [] := by
  intro n
  induction n with
  | zero =>
    intro row out h
    cases row with
    | nil => cases h; simp
    | cons a row => cases h
  | succ n ih =>
    intro row out h
    cases row with
    | nil => cases h; simp
    | cons a row =>
      change ((a::row).mapM next >>= fun bs => do
        return (a::row) :: (← layers? next n bs.flatten)) = some out at h
      obtain ⟨bs,_,h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨more,hm,h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      intro xs hx
      rcases List.mem_cons.mp hx with rfl | hx
      · simp
      · exact ih _ _ hm xs hx

private theorem no_empty {i r rev q d rows} (got : observe? i r rev q = some (d,rows)) :
    ∀ row ∈ rows, row ≠ 0 := by
  unfold observe? at got
  obtain ⟨k,_,got⟩ := Option.bind_eq_some_iff.mp got
  obtain ⟨inv,found,got⟩ := Option.bind_eq_some_iff.mp got
  cases Option.some.inj got
  unfold inventory? inventoryWith at found
  obtain ⟨vs,run,rfl⟩ := Option.map_eq_some_iff.mp found
  intro row h
  obtain ⟨vs',mem,rfl⟩ := List.mem_map.mp h
  have ne := layers_nonempty _ _ _ _ run vs' mem
  cases vs' with
  | nil => exact False.elim (ne rfl)
  | cons _ _ => simp

private theorem counts_ext (x y : Inventory) (hx : ∀ row ∈ x, row ≠ 0)
    (hy : ∀ row ∈ y, row ≠ 0)
    (counts : ∀ n p, (x.getD n 0).count p = (y.getD n 0).count p) : x = y := by
  induction x generalizing y with
  | nil =>
    cases y with
    | nil => rfl
    | cons a ys => exact False.elim (hy a List.mem_cons_self
        (Multiset.ext.mpr (fun p => (counts 0 p).symm)))
  | cons a xs ih =>
    cases y with
    | nil => exact False.elim (hx a List.mem_cons_self (Multiset.ext.mpr (counts 0)))
    | cons b ys =>
      exact congrArg₂ List.cons (Multiset.ext.mpr (counts 0))
        (ih ys (fun c h => hx c (.tail _ h)) (fun c h => hy c (.tail _ h)) (fun n => counts (n+1)))

/-- Once root types agree, a strict ordinary distinction is witnessed by a
specific distance and a specific signed priority path with different multiplicities.
Missing spheres count as zero; every recorded sphere contains occurrences. -/
theorem distinction_iff {i f r rev} (ready : @RingGroupedStereo.Ready i f r)
    {a b : Arm i} (va : Valid a) (vb : Valid b) (oa : On f a) (ob : On f b)
    {d x y} (ax : observe? i r rev a = some (d,x)) (by' : observe? i r rev b = some (d,y)) :
    RingFullPathEligibility.key? i r rev a ≠ RingFullPathEligibility.key? i r rev b ↔
      ∃ n p, (x.getD n 0).count p ≠ (y.getD n 0).count p := by
  have tie := tie_iff ready rev a b va vb oa ob
  rw [ax,by'] at tie
  constructor
  · intro ne
    by_contra! counts
    exact ne (tie.mpr (congrArg (fun v => some (d,v)) (counts_ext x y (no_empty ax) (no_empty by') counts)))
  · rintro ⟨n,p,h⟩ same
    have eqn := congrArg Prod.snd (Option.some.inj (tie.mp same))
    exact h (congrArg (fun v : Inventory => (v.getD n 0).count p) eqn)

end TetraStereo.Engine.RingOrdinaryLigandInventory
assert_kernel_only TetraStereo.Engine.RingOrdinaryLigandInventory.key_exact
assert_kernel_only TetraStereo.Engine.RingOrdinaryLigandInventory.tie_iff
assert_kernel_only TetraStereo.Engine.RingOrdinaryLigandInventory.public_tie_iff
assert_kernel_only TetraStereo.Engine.RingOrdinaryLigandInventory.tied_slot
assert_kernel_only TetraStereo.Engine.RingOrdinaryLigandInventory.distinction_iff
