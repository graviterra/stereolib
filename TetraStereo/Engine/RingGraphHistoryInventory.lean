import TetraStereo.Engine.RingOrdinaryLigandInventory
import TetraStereo.Engine.RingHistoryDonorRanks

/-! Unordered signed donor inventories on molecular histories. A change in
the enumeration of neighbors may permute each sphere but must preserve every
occurrence, path edge, hand, and multiplicity in it. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingGraphHistoryInventory
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingStereoSphereInventory (SignedPath Visit Inventory)
open RingRetainedChemicalTrace (Word)
open RingActiveDistanceSchedule (Cell)
open RingNestedActivePair (Reader)
open RingUnorderedSphereReading (layers?)
open private mapM_perm from TetraStereo.Engine.RingActivePairs
open private start nextWith eraseVisits from TetraStereo.Engine.RingStereoSphereInventory

abbrev History := List Nat
abbrev Edge := History × History
abbrev Entry := Edge × SignedPath
abbrev Rows := List ((Nat × History) × Cell)

def address {i : Input} (q : Site i) := (q.val.root.val, q.val.node.history.map Fin.val)

private theorem address_inj (i : Input) : Function.Injective (@address i) := by
  intro p q same
  have eqs := Prod.mk.inj same
  have root : p.val.root = q.val.root := Fin.ext eqs.1
  have hist := List.map_injective_iff.mpr Fin.val_injective eqs.2
  apply i.certified.molecularFrameUnit_injective_on_simpleBonded_carrier i.single
  simp only [molecularFrameUnit,root,hist]

def encode {i : Input} (rows : List (Site i × Cell)) : Rows := rows.map fun (q,c) => (address q,c)

/-- Each occurrence has an ordinary numeric key. A row storing failure takes
precedence over the default completed refusal for an absent row. -/
def read (rows : Rows) (root : Nat) (h : History) : Cell :=
  ((rows.find? (fun e => e.1 == (root,h))).map Prod.snd).getD (some none)

theorem read_exact {i : Input} (rows : List (Site i × Cell)) (q : Site i) :
    read (encode rows) q.val.root.val (q.val.node.history.map Fin.val) = RingSphereQueue.viewOf rows q := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    obtain ⟨p,c⟩ := row
    by_cases eq : p = q
    · subst p
      simp [read,encode,RingSphereQueue.viewOf,address]
    · have diff := (address_inj i).ne eq
      change address p ≠ (q.val.root.val,q.val.node.history.map Fin.val) at diff
      simpa [read,encode,RingSphereQueue.viewOf,eq,diff] using ih

def hand (cell : Cell) (rev : Bool) : Option RS :=
  RingNestedActivePair.upper (cell.join.map fun p => if rev then p.2 else p.1)

def next (kids : Edge → List Edge) (rank : Edge → Option (List Word))
    (get : History → Cell) (rev : Bool) (p : Entry) : Option (List Entry) :=
  (kids p.1).mapM fun e => do
    let earlier ← rank e
    return (e,p.2 ++ [⟨earlier,hand (get e.2) rev⟩])

def inventory (kids : Edge → List Edge) (rank : Edge → Option (List Word))
    (get : History → Cell) (rev : Bool) (fuel : Nat) (e : Edge) : Option Inventory :=
  (layers? (next kids rank get rev) fuel [(e,[⟨[],hand (get e.2) rev⟩])]).map
    (List.map (fun row => (↑(row.map Prod.snd) : Multiset SignedPath)))

private theorem moveRow {α β : Type} (image : α → β) (dom : α → Prop)
    {native : α → Option (List α)} {other : β → Option (List β)}
    (step : ∀ x, dom x → ∀ xs, native x = some xs →
      (∀ y ∈ xs, dom y) ∧ ∃ ys, other (image x) = some ys ∧ (xs.map image).Perm ys)
    {xs : List α} {blocks : List (List α)} (ok : ∀ x ∈ xs, dom x)
    (hit : xs.mapM native = some blocks) :
    (∀ y ∈ blocks.flatten, dom y) ∧ ∃ bs,
      (xs.map image).mapM other = some bs ∧ (blocks.flatten.map image).Perm bs.flatten := by
  induction xs generalizing blocks with
  | nil =>
    obtain rfl := Option.some.inj hit
    exact ⟨by simp,[],rfl,.nil⟩
  | cons x xs ih =>
    rw [List.mapM_cons] at hit
    obtain ⟨one,h1,tailHit⟩ := Option.bind_eq_some_iff.mp hit
    obtain ⟨rest,h2,eq⟩ := Option.bind_eq_some_iff.mp tailHit
    cases Option.some.inj eq
    obtain ⟨valid,ys,found,perm⟩ := step x (ok _ (.head _)) one h1
    obtain ⟨tail,bs,sub,p⟩ := ih (fun a ha => ok _ (.tail _ ha)) h2
    refine ⟨?_,ys::bs,by simp [List.mapM_cons,found,sub],?_⟩
    · intro y hy
      rcases List.mem_append.mp hy with h | h
      · exact valid y h
      · exact tail y h
    · simpa using perm.append p

/-- Transport a completed finite traversal to any sufficient fuel. Neighbor
lists need agree only up to permutation at each actual expansion. -/
private theorem layers_move {α β γ : Type} (image : α → β) (value : β → γ) (dom : α → Prop)
    {native : α → Option (List α)} {other : β → Option (List β)}
    (step : ∀ x, dom x → ∀ xs, native x = some xs →
      (∀ y ∈ xs, dom y) ∧ ∃ ys, other (image x) = some ys ∧ (xs.map image).Perm ys)
    (n : Nat) {m : Nat} (enough : n ≤ m) {xs ys rows}
    (matchRow : (xs.map image).Perm ys) (ok : ∀ x ∈ xs, dom x)
    (hit : layers? native n xs = some rows) :
    (layers? other m ys).map (List.map fun row => (↑(row.map value) : Multiset γ)) =
      some (rows.map (fun row => (↑(row.map (value ∘ image)) : Multiset γ))) := by
  induction n generalizing xs ys rows m with
  | zero =>
    cases xs with
    | nil => obtain rfl := matchRow.nil_eq; cases Option.some.inj hit; cases m <;> rfl
    | cons => contradiction
  | succ n ih =>
    cases m with
    | zero => omega
    | succ m =>
      cases xs with
      | nil => obtain rfl := matchRow.nil_eq; cases Option.some.inj hit; rfl
      | cons x xs =>
        cases ys with
        | nil => have := matchRow.length_eq; simp at this
        | cons y ys =>
          simp only [layers?] at hit ⊢
          obtain ⟨blocks,hb,tailHit⟩ := Option.bind_eq_some_iff.mp hit
          obtain ⟨tail,ht,eq⟩ := Option.bind_eq_some_iff.mp tailHit
          cases Option.some.inj eq
          obtain ⟨valid,bs,mapped,per⟩ := moveRow image dom step ok hb
          obtain ⟨cs,actual,pc⟩ := mapM_perm matchRow.symm mapped
          have restEq :=  ih (by omega : n ≤ m) (per.trans pc.flatten.symm) valid ht
          rw [actual]
          cases found : layers? other m cs.flatten with
          | none => simp [found] at restEq
          | some rest =>
            have eqns := Option.some.inj (by simpa [found] using restEq)
            have row := matchRow.map value
            rw [List.map_map] at row
            change (Option.map (List.map _) ((layers? other m cs.flatten).bind
              (fun rs => some ((y :: ys) :: rs)))) = _
            rw [found]
            change some (_ :: _) = some (_ :: _)
            congr 2
            · exact Quot.sound row.symm

/-- The domain is closed under actual children. The raw graph has exactly
those children up to permutation, and the two observations agree at each
reached cursor. No comparison of already assembled inventories is assumed. -/
structure Model {i : Input} (r : Reader i) (rev : Bool) (os : List RingRetainedStereoRefinement.Observation)
    (loc : Arm i → Edge) (kids : Edge → List Edge) (rank : Edge → Option (List Word))
    (get : History → Cell) (dom : Arm i → Prop) : Prop where
  closed : ∀ q, dom q → ∀ c ∈ i.certified.executableLocalizedRerootChildren q, dom c
  children : ∀ q, dom q → ((i.certified.executableLocalizedRerootChildren q).map loc).Perm (kids (loc q))
  earlier : ∀ q, dom q → rank (loc q) = (RingRetainedStereoRefinement.priority i r rev os q).map RingStereoSiblingPass.Branch.deep
  labels : ∀ q, dom q → get (loc q).2 = r q.occurrence

open private map_traversal from TetraStereo.Engine.RingStereoSphereInventory

private def project {i : Input} (loc : Arm i → Edge) (v : Visit i) : Entry := (loc v.arm,v.path)

private theorem expansion {i r rev os loc kids rank get dom}
    (model : @Model i r rev os loc kids rank get dom) (v : Visit i) (ok : dom v.arm)
    (vs : List (Visit i)) (found : nextWith r rev i.certified.executableLocalizedRerootChildren
      (RingRetainedStereoRefinement.priority i r rev os) v = some vs) :
    (∀ y ∈ vs, dom y.arm) ∧ ∃ ys, next kids rank get rev (project loc v) = some ys ∧
      (vs.map (project loc)).Perm ys := by
  let cs := i.certified.executableLocalizedRerootChildren v.arm
  let raw (e : Edge) : Option Entry := do
    let k ← rank e
    return (e,v.path ++ [⟨k,hand (get e.2) rev⟩])
  unfold nextWith at found
  have tagged : (cs.map loc).mapM raw = some (vs.map (project loc)) := by
    rw [List.mapM_map]
    have eqn := congrArg (Option.map (List.map (project loc))) found
    rw [map_traversal] at eqn
    refine Eq.trans (RingFrameTransport.mapM_congr_mem _ _ _ ?_) eqn
    intro c hc
    have child := model.closed _ ok c hc
    dsimp only [raw,Function.comp_apply]
    rw [model.earlier c child,model.labels c child]
    cases RingRetainedStereoRefinement.priority i r rev os c <;> rfl
  constructor
  · intro y hy
    obtain ⟨c,hc,hit⟩ := RingRetainedUnitPass.forOutput found hy
    cases h : RingRetainedStereoRefinement.priority i r rev os c with
    | none => simp [h] at hit
    | some b =>
      cases Option.some.inj (by simpa only [h,Option.bind_some] using hit)
      exact model.closed _ ok c hc
  · obtain ⟨ys,also,perm⟩ := mapM_perm (model.children _ ok).symm tagged
    exact ⟨ys,also,perm.symm⟩

theorem inventory_exact {i r rev os loc kids rank get dom} (model : @Model i r rev os loc kids rank get dom)
    {q : Arm i} (on : dom q) {inv : Inventory} (n : Nat)
    (bound : i.certified.localizedRerootCursorBudget q + 1 ≤ n)
    (found : RingStereoSphereInventory.inventory? i r rev os q = some inv) :
    inventory kids rank get rev n (loc q) = some inv := by
  obtain ⟨rows,run,equal⟩ := Option.map_eq_some_iff.mp found
  have h := layers_move (project loc) Prod.snd (fun v => dom v.arm) (expansion model)
    _ bound (List.Perm.refl _) (by simpa only [List.mem_singleton] using
      (fun v (hv : v = start r rev q) => hv ▸ on)) run
  change (layers? _ _ [_]).map _ = _
  rw [←equal]
  simpa only [project,start,hand,RingFullPathPairs.handAt,model.labels q on,List.map_cons,List.map_nil,
    Function.comp_def,eraseVisits] using h

/-- Every completed donor sphere can be read directly from written bonds,
isotopes, and the numeric encoding of the frozen evaluator rows. -/
theorem molecular_inventory {i : Input} {f : Site i} (rows : List (Site i × Cell))
    (ready : RingGroupedStereo.Ready f (RingSphereQueue.viewOf rows))
    (rev : Bool) (os : List RingRetainedStereoRefinement.Observation) (q : Arm i)
    (valid : i.certified.LocalizedRerootCursorValid q) (on : q.occurrence.val.root = f.val.root)
    (prev : ∃ p, q.previous? = some p) {inv : Inventory}
    (found : RingStereoSphereInventory.inventory? i (RingSphereQueue.viewOf rows) rev os q = some inv) :
    let get := read (encode rows) f.val.root.val
    let n := RingHistoryDonorRanks.fuel i.molecule
    inventory (RingDeepHistoryPathOrder.children i.molecule)
      (fun e => (RingHistoryDonorRanks.rank? i.molecule get rev os n e).map RingStereoSiblingPass.Branch.deep)
      get rev n (Examples.RingDeepHistoryComparison.edge q) = some inv := by
  let dom (a : Arm i) := i.certified.LocalizedRerootCursorValid a ∧
    a.occurrence.val.root = f.val.root ∧ ∃ p, a.previous? = some p
  have seen (t : Site i) (h : t.val.root = f.val.root) :
      read (encode rows) f.val.root.val (Examples.DecalinAuxiliary.history t) = RingSphereQueue.viewOf rows t := by
    rw [← h]; exact read_exact rows t
  apply inventory_exact (dom := dom) _ (show dom q from ⟨valid,on,prev⟩) _ (RingHistoryDonorRanks.enough i q) found
  constructor
  · intro a d c hc
    have edges := i.certified.executableLocalizedRerootChildren_declarative a
    exact ⟨i.certified.localizedRerootChild_valid a c _ edges hc,
      (i.certified.localizedRerootChildren_root_eq a c _ edges hc).trans d.2.1,
      _,i.certified.executableLocalizedRerootChildren_previous a c hc⟩
  · intro a d
    obtain ⟨p,h⟩ := d.2.2
    exact Examples.RingDeepHistoryComparison.children_exact a p h d.1
  · intro a d
    obtain ⟨p,h⟩ := d.2.2
    exact congrArg (Option.map RingStereoSiblingPass.Branch.deep)
      (RingHistoryDonorRanks.exact_rank ready _ seen rev os a p h d.1 d.2.1 _ (RingHistoryDonorRanks.enough i a))
  · intro a d
    exact seen a.occurrence d.2.1

end TetraStereo.Engine.RingGraphHistoryInventory
assert_kernel_only TetraStereo.Engine.RingGraphHistoryInventory.read_exact
assert_kernel_only TetraStereo.Engine.RingGraphHistoryInventory.inventory_exact
assert_kernel_only TetraStereo.Engine.RingGraphHistoryInventory.molecular_inventory
