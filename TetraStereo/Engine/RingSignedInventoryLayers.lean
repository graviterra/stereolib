import TetraStereo.Engine.RingStereoSphereInventory
import TetraStereo.Engine.RingRule5Tie

set_option autoImplicit false
namespace TetraStereo.Engine.RingSignedInventoryLayers
open OneCenter RingStereoSiblingPass RingFullPathPairs RingRule5SeedExchange
open RingStereoSphereInventory
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm)
open RingNestedActivePair (Reader)
open RingRetainedReferenceGroup (Path)
open private image start nextWith eraseVisits next_projects from TetraStereo.Engine.RingStereoSphereInventory
open private mapM_image order_perm from TetraStereo.Engine.RingUnorderedSphereReading
open private mapM_perm from TetraStereo.Engine.RingActivePairs
open private mapM_related forall2_functional from TetraStereo.Engine.RingFullPathPairs
open private recover root_good from TetraStereo.Engine.RingRule5Tie

/-- Canonically sorted complete paths of a signed sphere. -/
def projectRow (s : RS) (row : Multiset SignedPath) : List Path :=
  Quotient.liftOn row (fun xs => order id (xs.map (project s)))
    (fun _ _ p => order_perm (p.map _))

def projectInventory (s : RS) (rows : Inventory) : List (List Path) := rows.map (projectRow s)

private theorem edge_injective (s : RS) :
    Function.Injective (fun e : Edge => stepKey e.earlier (e.hand.map (· == s))) := by
  intro a b h
  have earlier : a.earlier = b.earlier := by
    simpa only [stripBit_step] using congrArg stripBit h
  have marked : a.hand.map (· == s) = b.hand.map (· == s) := by
    have e := congrArg (fun x => bitOf ([] ++ [x])) h
    simpa only [bitOf_snoc] using e
  have hands : a.hand = b.hand := by
    have decode (x y : Option RS) (same : x.map (· == s) = y.map (· == s)) : x = y := by
      rcases x with _ | (h | h) <;> rcases y with _ | (h | h) <;> cases s <;> simp_all
    exact decode _ _ marked
  cases a; cases b
  simp_all

theorem project_injective (s : RS) : Function.Injective (project s) :=
  List.map_injective_iff.mpr (edge_injective s)

theorem projectRow_injective (s : RS) : Function.Injective (projectRow s) := by
  intro a b h
  induction a using Quotient.inductionOn with
  | _ xs =>
    induction b using Quotient.inductionOn with
    | _ ys =>
      change order id (xs.map (project s)) = order id (ys.map (project s)) at h
      have p := (legal_order id (xs.map (project s))).perm.symm.trans
        ((List.Perm.of_eq h).trans (legal_order id (ys.map (project s))).perm)
      exact Quot.sound ((List.map_perm_map_iff (project_injective s)).mp p)

theorem projectInventory_injective (s : RS) : Function.Injective (projectInventory s) :=
  List.map_injective_iff.mpr (projectRow_injective s)

private theorem layers_record {α β κ : Type} [LinearOrder κ]
    (image : α → β) (key : β → κ) (edges : α → Option (List α))
    (next : β → Option (List β)) (E : β → List β → Prop)
    (commute : ∀ x, (edges x).map (List.map image) = next (image x))
    (sound : ∀ b ys, next b = some ys → E b ys)
    (functional : ∀ b xs ys, E b xs → E b ys → xs = ys)
    {row out rows} (record : Layers key E row out rows) :
    ∀ n raw rs, RingUnorderedSphereReading.layers? edges n raw = some rs →
      (raw.map image).Perm row → (row.map key).Pairwise (· ≥ ·) →
      rs.map (fun xs => order id ((xs.map image).map key)) = rows := by
  induction record with
  | stop =>
    intro n raw rs found perm _
    have empty : raw = [] := List.map_eq_nil_iff.mp perm.eq_nil
    subst raw
    have eqn : rs = [] := Option.some.inj (by simpa [RingUnorderedSphereReading.layers?] using found.symm)
    subst rs
    rfl
  | @sphere b row blocks nextRow rest rows grown sorted tail ih =>
    intro n raw rs found perm desc
    cases raw with
    | nil => simp at perm
    | cons a raw =>
      cases n with
      | zero => simp [RingUnorderedSphereReading.layers?] at found
      | succ n =>
        simp only [RingUnorderedSphereReading.layers?] at found
        obtain ⟨bs,hbs,more⟩ := Option.bind_eq_some_iff.mp found
        obtain ⟨ts,hts,result⟩ := Option.bind_eq_some_iff.mp more
        obtain rfl := Option.some.inj result
        have mapped := mapM_image image edges next commute (a::raw)
        rw [hbs] at mapped
        obtain ⟨cs,hcs,pcs⟩ := mapM_perm perm.symm mapped.symm
        have actual : List.Forall₂ E (b::row) cs := mapM_related sound hcs
        have eqn := forall2_functional functional actual grown
        subst cs
        have flat : (bs.flatten.map image).Perm nextRow := by
          have p := pcs.symm.flatten
          rw [← List.map_flatten] at p
          exact p.trans sorted.perm.symm
        have head : order id (((a::raw).map image).map key) = (b::row).map key := by
          have legal := legal_order id (((a::raw).map image).map key)
          exact List.Perm.eq_of_pairwise (fun _ _ _ _ ab ba => le_antisymm ba ab)
            (by simpa using legal.descending) desc
            (by simpa using legal.perm.trans (perm.map key))
        exact congrArg₂ List.cons head (ih n _ _ hts flat sorted.descending)

/-- Every successful raw inventory gives the complete recorded paths in any
legal native walk, including all neutral occurrences and all multiplicities. -/
theorem inventory_layers {i : Input} (r : Reader i) (rev : Bool)
    (stages : List RingRetainedStereoRefinement.Observation) (s : RS) (q : Arm i)
    {inv : Inventory} (found : inventory? i r rev stages q = some inv)
    {out rows} (record : Layers FullVisit.path
      ((stage i r rev stages).Expansion (likeAt i r rev s))
      [Oracle.root (likeAt i r rev s) q] out rows) :
    projectInventory s inv = rows := by
  unfold inventory? inventoryWith at found
  obtain ⟨rs,hrs,rfl⟩ := Option.map_eq_some_iff.mp found
  have h := layers_record (image s) FullVisit.path
    (nextWith r rev i.certified.executableLocalizedRerootChildren (stage i r rev stages).rank?)
    ((stage i r rev stages).next? (likeAt i r rev s))
    ((stage i r rev stages).Expansion (likeAt i r rev s))
    (next_projects (stage i r rev stages) r rev s)
    ((stage i r rev stages).next_sound (likeAt i r rev s))
    ((stage i r rev stages).expansion_functional (likeAt i r rev s)) record _ _ rs hrs
    (by exact List.Perm.refl _) (by simp)
  simp only [projectInventory,eraseVisits,List.map_map,Function.comp_def]
  simpa only [projectRow,Quotient.liftOn,Multiset.lift_coe,List.map_map,Function.comp_def,image] using h

/-- Equal complete recorded paths for one seed determine the signed inventory. -/
theorem inventory_eq_of_layers {i j : Input} {r : Reader i} {t : Reader j} {rev mir : Bool}
    {stages : List RingRetainedStereoRefinement.Observation} {s : RS} {q : Arm i} {p : Arm j}
    {xs ys : Inventory} (left : inventory? i r rev stages q = some xs)
    (right : inventory? j t mir stages p = some ys) {out out' rows}
    (a : Layers FullVisit.path ((stage i r rev stages).Expansion (likeAt i r rev s))
      [Oracle.root (likeAt i r rev s) q] out rows)
    (b : Layers FullVisit.path ((stage j t mir stages).Expansion (likeAt j t mir s))
      [Oracle.root (likeAt j t mir s) p] out' rows) : xs = ys :=
  projectInventory_injective s ((inventory_layers r rev stages s q left a).trans
    (inventory_layers t mir stages s p right b).symm)

/-- A through-4c tie and one tied fixed-R word recover the entire raw signed
inventory, including neutral vertices and the signed history of every path. -/
theorem lower_inventory_eq {i : Input} {f : RingActivePairs.Site i} {r : Reader i} {rev : Bool}
    (ready : RingGroupedStereo.Ready f r) {a b : Arm i}
    (va : RingRule5Shape.Valid a) (vb : RingRule5Shape.Valid b)
    (oa : RingRule5Shape.On f a) (ob : RingRule5Shape.On f b)
    (tie : RingRule5Shape.key i r rev a = RingRule5Shape.key i r rev b)
    {w : List Bool} (ha : RingFullPathRule5.Word i r rev .R a w)
    (hb : RingFullPathRule5.Word i r rev .R b w) :
    inventory? i r rev [.lowercase] a = inventory? i r rev [.lowercase] b := by
  have exists_inventory (q : Arm i) (vq : RingRule5Shape.Valid q) (oq : RingRule5Shape.On f q) :
      ∃ inv, inventory? i r rev [.lowercase] q = some inv := by
    obtain ⟨bits,hbits,_⟩ := RingFullPathRule5.word_exact rev
      (RingOccurrenceStereo.rank_total ready rev [.lowercase]) .R q vq oq
    have h := reading_exact i r rev [.lowercase] .R q
    change (inventory? i r rev [.lowercase] q).map (reading .R) =
      RingFullPathRule5.word? i r rev .R q at h
    rw [hbits] at h
    obtain ⟨inv,hi,_⟩ := Option.map_eq_some_iff.mp h
    exact ⟨inv,hi⟩
  obtain ⟨xs,hxs⟩ := exists_inventory a va oa
  obtain ⟨ys,hys⟩ := exists_inventory b vb ob
  obtain ⟨x,tx,hx⟩ := ha
  obtain ⟨y,ty,hy⟩ := hb
  obtain ⟨rx,lx⟩ := record tx
  obtain ⟨ry,ly⟩ := record ty
  have eqn : rx = ry := recover ready lx ly 0
    (fun _ h => List.mem_singleton.mp h ▸ root_good va oa rfl)
    (fun _ h => List.mem_singleton.mp h ▸ root_good vb ob tie.symm)
    (by simp [Oracle.root,RingRule5Shape.eraseEndpoint,stripBit_step]) (hx.symm.trans hy)
  subst ry
  have same := inventory_eq_of_layers hxs hys lx ly
  rw [hxs,hys,same]

end TetraStereo.Engine.RingSignedInventoryLayers
assert_kernel_only TetraStereo.Engine.RingSignedInventoryLayers.project_injective
assert_kernel_only TetraStereo.Engine.RingSignedInventoryLayers.inventory_layers
assert_kernel_only TetraStereo.Engine.RingSignedInventoryLayers.inventory_eq_of_layers

assert_kernel_only TetraStereo.Engine.RingSignedInventoryLayers.lower_inventory_eq
