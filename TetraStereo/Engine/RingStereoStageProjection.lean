import TetraStereo.Engine.RingStereoSphereInventory

/-! A successful through-4c inventory contains the through-4a inventory.
Projection removes the last earlier-rule word at every edge, retaining hands,
occurrences and multiplicities. No converse success implication is assumed. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingStereoStageProjection
open OneCenter
open RingStereoSphereInventory
open RingStereoSiblingPass (Branch)
open RingActivePairs (Arm)
open RingNestedActivePair (Reader)
open LocalizedChemicalRing (Input)
open RingUnorderedSphereReading (layers?)
open private start nextWith eraseVisits from TetraStereo.Engine.RingStereoSphereInventory

def edge (e : Edge) : Edge := ⟨e.earlier.dropLast, e.hand⟩
def path (p : SignedPath) : SignedPath := p.map edge
def inventory (s : Inventory) : Inventory := s.map (Multiset.map path)
private def visit {i : Input} (v : Visit i) : Visit i := ⟨v.arm,path v.path⟩

private theorem mapM_success {α β γ : Type} (f : α → Option β) (g : α → Option γ)
    (image : β → γ) (same : ∀ a b, f a = some b → g a = some (image b)) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = some ys → xs.mapM g = some (ys.map image) := by
  intro xs
  induction xs with
  | nil => intro ys h; cases h; rfl
  | cons x xs ih =>
    intro ys h
    simp only [List.mapM_cons] at h ⊢
    obtain ⟨b,hb,t⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨bs,hbs,out⟩ := Option.bind_eq_some_iff.mp t
    obtain rfl := Option.some.inj out
    rw [same x b hb,ih bs hbs]
    rfl

private theorem rank_projects (i : Input) (r : Reader i) (rev : Bool) (q : Arm i)
    (b : Branch) (h : RingRetainedStereoRefinement.priority i r rev [.lowercase] q = some b) :
    ∃ a, RingRetainedStereoRefinement.priority i r rev [] q = some a ∧ b.deep.dropLast = a.deep := by
  unfold RingRetainedStereoRefinement.priority at h
  simp only [RingRetainedStereoRefinement.build] at h
  obtain ⟨a,ha,t⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨v,hv,t⟩ := Option.bind_eq_some_iff.mp t
  obtain ⟨cs,hcs,out⟩ := Option.bind_eq_some_iff.mp t
  obtain rfl := Option.some.inj out
  exact ⟨a,ha,by simp [RingRetainedStereoRefinement.extend,Branch.deep]⟩

private theorem next_projects {i : Input} (r : Reader i) (rev : Bool) (v : Visit i)
    (out : List (Visit i))
    (h : nextWith r rev i.certified.executableLocalizedRerootChildren
      (RingRetainedStereoRefinement.priority i r rev [.lowercase]) v = some out) :
    nextWith r rev i.certified.executableLocalizedRerootChildren
      (RingRetainedStereoRefinement.priority i r rev []) (visit v) = some (out.map visit) := by
  apply mapM_success _ _ visit ?_ _ _ h
  intro c b hb
  obtain ⟨k,hk,t⟩ := Option.bind_eq_some_iff.mp hb
  obtain rfl := Option.some.inj t
  obtain ⟨a,ha,eqn⟩ := rank_projects i r rev c k hk
  change (RingRetainedStereoRefinement.priority i r rev [] c).bind _ = _
  rw [ha]
  simp [visit,path,edge,eqn]

private theorem layers_success {α β : Type} (f : α → Option (List α))
    (g : β → Option (List β)) (image : α → β)
    (same : ∀ a bs, f a = some bs → g (image a) = some (bs.map image)) :
    ∀ n xs rows, layers? f n xs = some rows →
      layers? g n (xs.map image) = some (rows.map (List.map image)) := by
  intro n
  induction n with
  | zero =>
    intro xs rows h
    cases xs with
    | nil => cases h; rfl
    | cons x xs => contradiction
  | succ n ih =>
    intro xs rows h
    cases xs with
    | nil => cases h; rfl
    | cons x xs =>
      simp only [layers?] at h
      obtain ⟨bs,hbs,t⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨rs,hrs,out⟩ := Option.bind_eq_some_iff.mp t
      obtain rfl := Option.some.inj out
      have mapped := mapM_success f (g ∘ image) (List.map image) same (x::xs) bs hbs
      rw [← List.mapM_map] at mapped
      have tail := ih _ _ hrs
      simp only [List.map_cons] at mapped
      simp only [List.map_cons,layers?,mapped]
      change (do
        let ts ← layers? g n (bs.map (List.map image)).flatten
        pure ((image x :: xs.map image) :: ts)) = _
      rw [← List.map_flatten]
      rw [tail]
      rfl

/-- Successful finer traversal implies successful coarser traversal. This
covers arbitrary readers; a failed finer traversal says nothing about the base. -/
theorem inventory_projects (i : Input) (r : Reader i) (rev : Bool) (q : Arm i)
    (fine : Inventory) (h : inventory? i r rev [.lowercase] q = some fine) :
    inventory? i r rev [] q = some (inventory fine) := by
  unfold inventory? inventoryWith at h ⊢
  obtain ⟨rows,hr,out⟩ := Option.map_eq_some_iff.mp h
  obtain rfl := out
  have run := layers_success _ _ visit (next_projects r rev)
    (i.certified.localizedRerootCursorBudget q + 1) [start r rev q] rows hr
  have root : visit (start r rev q) = start r rev q := rfl
  simp only [List.map_cons,List.map_nil,root] at run
  rw [run]
  simp [inventory,eraseVisits,visit,path,List.map_map,Multiset.map_coe,Function.comp_def]

/-- Compute the ordinary trial key from one fine sphere expansion. Top-level
ranks are still checked separately, preserving their failure behavior. -/
def key? (i : Input) (r : Reader i) (rev : Bool) (q : Arm i) : Option RingFullPathEligibility.Key := do
  let u ← RingRetainedStereoRefinement.priority i r rev [] q
  let l ← RingRetainedStereoRefinement.priority i r rev [.lowercase] q
  let f ← inventory? i r rev [.lowercase] q
  let b := inventory f
  return ⟨u.deep,max (reading .R b) (reading .S b),l.word,reading .R f⟩

/-- Failure and success agree with the existing complete ordinary key. -/
theorem key_exact (i : Input) (r : Reader i) (rev : Bool) (q : Arm i) :
    key? i r rev q = RingFullPathEligibility.key? i r rev q := by
  rw [← RingStereoSphereInventory.key_exact]
  unfold key? RingStereoSphereInventory.key?
  cases hu : RingRetainedStereoRefinement.priority i r rev [] q with
  | none => rfl
  | some u =>
    cases hl : RingRetainedStereoRefinement.priority i r rev [.lowercase] q with
    | none => rfl
    | some l =>
      cases hf : inventory? i r rev [.lowercase] q with
      | none =>
        cases inventory? i r rev [] q <;> rfl
      | some fine => rw [inventory_projects i r rev q fine hf]; rfl

end TetraStereo.Engine.RingStereoStageProjection
assert_kernel_only TetraStereo.Engine.RingStereoStageProjection.inventory_projects
assert_kernel_only TetraStereo.Engine.RingStereoStageProjection.key_exact
