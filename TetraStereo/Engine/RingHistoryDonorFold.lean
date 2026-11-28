import TetraStereo.Engine.RingFullPathEligibility

/-! Lift unordered physical history children and frozen publications through every
cumulative stereochemical sibling pass, including tied shallow and deep orders. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingHistoryDonorFold
open OneCenter RingStereoSiblingPass
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm)
open RingNestedActivePair (Reader Labels unit)
open RingRetainedChemicalTrace (Key Framed)
open RingRetainedStereoRefinement (Observation Derives)
open private mapM_perm from TetraStereo.Engine.RingActivePairs

structure Model (α : Type) where
  children : α → List α
  constitution : α → Option Key
  read : α → Option (Option Labels)

def fold {α : Type} (children : α → List α) (head : α → Option Branch) : Nat → α → Option Branch
  | 0,_ => none
  | n+1,q => do
    let h ← head q
    let cs ← (children q).mapM (fold children head n)
    return {h with levels := rows (order Branch.shallow cs) (order Branch.deep cs)}

def rank {α : Type} (m : Model α) (rev : Bool) (fuel : Nat) : List Observation → α → Option Branch
  | [] => fold m.children (fun q => do
      let k ← m.constitution q
      let v ← m.read q
      return RingRetainedUnitPass.branch k (unit (v.map fun p => if rev then p.2 else p.1)) [] []) fuel
  | o::os => fold m.children (fun q => do
      let before ← rank m rev fuel os q
      let v ← m.read q
      return RingRetainedStereoRefinement.extend before (o.value v rev) [] []) fuel

structure Corresponds {α : Type} (m : Model α) {i : Input} (read : Reader i)
    (image : Arm i → α) (domain : Arm i → Prop) : Prop where
  valid : ∀ q, domain q → i.certified.LocalizedRerootCursorValid q
  closed : ∀ q, domain q → ∀ c ∈ i.certified.executableLocalizedRerootChildren q, domain c
  children : ∀ q, domain q →
    ((i.certified.executableLocalizedRerootChildren q).map image).Perm (m.children (image q))
  constitution : ∀ q, domain q → m.constitution (image q) = RingRetainedChemicalTrace.key? i q
  read_eq : ∀ q, domain q → m.read (image q) = read q.occurrence

private theorem mapped {α β γ : Type} {f : α → Option γ} {g : β → Option γ} {image : α → β}
    {xs : List α} {ys : List γ} (got : xs.mapM f = some ys)
    (agree : ∀ a ∈ xs, ∀ b, f a = some b → g (image a) = some b) :
    (xs.map image).mapM g = some ys := by
  induction xs generalizing ys with
  | nil => simpa using got
  | cons x xs ih =>
    simp only [List.mapM_cons] at got
    obtain ⟨b,hb,t⟩ := Option.bind_eq_some_iff.mp got
    obtain ⟨bs,hbs,t⟩ := Option.bind_eq_some_iff.mp t
    cases Option.some.inj t
    simp [List.mapM_cons,agree x (by simp) b hb,ih hbs (fun a ha => agree a (by simp [ha]))]

private theorem framed {α : Type} (children : α → List α) (head : α → Option Branch) :
    ∀ n q b, fold children head n q = some b → Framed 2 b.levels
  | 0,_,_,h => by contradiction
  | n+1,q,b,h => by
    unfold fold at h
    obtain ⟨hd,_,t⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨cs,hcs,t⟩ := Option.bind_eq_some_iff.mp t
    cases Option.some.inj t
    apply rows_framed (legal_order ..).perm (legal_order ..).perm
    intro c hc
    obtain ⟨a,_,ha⟩ := RingRetainedUnitPass.forOutput hcs hc
    exact framed children head n a c ha

private theorem evaluate {α : Type} {m : Model α} {i : Input} {read : Reader i}
    {image : Arm i → α} {domain : Arm i → Prop} (model : Corresponds m read image domain)
    (D : Arm i → Branch → Prop) (head : α → Option Branch)
    (step : ∀ q b, domain q → D q b → ∃ h cs sh de, ∃ (lookup : Arm i → Option Branch),
      head (image q) = some h ∧ (i.certified.executableLocalizedRerootChildren q).mapM lookup = some cs ∧
      (∀ c ∈ i.certified.executableLocalizedRerootChildren q, ∀ z, lookup c = some z → D c z) ∧
      Legal Branch.shallow cs sh ∧ Legal Branch.deep cs de ∧ b = {h with levels := rows sh de}) :
    ∀ n q b, domain q → i.certified.localizedRerootCursorBudget q < n → D q b →
      fold m.children head n (image q) = some b := by
  intro n
  induction n with
  | zero => intros; omega
  | succ n ih =>
    intro q b dom fuel deriv
    obtain ⟨h,cs,sh,de,lookup,hh,hcs,sub,hs,hd,rfl⟩ := step q b dom deriv
    have seen := mapped (image := image) (g := fold m.children head n) hcs (by
      intro c hc z hz
      have lt := i.certified.localizedRerootChild_budget_lt q c _ (model.valid q dom)
        (i.certified.executableLocalizedRerootChildren_declarative q) hc
      exact ih c z (model.closed q dom c hc) (by omega) (sub c hc z hz))
    obtain ⟨out,got,perm⟩ := mapM_perm (model.children q dom).symm seen
    have sh' := legal_order Branch.shallow out
    have de' := legal_order Branch.deep out
    have eqn := rows_unique hs hd
      (⟨sh'.perm.trans perm,sh'.descending⟩ : Legal Branch.shallow cs _)
      (⟨de'.perm.trans perm,de'.descending⟩ : Legal Branch.deep cs _) (by
        intro z hz
        obtain ⟨a,_,ha⟩ := RingRetainedUnitPass.forOutput got (perm.mem_iff.mpr hz)
        exact framed _ _ _ _ _ ha)
    simp [fold,hh,got,←eqn]

theorem rank_of_derives {α : Type} {m : Model α} {i : Input} {read : Reader i}
    {image : Arm i → α} {domain : Arm i → Prop} (model : Corresponds m read image domain)
    (rev : Bool) : ∀ os n q b, domain q → i.certified.localizedRerootCursorBudget q < n →
      Derives i read rev os q b → rank m rev n os (image q) = some b := by
  intro os
  induction os with
  | nil =>
    intro n q b dom enough deriv
    apply evaluate model (RingRetainedUnitPass.Reading i read rev) _ _ n q b dom enough deriv
    intro a z d h
    cases h with
    | @node _ k v _ _ _ hk hv _ lookup cs sub sh de =>
      exact ⟨RingRetainedUnitPass.branch k (unit (v.map fun p => if rev then p.2 else p.1)) [] [],_,_,_,lookup,by simp [model.constitution a d,hk,model.read_eq a d,hv],cs,
        fun c hc z hz => sub c hc hz,sh,de,rfl⟩
  | cons o os ih =>
    intro n q b dom enough deriv
    let within (a : Arm i) := domain a ∧ i.certified.localizedRerootCursorBudget a < n
    have submodel : Corresponds m read image within := {model with
      valid := fun a h => model.valid a h.1
      closed := fun a h c hc => ⟨model.closed a h.1 c hc,lt_trans
        (i.certified.localizedRerootChild_budget_lt a c _ (model.valid a h.1)
          (i.certified.executableLocalizedRerootChildren_declarative a) hc) h.2⟩
      children := fun a h => model.children a h.1
      constitution := fun a h => model.constitution a h.1
      read_eq := fun a h => model.read_eq a h.1}
    apply evaluate submodel (Derives i read rev (o::os)) _ _ n q b ⟨dom,enough⟩ enough deriv
    intro a z d h
    cases h with
    | @node _ p v _ _ _ prev seen lookup cs sub sh de =>
      exact ⟨RingRetainedStereoRefinement.extend p (o.value v rev) [] [],_,_,_,lookup,by simp [ih n a _ d.1 d.2 prev,model.read_eq a d.1,seen],cs,
        fun c hc z hz => sub c hc hz,sh,de,rfl⟩

end TetraStereo.Engine.RingHistoryDonorFold
assert_kernel_only TetraStereo.Engine.RingHistoryDonorFold.rank_of_derives
