import TetraStereo.OneCenter.LocalizedMarkedRetainedCanonicalMarker
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.LocalizedChemicalRingPromotedTransport

open LocalizedMarkedRetainedPromotedKey LocalizedMarkedRetainedCanonicalMarker
open DeclarativeCIP.PromotedCanonical

theorem mapM_available {α β : Type} (f : α → Option β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = some ys → ∀ x ∈ xs, ∃ y, f x = some y
  | [], _, _, x, member => by simp at member
  | a :: xs, ys, h, x, member => by
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, pure,
        Option.some.injEq] at h
      obtain ⟨b, hb, rest, hrest, _⟩ := h
      rcases List.mem_cons.1 member with rfl | member
      · exact ⟨b, hb⟩
      · exact mapM_available f xs rest hrest x member

private theorem mapM_forall₂ {α β : Type} (f : α → Option β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = some ys →
      List.Forall₂ (fun x y => f x = some y) xs ys
  | [], ys, h => by
      simp only [List.mapM_nil, pure, Option.some.injEq] at h
      subst h
      exact .nil
  | x :: xs, ys, h => by
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, pure,
        Option.some.injEq] at h
      obtain ⟨y, hy, rest, hrest, rfl⟩ := h
      exact .cons hy (mapM_forall₂ f xs rest hrest)

private theorem forall₂_imp_mem {α β : Type*} {R S : α → β → Prop} :
    ∀ {l : List α} {m : List β}, (∀ a ∈ l, ∀ b, R a b → S a b) →
      List.Forall₂ R l m → List.Forall₂ S l m
  | [], [], _, _ => .nil
  | a :: _, _ :: _, h, .cons hab rest =>
      .cons (h a (by simp) _ hab)
        (forall₂_imp_mem (fun x hx y hy => h x (by simp [hx]) y hy) rest)

private theorem exists_of_mem_forall₂_right {α β : Type*} {R : α → β → Prop} :
    ∀ {l : List α} {m : List β}, List.Forall₂ R l m → ∀ b ∈ m, ∃ a ∈ l, R a b
  | [], [], _, b, hb => by simp at hb
  | a :: _, _ :: _, .cons h rest, b, hb => by
      rcases List.mem_cons.1 hb with rfl | hb
      · exact ⟨a, by simp, h⟩
      · obtain ⟨a', ha', h'⟩ := exists_of_mem_forall₂_right rest b hb
        exact ⟨a', by simp [ha'], h'⟩

private theorem map_eq_of_forall₂ {α β γ : Type*} {f : α → γ} {g : β → γ} :
    ∀ {l : List α} {m : List β}, List.Forall₂ (fun a b => f a = g b) l m → l.map f = m.map g
  | [], [], _ => rfl
  | _ :: _, _ :: _, .cons h rest => by
      simp only [List.map_cons, h, map_eq_of_forall₂ rest]

/-- Project actual sorting to one independent key column, allowing equal results at different
source entries. The premises concern individual builds and ordinary comparison only. -/
theorem sorted_markers_mapM (input : CertifiedLocalizedCIPInput)
    {α P : Type} [LinearOrder P] (xs : List α)
    (f : α → Option (PromotedKey input)) (keys : List (PromotedKey input))
    (built : xs.mapM f = some keys) (prior : α → P) (fallback : P) (mark : α → MarkerKey)
    (priorCmp : ∀ a ∈ xs, ∀ b ∈ xs, ∀ ka kb, f a = some ka → f b = some kb →
      (input.compareLocalizedRerootCompoundThroughRule5 ka.prior kb.prior).ordering =
        compare (prior a) (prior b))
    (markEq : ∀ a ∈ xs, ∀ k, f a = some k → k.marker = mark a) :
    (sortKeys input keys).map PromotedKey.marker =
      (Certificate.CanonicalSphereKey.sortDesc
        (xs.map fun a => toLex (prior a, mark a))).map (fun k => (ofLex k).2) := by
  classical
  have related := mapM_forall₂ f xs keys built
  let priorOf : PromotedKey input → P := fun k =>
    if h : ∃ a ∈ xs, f a = some k then prior (Classical.choose h) else fallback
  have priorOf_eq : ∀ a ∈ xs, ∀ k, f a = some k → priorOf k = prior a := by
    intro a member k builtA
    have present : ∃ a ∈ xs, f a = some k := ⟨a, member, builtA⟩
    simp only [priorOf, dif_pos present]
    obtain ⟨member', built'⟩ := Classical.choose_spec present
    have cross := priorCmp _ member' a member k k built' builtA
    have self := priorCmp a member a member k k builtA builtA
    rw [show compare (prior a) (prior a) = .eq from compare_eq_iff_eq.2 rfl] at self
    exact compare_eq_iff_eq.1 (cross.symm.trans self)
  let φ : PromotedKey input → Lex (P × MarkerKey) := fun k => toLex (priorOf k, k.marker)
  have order : ∀ x ∈ keys, ∀ y ∈ keys, compareKeys input x y ≠ .lt ↔ φ y ≤ φ x := by
    intro x hx y hy
    obtain ⟨a, ha, builtA⟩ := exists_of_mem_forall₂_right related x hx
    obtain ⟨b, hb, builtB⟩ := exists_of_mem_forall₂_right related y hy
    simp only [φ, priorOf_eq a ha x builtA, priorOf_eq b hb y builtB]
    exact compareKeys_ne_lt_iff input x y (prior a) (prior b)
      (priorCmp a ha b hb x y builtA builtB)
  rw [sortKeys_marker_eq input keys φ (fun _ => rfl) order]
  have mapped : xs.map (fun a => toLex (prior a, mark a)) = keys.map φ := by
    apply map_eq_of_forall₂
    refine forall₂_imp_mem ?_ related
    intro a ha k hk
    simp only [φ, priorOf_eq a ha k hk, markEq a ha k hk]
  rw [mapped]

end TetraStereo.OneCenter.LocalizedChemicalRingPromotedTransport

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedTransport.sorted_markers_mapM
