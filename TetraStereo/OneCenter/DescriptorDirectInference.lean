import TetraStereo.OneCenter.DescriptorTaskExtraction

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace MultiCenterMolecule

/-- If an atom is one of the molecule's distinguished centers, recover it as a typed center. -/
def centerOfAtom? (m : MultiCenterMolecule V) (v : V) : Option m.Center :=
  if h : v ∈ m.centers then some ⟨v, h⟩ else none

@[simp] theorem centerOfAtom?_eq_some_of_mem
    (m : MultiCenterMolecule V) {v : V} (h : v ∈ m.centers) :
    m.centerOfAtom? v = some ⟨v, h⟩ := by
  classical
  simp [centerOfAtom?, h]

@[simp] theorem centerOfAtom?_eq_none_of_not_mem
    (m : MultiCenterMolecule V) {v : V} (h : v ∉ m.centers) :
    m.centerOfAtom? v = none := by
  classical
  simp [centerOfAtom?, h]

/-- The direct descriptor source of a ligand, when that ligand atom is itself a distinguished
stereochemical center.  This is the first graph-derived Rule-5 dependency hook: no oracle is needed
when a tied ligand points directly at another resolved center. -/
def directLigandSource? (m : MultiCenterMolecule V) (center : m.Center) (i : Fin 4) :
    Option m.Center :=
  m.centerOfAtom? (m.ligandAtomAt center i)

@[simp] theorem directLigandSource?_eq_some_of_ligandAtomAt_mem
    (m : MultiCenterMolecule V) {center : m.Center} {i : Fin 4}
    (h : m.ligandAtomAt center i ∈ m.centers) :
    m.directLigandSource? center i = some ⟨m.ligandAtomAt center i, h⟩ := by
  simp [directLigandSource?, h]

@[simp] theorem directLigandSource?_eq_none_of_ligandAtomAt_not_mem
    (m : MultiCenterMolecule V) {center : m.Center} {i : Fin 4}
    (h : m.ligandAtomAt center i ∉ m.centers) :
    m.directLigandSource? center i = none := by
  simp [directLigandSource?, h]

end MultiCenterMolecule

namespace Rule5DirectInference

variable {m : MultiCenterMolecule V} {cfg : m.Configuration}

/-- Return the first successful optional result from a candidate list. -/
def firstSome {α β : Type*} (f : α → Option β) : List α → Option β
  | [] => none
  | x :: xs =>
      match f x with
      | some y => some y
      | none => firstSome f xs

@[simp] theorem firstSome_nil {α β : Type*} (f : α → Option β) :
    firstSome f [] = none :=
  rfl

@[simp] theorem firstSome_cons_some {α β : Type*} (f : α → Option β)
    {x : α} {xs : List α} {y : β} (h : f x = some y) :
    firstSome f (x :: xs) = some y := by
  simp [firstSome, h]

@[simp] theorem firstSome_cons_none {α β : Type*} (f : α → Option β)
    {x : α} {xs : List α} (h : f x = none) :
    firstSome f (x :: xs) = firstSome f xs := by
  simp [firstSome, h]

theorem firstSome_eq_some_mem {α β : Type*} {f : α → Option β}
    {xs : List α} {y : β} (h : firstSome f xs = some y) :
    ∃ x, x ∈ xs ∧ f x = some y := by
  induction xs with
  | nil =>
      simp at h
  | cons x xs ih =>
      cases hx : f x with
      | none =>
          rcases ih (by simpa [firstSome, hx] using h) with ⟨x', hxmem, hx'⟩
          exact ⟨x', by simp [hxmem], hx'⟩
      | some y' =>
          have hy : y' = y := by
            simpa [firstSome, hx] using h
          subst y'
          exact ⟨x, by simp, hx⟩



def directRule5TaskSpec? (center : m.Center) (left right : Fin 4) :
    Option (Rule5TaskSpec m cfg center) :=
  match m.directLigandSource? center left, m.directLigandSource? center right with
  | some leftSource, some rightSource =>
      if h :
          cipTraceOutcome
            (CIPRuleEngine.compareKeyTrace
              (m.cipKeyDescriptorAt center left)
              (m.cipKeyDescriptorAt center right)) = Ordering.eq then
        some
          { leftLigand := left
            rightLigand := right
            leftSource := leftSource
            rightSource := rightSource
            keyTie := h }
      else
        none
  | _, _ => none

/-- The unordered ligand pairs searched by the direct Rule-5 selector. -/
def directRule5PairCandidates : List (Fin 4 × Fin 4) :=
  [((0 : Fin 4), (1 : Fin 4)), ((0 : Fin 4), (2 : Fin 4)),
    ((0 : Fin 4), (3 : Fin 4)), ((1 : Fin 4), (2 : Fin 4)),
    ((1 : Fin 4), (3 : Fin 4)), ((2 : Fin 4), (3 : Fin 4))]




def directRule5TaskSelector (m : MultiCenterMolecule V) (cfg : m.Configuration) :
    Rule5TaskSelector m cfg where
  spec? := fun center =>
    firstSome
      (fun pair =>
        directRule5TaskSpec? (m := m) (cfg := cfg) center pair.1 pair.2)
      directRule5PairCandidates

end Rule5DirectInference

export Rule5DirectInference
  (firstSome firstSome_eq_some_mem directRule5TaskSpec? directRule5PairCandidates
    directRule5TaskSelector)

end
end OneCenter
end TetraStereo
