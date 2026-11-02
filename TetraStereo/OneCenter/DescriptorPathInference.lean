import TetraStereo.OneCenter.DescriptorDirectInference

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace MultiCenterMolecule

/-- Recover a distinguished center from an atom, but reject the target center itself.  Branch
walking uses this to avoid treating a return to the queried stereocenter as a descriptor source. -/
def centerOfAtomExcept? (m : MultiCenterMolecule V) (target : m.Center) (v : V) :
    Option m.Center :=
  match m.centerOfAtom? v with
  | some source => if source = target then none else some source
  | none => none

@[simp] theorem centerOfAtomExcept?_eq_none_of_not_mem
    (m : MultiCenterMolecule V) (target : m.Center) {v : V} (h : v ∉ m.centers) :
    m.centerOfAtomExcept? target v = none := by
  simp [centerOfAtomExcept?, h]

@[simp] theorem centerOfAtomExcept?_eq_none_self
    (m : MultiCenterMolecule V) (target : m.Center) :
    m.centerOfAtomExcept? target target.1 = none := by
  simp [centerOfAtomExcept?, target.2]

@[simp] theorem centerOfAtomExcept?_eq_some_of_mem_ne
    (m : MultiCenterMolecule V) (target : m.Center) {v : V}
    (hmem : v ∈ m.centers) (hne : (⟨v, hmem⟩ : m.Center) ≠ target) :
    m.centerOfAtomExcept? target v = some ⟨v, hmem⟩ := by
  simp [centerOfAtomExcept?, hmem, hne]

/-- The root node for walking outward along a ligand branch.  It starts at the ligand atom and
remembers the queried stereocenter as both parent and already-seen atom. -/
def branchRootState (m : MultiCenterMolecule V) (center : m.Center) (i : Fin 4) :
    MoleculeGraph.CIPState V where
  parent := center.1
  current := m.ligandAtomAt center i
  seen := {center.1}

/-- The branch frontier after `depth` cycle-cut expansion steps from one ligand. -/
def branchFrontier (m : MultiCenterMolecule V) (center : m.Center) (i : Fin 4)
    (depth : ℕ) : List (MoleculeGraph.CIPState V) :=
  m.mol.cycleCutFrontier depth [m.branchRootState center i]

/-- Search one frontier layer for a distinguished source center. -/
def branchSourceAtDepth? (m : MultiCenterMolecule V) (center : m.Center) (i : Fin 4)
    (depth : ℕ) : Option m.Center :=
  firstSome
    (fun state : MoleculeGraph.CIPState V =>
      m.centerOfAtomExcept? center state.current)
    (m.branchFrontier center i depth)

@[simp] theorem branchSourceAtDepth?_zero
    (m : MultiCenterMolecule V) (center : m.Center) (i : Fin 4) :
    m.branchSourceAtDepth? center i 0 =
      m.centerOfAtomExcept? center (m.ligandAtomAt center i) := by
  cases h : m.centerOfAtomExcept? center (m.ligandAtomAt center i) <;>
    simp [branchSourceAtDepth?, branchFrontier, branchRootState, MoleculeGraph.cycleCutFrontier,
      firstSome, h]

/-- Search a branch by increasing frontier depth, starting at `depth` and taking at most `fuel`
more expansion steps. -/
def branchSourceFrom? (m : MultiCenterMolecule V) (center : m.Center) (i : Fin 4)
    (depth : ℕ) : ℕ → Option m.Center
  | 0 => m.branchSourceAtDepth? center i depth
  | fuel + 1 =>
      match m.branchSourceAtDepth? center i depth with
      | some source => some source
      | none => m.branchSourceFrom? center i (depth + 1) fuel

/-- Search the branch by increasing frontier depth up to the supplied fuel. -/
def branchSourceWithin? (m : MultiCenterMolecule V) (center : m.Center) (i : Fin 4)
    (fuel : ℕ) : Option m.Center :=
  m.branchSourceFrom? center i 0 fuel

@[simp] theorem branchSourceWithin?_zero
    (m : MultiCenterMolecule V) (center : m.Center) (i : Fin 4) :
    m.branchSourceWithin? center i 0 = m.branchSourceAtDepth? center i 0 :=
  rfl

theorem branchSourceWithin?_eq_some_of_depth_zero
    (m : MultiCenterMolecule V) (center : m.Center) (i : Fin 4) (fuel : ℕ)
    {source : m.Center}
    (hzero : m.branchSourceAtDepth? center i 0 = some source) :
    m.branchSourceWithin? center i fuel = some source := by
  cases fuel <;> simp [branchSourceWithin?, branchSourceFrom?, hzero]

theorem branchSourceWithin?_one_eq_some_of_zero_none
    (m : MultiCenterMolecule V) (center : m.Center) (i : Fin 4) {source : m.Center}
    (hzero : m.branchSourceAtDepth? center i 0 = none)
    (hone : m.branchSourceAtDepth? center i 1 = some source) :
    m.branchSourceWithin? center i 1 = some source := by
  simp [branchSourceWithin?, branchSourceFrom?, hzero, hone]

/-- Default branch-source search.  The fuel `Fintype.card V` is enough to cover every simple
finite branch before cycle-cut expansion can only revisit already-seen atoms. -/
def branchSource? (m : MultiCenterMolecule V) (center : m.Center) (i : Fin 4) :
    Option m.Center :=
  m.branchSourceWithin? center i (Fintype.card V)

/-- A proof-facing witness that the branch walker found `source` at a concrete frontier depth. -/
def BranchSourceFoundWithin (m : MultiCenterMolecule V) (center : m.Center) (i : Fin 4)
    (fuel : ℕ) (source : m.Center) : Prop :=
  ∃ depth, depth ≤ fuel ∧
    ∃ state, state ∈ m.branchFrontier center i depth ∧
      m.centerOfAtomExcept? center state.current = some source

end MultiCenterMolecule

namespace Rule5PathInference

variable {m : MultiCenterMolecule V} {cfg : m.Configuration}



def pathRule5TaskSpecWithin? (center : m.Center) (left right : Fin 4) (fuel : ℕ) :
    Option (Rule5TaskSpec m cfg center) :=
  match m.branchSourceWithin? center left fuel, m.branchSourceWithin? center right fuel with
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


def pathRule5TaskSpec? (center : m.Center) (left right : Fin 4) :
    Option (Rule5TaskSpec m cfg center) :=
  pathRule5TaskSpecWithin? (m := m) (cfg := cfg) center left right (Fintype.card V)

/-- Branch-walking Rule-5 selector.  It scans ligand pairs at every center and emits the first pair
whose ordinary descriptor keys tie and whose two ligand branches lead to descriptor source centers. -/
def pathRule5TaskSelector (m : MultiCenterMolecule V) (cfg : m.Configuration) :
    Rule5TaskSelector m cfg where
  spec? := fun center =>
    firstSome
      (fun pair =>
        pathRule5TaskSpec? (m := m) (cfg := cfg) center pair.1 pair.2)
      directRule5PairCandidates

/-- Fuel-bounded branch-walking Rule-5 selector, useful for examples and staged searches. -/
def pathRule5TaskSelectorWithin (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (fuel : ℕ) : Rule5TaskSelector m cfg where
  spec? := fun center =>
    firstSome
      (fun pair =>
        pathRule5TaskSpecWithin? (m := m) (cfg := cfg) center pair.1 pair.2 fuel)
      directRule5PairCandidates

end Rule5PathInference

export Rule5PathInference
  (pathRule5TaskSpecWithin? pathRule5TaskSpec? pathRule5TaskSelector
    pathRule5TaskSelectorWithin)

end
end OneCenter
end TetraStereo
