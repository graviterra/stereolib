import TetraStereo.Engine.RingUnitClasses

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority.InventoryPriority
open OneCenter CertifiedLocalizedCIPInput Recursive

/-- Every candidate occurrence has a position in this list. A missing
reading denotes a proposed absence, which requires its own molecular proof
when applying the parent step. -/
abbrev Entries := List (List Nat × Option Reading)

def positives (es : Entries) : Facts :=
  es.filterMap fun (p,h) => h.map (p,·)

def omissions (es : Entries) : List (List Nat) :=
  es.filterMap fun x => if x.2.isNone then some x.1 else none

/-- The selected order on each geometry is determined by the molecular
comparison. The class comparison uses all signed or absent occurrences.
Later rules use the positive entries after checking earlier equivalence. -/
inductive Decision (m : RawMolecule) (p : List Nat) (d : Nat) (f : Recursive.Frame)
    (ln rn : RawMolecule.CanonicalBranchNode) (ls rs : Entries) : Type where
  | fourA (result : UnitClasses.Decision m p d f ls rs) : Decision m p d f ln rn ls rs
  | later (x y : Bool)
      (agree : ∃ flip a b, inventory m ln (positives ls) f.stage flip f.rename = some a ∧
        inventory m rn (positives rs) f.stage false id = some b ∧ a.Perm b)
      (actual : molecularSeniorLeft? m ln rn f.stage (positives ls) (positives rs) false = some x)
      (reflected : molecularSeniorLeft? m ln rn f.stage (positives ls) (positives rs) true = some y) :
      Decision m p d f ln rn ls rs

structure Step (m : RawMolecule) (p : List Nat) (depth : Nat) (f : Recursive.Frame) (ls rs : Entries) where
  frame : frameOK m p depth f = true
  left : RawMolecule.CanonicalBranchNode
  right : RawMolecule.CanonicalBranchNode
  reachedLeft : occurrence? m (p ++ [f.left]) = some left
  reachedRight : occurrence? m (p ++ [f.right]) = some right
  leftComplete : carbonSites m (m.atomCount+1) left = some (ls.map Prod.fst)
  rightComplete : carbonSites m (m.atomCount+1) right = some (rs.map Prod.fst)
  decision : Decision m p depth f left right ls rs

def Step.orders {m p depth f ls rs} (s : Step m p depth f ls rs) : Bool × Bool :=
  match s.decision with
  | .fourA c => (c.leftSenior,c.leftSenior)
  | .later x y .. => (x,y)

def check? (m : RawMolecule) (p : List Nat) (depth : Nat) (f : Recursive.Frame) (ls rs : Entries) :
    Option (Step m p depth f ls rs) := do
  if valid : frameOK m p depth f = true then
    let ⟨ln,hl⟩ ← (occurrence? m (p ++ [f.left])).attach
    let ⟨rn,hr⟩ ← (occurrence? m (p ++ [f.right])).attach
    if lc : carbonSites m (m.atomCount+1) ln = some (ls.map Prod.fst) then
      if rc : carbonSites m (m.atomCount+1) rn = some (rs.map Prod.fst) then
        let l := positives ls
        let r := positives rs
        if let some ⟨earlier⟩ := agree? m f ln rn l r then
          -- This correspondence already preserves every earlier unit class.
          let ⟨x,hx⟩ ← (molecularSeniorLeft? m ln rn f.stage l r false).attach
          let ⟨y,hy⟩ ← (molecularSeniorLeft? m ln rn f.stage l r true).attach
          return ⟨valid,ln,rn,hl,hr,lc,rc,.later x y earlier hx hy⟩
        let c ← UnitClasses.compare? m p depth f ls rs
        return ⟨valid,ln,rn,hl,hr,lc,rc,.fourA c⟩
  none

end TetraStereo.Engine.RingChemicalPriority.InventoryPriority
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.InventoryPriority.check?
