import TetraStereo.Engine.RingSignedPair
import TetraStereo.Engine.RingEarlierStereoMatch

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority.DiscoveredPriority
open OneCenter Recursive InventoryPriority

/-- The list of bonds and the constitutional keys determine the position
of the tied pair among the four ligands. A stereochemical preference only
resolves that one pair. -/
def precedes {m p d} (f : SignedPair.Frame m p d) (leftWins : Bool)
    (a b : SignedPair.Row m p d) : Bool :=
  decide (b.key < a.key) || (a.key == b.key &&
    if leftWins then a.ligand == f.left.ligand && b.ligand == f.right.ligand
    else a.ligand == f.right.ligand && b.ligand == f.left.ligand)

structure Order {m p d} (f : SignedPair.Frame m p d) (leftWins : Bool) where
  rows : List (SignedPair.Row m p d)
  complete : rows.Perm f.rows
  strict : rows.Pairwise (fun a b => precedes f leftWins a b = true)

def Order.ligands {m p d f w} (o : @Order m p d f w) := o.rows.map (·.ligand)

private def order? {m p d} (f : SignedPair.Frame m p d) (wins : Bool) : Option (Order f wins) := do
  let before a b := precedes f wins a b = true
  let rows := f.rows.insertionSort before
  if strict : rows.Pairwise before then return ⟨rows,List.perm_insertionSort _ _,strict⟩
  none

/-- Both molecular comparisons must exhibit the reflection behavior of
their deciding rule. The outer order uses the unchanged constitutional keys. -/
def mirrorWinner (stage : Stage) (win : Bool) := if stage == .five then !win else win

inductive Basis {m p d} (f : SignedPair.Frame m p d) (ls rs : Entries) : Bool → Bool → Type where
  | classes (c : UnitClasses.ArmComparison m p f.left.ligand f.right.ligand ls rs) :
      Basis f ls rs (c.difference.current.ordering == .gt) (c.difference.current.ordering == .gt)
  | stereo (stage : Stage) (w : Bool)
      (prior : EarlierStereoMatch.Decision m p f.left.ligand f.right.ligand stage ls rs)
      (actual : molecularSeniorLeft? m f.leftNode f.rightNode stage (positives ls) (positives rs) false = some w)
      (reflected : molecularSeniorLeft? m f.leftNode f.rightNode stage (positives ls) (positives rs) true =
        some (mirrorWinner stage w)) : Basis f ls rs w (mirrorWinner stage w)

def exchange (a b x : Nat) := if x = a then b else if x = b then a else x

structure Step (m : RawMolecule) (p : List Nat) (ls rs : Entries) where
  depth : Nat
  frame : SignedPair.Frame m p depth
  leftCoverage : ls.map Prod.fst = frame.leftPaths
  rightCoverage : rs.map Prod.fst = frame.rightPaths
  actualWins : Bool
  reflectedWins : Bool
  basis : Basis frame ls rs actualWins reflectedWins
  actual : Order frame actualWins
  reflected : Order frame reflectedWins
  transport : reflected.ligands = if actualWins = reflectedWins then actual.ligands else
    actual.ligands.map (exchange frame.left.ligand frame.right.ligand)

private def finish? {m p d} (f : SignedPair.Frame m p d) (l r : Entries)
    (lc : l.map Prod.fst = f.leftPaths) (rc : r.map Prod.fst = f.rightPaths)
    (x y : Bool) (b : Basis f l r x y) : Option (Step m p l r) := do
  let actual ← order? f x
  let reflected ← order? f y
  if h : reflected.ligands = (if x = y then actual.ligands else
      actual.ligands.map (exchange f.left.ligand f.right.ligand)) then
    return ⟨d,f,lc,rc,x,y,b,actual,reflected,h⟩
  none

private def stereo? {m p d} (f : SignedPair.Frame m p d) (l r : Entries) (s : Stage) :
    Option ((w : Bool) × Basis f l r w (mirrorWinner s w)) := do
  let ⟨w,hw⟩ ← (molecularSeniorLeft? m f.leftNode f.rightNode s (positives l) (positives r) false).attach
  if mirror : molecularSeniorLeft? m f.leftNode f.rightNode s (positives l) (positives r) true =
      some (mirrorWinner s w) then
    let prior ← EarlierStereoMatch.check? m p f.left.ligand f.right.ligand s l r
    return ⟨w,.stereo s w prior hw mirror⟩
  none

def check? {m p d} (f : SignedPair.Frame m p d) (l r : Entries) : Option (Step m p l r) := do
  if coverage : l.map Prod.fst = f.leftPaths ∧ r.map Prod.fst = f.rightPaths then
    for s in [Stage.fourB,.fourC,.five] do
      if let some ⟨w,b⟩ := stereo? f l r s then
        return ← finish? f l r coverage.1 coverage.2 w (mirrorWinner s w) b
    let c ← UnitClasses.between? m p f.left.ligand f.right.ligand l r
    let w := c.difference.current.ordering == .gt
    return ← finish? f l r coverage.1 coverage.2 w w (.classes c)
  none

end TetraStereo.Engine.RingChemicalPriority.DiscoveredPriority
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.DiscoveredPriority.check?
