import TetraStereo.OneCenter.CanonicalComparisonFrame

set_option autoImplicit false

namespace TetraStereo.OneCenter.CanonicalTreeProfile
open RawMolecule

structure Profile where
  center : CanonicalBranchNode
  frame : CanonicalComparisonFrame.Frame
  generated : List CanonicalBranchNode
  deriving DecidableEq, Repr


def collect : Nat → Nat → RawMolecule → List CanonicalBranchNode →
    Option (List CanonicalBranchNode)
  | 0, _, _, [] => some []
  | 0, _, _, _ :: _ => none
  | _ + 1, _, _, [] => some []
  | fuel + 1, cap, mol, frontier =>
      if cap < frontier.length then none else do
        let tail ← collect fuel (cap - frontier.length) mol (frontier.flatMap mol.canonicalChildren)
        some (frontier ++ tail)

/-- No caller supplies coordinate bounds or membership. Entire actual original-root tree is checked. -/
def profile? (mol : RawMolecule) (center : CanonicalBranchNode) : Option Profile := do
  let root ← center.history.getLast?
  if !(decide (root < mol.atomCount)) || !(mol.bonds.all mol.bondEndpointsOK?) then none else
  let generated ← collect (mol.atomCount + 1) mol.atomCount mol
    [{ atom := root, parent := root, history := [root], provenance := .realAtom }]
  if !generated.contains center then none else
  if !(generated.all fun node =>
      node.provenance == .realAtom && node.history.head? == some node.atom &&
      node.history.getLast? == some root && !node.history.isEmpty &&
      decide node.history.Nodup && node.history.all (fun atom => decide (atom < mol.atomCount))) then none else
    some ⟨center, ⟨center.history⟩, generated⟩


/-- Empty frontiers terminate independently of fuel and remaining budget. -/
theorem collect_empty (fuel cap : Nat) (mol : RawMolecule) :
    collect fuel cap mol [] = some [] := by
  cases fuel <;> rfl

end TetraStereo.OneCenter.CanonicalTreeProfile
