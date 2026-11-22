import TetraStereo.Engine.RingCursorStereo

set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 2600000
set_option Elab.async false

namespace TetraStereo.Examples.RingIncomingStereo
open OneCenter Engine RingChemicalPriority LocalizedGenericMarkedRecalculation

/-- The cyclopropoxy-substituted focus at 5 has two 3-chloro-3-fluoropropyl
arms. The original digraph root at 0 is a methylene in one of those arms. -/
def molecule : RawMolecule :=
  match parseAndNormalizeOpenSMILESCertified "C(CC(F)Cl)C(F)(OC1CC1)CCC(F)Cl" [] with
  | .ok v => v.result.parsed.withExplicitHydrogens
  | .error _ => {atoms := [],bonds := []}

/-- The moment-curve control gives S on both arm termini. Exchanging the
two halogen positions at 13 inverts that site while keeping the coordinates
at the nested focus and at the other arm fixed. -/
def geometry (invert : Bool) : Geometry := fun i =>
  let k : Nat := if invert && i == 14 then 15 else if invert && i == 15 then 14 else i
  some ⟨k,k*k,k*k*k⟩

structure Projection where
  incoming : List Nat
  outward : List Nat
  actual : Int
  reflected : Int
  order : List Nat
  label : LocalizedTetrahedralRSPseudoDescriptor
  deriving DecidableEq, Repr

def diagnosis (g : Geometry) : Option Projection := do
  let cache : RecursiveSigned.Cache molecule g 3 := {}
  let a ← CursorStereo.assign? cache [0,5]
  return ⟨a.pair.a.node.history.reverse,a.pair.b.node.history.reverse,
    a.pair.code false,a.pair.code true,a.rank.actual,a.label⟩

/-- The incoming witness lies in a different branch of the original
digraph. Its original depth exceeds the depth of the current focus. -/
theorem different_branch : ¬([0,5] : List Nat) <+: [0,1,2] ∧
    ([0,5] : List Nat).length < [0,1,2].length ∧ molecule.atomCount = 31 ∧
    saturatedWithHalogens molecule = true := by decide +kernel

theorem omitted_by_descendant_certificate {g : Geometry} (c : RecursiveSigned.Certificate molecule g [0,5]) :
    c.published.lookup [0,1,2] = none := CursorStereo.outside_branch c different_branch.1

theorem opposite_arms : diagnosis (geometry true) =
    some ⟨[0,1,2],[0,5,11,12,13],-2,2,[6,7,11,0],.pseudoasymmetric .s⟩ := by
  decide +kernel

/-- Replay the reflected molecule as a new comparison, and invert only the
terminus as a control. Identical hands cannot establish the Rule 5 split. -/
def validate : IO Unit := do
  unless diagnosis (mirror (geometry true)) ==
      some ⟨[0,1,2],[0,5,11,12,13],2,-2,[6,7,0,11],.pseudoasymmetric .s⟩ do
    throw (IO.userError "unexpected reflected incoming Rule 5 assignment")
  unless (RecursiveSigned.derive? molecule (geometry true) 3 molecule.atomCount [0,5]).isNone do
    throw (IO.userError "descendant-only calculation unexpectedly resolved")
  unless (diagnosis (geometry false)).isNone do
    throw (IO.userError "equal arm hands passed the opposite-pair check")

#eval validate
end TetraStereo.Examples.RingIncomingStereo

assert_kernel_only TetraStereo.Examples.RingIncomingStereo.different_branch
assert_kernel_only TetraStereo.Examples.RingIncomingStereo.opposite_arms

assert_kernel_only TetraStereo.Examples.RingIncomingStereo.omitted_by_descendant_certificate
