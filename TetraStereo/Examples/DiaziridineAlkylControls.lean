import TetraStereo.Engine.RingOxaziridineNitrogen

/-! Structural controls for saturated N-alkyl and C3-alkyl diaziridines.
All omitted hydrogens are represented by ordinary valence completion. -/
set_option autoImplicit false
namespace TetraStereo.Examples.DiaziridineAlkylControls
open OneCenter Engine
open RingDialkyldiaziridine (constrainedRaw)

private def single (a b : Nat) : RawBond := ⟨a,b,.single⟩
private def chain (start length : Nat) :=
  (List.range (length-1)).map fun k => single (start+k) (start+k+1)

/-- Each N bears a straight-chain alkyl group; the ring carbon may carry
one or two additional methyl groups. -/
private def scaffold (left right c3 : Nat) : RawMolecule :=
  let b := 3+left
  {atoms := ([Element.N,.N] ++ List.replicate (1+left+right+c3) Element.C).map AtomSpec.aliphatic
   bonds := [single 0 1,single 0 2,single 1 2,single 0 3,single 1 b] ++
     chain 3 left ++ chain b right ++ (List.range c3).map (fun k => single 2 (b+right+k))}

private def both (m : RawMolecule) := constrainedRaw m 0 && constrainedRaw m 1

set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

/-- The same decision accepts both N atoms of the di-n-propyl and di-n-butyl
scaffolds and the 1,2,3,3-tetramethyl constitution. -/
theorem sourced : both (scaffold 3 3 0) = true ∧ both (scaffold 4 4 0) = true ∧
    both (scaffold 1 1 1) = true ∧ both (scaffold 1 1 2) = true := by decide +kernel

private def appendBond (m : RawMolecule) (b : RawBond) := {m with bonds := m.bonds ++ [b]}
private def endO (kind : ParsedBondKind) : RawMolecule :=
  let m := scaffold 2 1 0
  {m with atoms := m.atoms ++ [AtomSpec.aliphatic .O], bonds := m.bonds ++ [⟨4,m.atomCount,kind⟩]}

private def neither (m : RawMolecule) := !constrainedRaw m 0 && !constrainedRaw m 1

/-- A cyclopropyl substituent, distal alcohol, carbonyl or N-acyl substituent
each excludes both sites from this measured dialkyl class. -/
theorem excluded :
    neither (appendBond (scaffold 3 1 0) (single 3 5)) = true ∧
    neither (endO .single) = true ∧ neither (endO .double) = true ∧
    neither (let m := scaffold 1 1 0
      {m with atoms := m.atoms ++ [AtomSpec.aliphatic .O],
              bonds := m.bonds ++ [⟨3,m.atomCount,.double⟩]}) = true := by decide +kernel

end TetraStereo.Examples.DiaziridineAlkylControls
assert_kernel_only TetraStereo.Examples.DiaziridineAlkylControls.sourced
assert_kernel_only TetraStereo.Examples.DiaziridineAlkylControls.excluded
