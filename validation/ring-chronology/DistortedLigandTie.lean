import TetraStereo.Engine.RingConstitutionalResidual

/-! A rigid motion is unnecessary for two ligand paths to tie.
The raw As/O/O/F graph is an admitted mathematical test input. -/
open TetraStereo.OneCenter TetraStereo.Engine
namespace DistortedLigandTie

def molecule : RawMolecule where
  atoms := [.As,.O,.O,.F].map AtomSpec.aliphatic
  bonds := [⟨0,1,.single⟩,⟨1,2,.single⟩,⟨2,0,.single⟩,⟨0,3,.single⟩]

def center : CartesianPoint3 := ⟨0,0,1⟩
def left : CartesianPoint3 := ⟨1,0,0⟩
def right : CartesianPoint3 := ⟨0,2,0⟩
def positions : SpatialConfiguration := ⟨[center,left,right,⟨-1,-1,0⟩]⟩

def distSq (p q : CartesianPoint3) : ℚ :=
  (p.x-q.x)^2 + (p.y-q.y)^2 + (p.z-q.z)^2

theorem impossible_exchange (f : CartesianPoint3 → CartesianPoint3)
    (iso : ∀ p q, distSq (f p) (f q) = distSq p q) (fix : f center = center) : f left ≠ right := by
  intro exchange
  have h := iso center left
  rw [fix,exchange] at h
  norm_num [distSq,center,left,right] at h

def check : IO Unit := do
  let some i := LocalizedChemicalRing.admitRawSpatial? molecule positions | throw (IO.userError "admission")
  unless LocalizedChemicalRing.coordinatesAdmitted i do throw (IO.userError "coordinates")
  if h : 0 < i.certified.certified.input.molecule.atomCount then
    let a : i.certified.Atom := ⟨0,h⟩
    let q := RingGroupedReport.origin i a
    let arms := RingRetainedAuxiliary.frame i.certified q
    let arm (id : Nat) := arms.find? fun u => u.occurrence.val.node.current?.map Fin.val == some id
    let some u := arm 1 | throw (IO.userError "first O arm")
    let some v := arm 2 | throw (IO.userError "second O arm")
    let r := RingActiveDistanceSchedule.frozen (RingChemicalGraphProof.state i) q
    for rev in [false,true] do
      let some x := RingFullPathEligibility.key? i r rev u | throw (IO.userError "first key missing")
      let some y := RingFullPathEligibility.key? i r rev v | throw (IO.userError "second key missing")
      unless x == y do throw (IO.userError "unequal ordinary ligand priorities")
    unless RingHydrogenReport.fromRaw? molecule positions [0] == some [(0,none)] do
      throw (IO.userError "raw report assigned distorted As")
    IO.println "Squared distances 2 and 5. Equal ordinary keys through Rule 5 on both geometries. Public root unassigned."
  else throw (IO.userError "missing As")
end DistortedLigandTie
assert_kernel_only DistortedLigandTie.impossible_exchange
def main : IO Unit := DistortedLigandTie.check
