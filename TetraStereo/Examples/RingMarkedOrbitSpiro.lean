import TetraStereo.Examples.RingSignedTwoPairSpiro
import TetraStereo.Engine.RingMarkedOrbitCancellation

set_option autoImplicit false
set_option maxRecDepth 60000
set_option maxHeartbeats 7500000

namespace TetraStereo.Examples.RingMarkedOrbitSpiro
open OneCenter Engine CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open RingChemicalPriority Recursive Promotion TwoPairPriority MarkedOrbit
open RingSignedTwoPairSpiro (molecule geometry)

/-- Exchange the two three-membered rings and their complete substituents. -/
private def ringMap : Fin 25 → Fin 25 :=
  ![0,3,4,1,2,7,8,5,6,11,12,9,10,19,20,21,22,23,24,13,14,15,16,17,18]

private theorem involution : Function.Involutive ringMap := by
  change ∀ x : Fin 25, ringMap (ringMap x) = x
  decide +kernel

def exchange : Equiv.Perm (Fin molecule.atomCount) :=
  ⟨ringMap,ringMap,involution,involution⟩

/-- The exchange is realized on the supplied rational coordinates by the
half turn about the line x = 0, y = z. -/
def rotate (p : CartesianPoint3) : CartesianPoint3 := ⟨-p.x,p.z,p.y⟩

theorem coordinates : ∀ i : Fin molecule.atomCount,
    geometry (exchange i).val = (geometry i.val).map rotate := by decide +kernel

theorem volume_preserved (a b c d : CartesianPoint3) :
    CartesianPoint3.orientedVolume (rotate a) (rotate b) (rotate c) (rotate d) =
      CartesianPoint3.orientedVolume a b c d := by
  unfold CartesianPoint3.orientedVolume rotate
  dsimp only
  ring

private theorem atomData : ∀ i, molecule.atoms.get (exchange i) = molecule.atoms.get i := by
  decide +kernel

theorem automorphism : exchange ∈ molecule.toMoleculeGraph.Aut :=
  ⟨fun x => congrArg (fun z : AtomSpec => z.element.atomicNumber) (atomData x),
   by decide +kernel,fun x => congrArg AtomSpec.charge (atomData x),by decide +kernel⟩

/-- Check the signed inventory, omissions and both sets of marked directions
in the classified experiment. All projected data come from that experiment. -/
def exchange? {omitted} {e : Experiment molecule [0] omitted} (q : Classified e) :
    Option (Action q 2 4 1 3) := do
  if slots : q.partition.order = [2,4,1,3] then
    if omissions : (omitted.map (List.map (atomImage exchange))).Perm omitted then
      if facts : ∀ u ∈ e.arms, ∃ v ∈ e.arms, v.ligand = atomImage exchange u.ligand ∧
          (u.facts.map fun f => (f.1.map (atomImage exchange),f.2)).Perm v.facts then
        return ← check? ⟨slots,exchange,automorphism,atomData,by decide +kernel,omissions,facts,
          true,true,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩
  none

/-- The reference uses the full signed inventory of the published fixture,
including the two routes to each carbon and all eight omissions. -/
private def entries : InventoryPriority.Entries :=
  ([(1,2,RS.S),(2,1,.R),(3,4,.S),(4,3,.R)] : List (Nat × Nat × RS)).flatMap fun (u,v,h) =>
    [([0,u],some ⟨h,h.swap⟩),([0,u,v],some ⟨h,h.swap⟩),([0,u,v,v+4],none),([0,u,u+4],none)]

private def signed := RingAuxiliaryInventory.signedExperiment? 2 (canonicalCenterRoot 0)
  (m := molecule) (p := [0]) (by decide +kernel) (by rfl) (by decide +kernel) entries

/-- Both outputs are checked on the same source matrix. The first checks the
double exchange and the second is the real four-vote consensus. -/
def verify : Option (Bool × Reading) := do
  let e ← signed
  let q ← classify? e
  let r ← q.certificate? geometry
  return ((exchange? q).isSome,r.reading)

theorem checked : verify = some (true,⟨.S,.R⟩) := by decide +kernel

end TetraStereo.Examples.RingMarkedOrbitSpiro
assert_kernel_only TetraStereo.Examples.RingMarkedOrbitSpiro.automorphism
assert_kernel_only TetraStereo.Examples.RingMarkedOrbitSpiro.checked

assert_kernel_only TetraStereo.Examples.RingMarkedOrbitSpiro.coordinates
assert_kernel_only TetraStereo.Examples.RingMarkedOrbitSpiro.volume_preserved
