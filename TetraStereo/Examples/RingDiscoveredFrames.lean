import TetraStereo.Examples.BlueBookRule4aSource
import TetraStereo.Examples.BlueBookCyclobutanediol

set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option Elab.async false

namespace TetraStereo.Examples.RingDiscoveredFrames
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open Engine.RingChemicalPriority Recursive

/-- The constructed control has a Cl,F-substituted central carbon and two
CHFBr arms. Each arm has the same constitution and ranks behind both halogens. -/
def molecule : RawMolecule where
  atoms := [.aliphatic .C,.aliphatic .Cl,.aliphatic .F,.aliphatic .C,.aliphatic .C,
    .aliphatic .Br,.aliphatic .F,.aliphatic .H,.aliphatic .Br,.aliphatic .F,.aliphatic .H]
  bonds := ([(0,1),(0,2),(0,3),(0,4),(3,5),(3,6),(3,7),(4,8),(4,9),(4,10)] :
    List (Nat × Nat)).map fun (a,b) => ⟨a,b,.single⟩



def points : List CartesianPoint3 := [
  ⟨0,0,0⟩,⟨0,-1,2⟩,⟨0,-1,-2⟩,⟨2,1,0⟩,⟨-2,1,0⟩,
  ⟨3,3,1⟩,⟨4,-1,0⟩,⟨1,2,-1⟩,⟨-3,3,1⟩,⟨-4,-1,0⟩,⟨-1,2,-1⟩]

def geometry : Geometry := fun i => points[i]?

/-- Exchanging the positions of Br8 and H10 inverts C4 alone. -/
def sameHand : Geometry := fun i => geometry (if i = 8 then 10 else if i = 10 then 8 else i)

private def unhinted (m : RawMolecule) (g : Geometry) (p : List Nat) (depth fuel : Nat) :=
  RingAuxiliaryInventory.classify? m g (fun _ => none) (fun _ => depth) fuel p

private def decidingStage {m p d f ls rs x y} :
    @DiscoveredPriority.Basis m p d f ls rs x y → Option Stage
  | .classes _ => none
  | .stereo s .. => some s

/-- A missing stage denotes the Rule 4a comparison of stereogenic unit classes. -/
private def hasDecision {m g p} (r : Option (RingAuxiliaryInventory.Result m g p))
    (stage : Option Stage) (actual reflected : List Nat) (reading : Reading) : Bool :=
  r.any fun
    | .discovered c =>
      decidingStage c.step.basis == stage && c.step.actual.ligands == actual &&
        c.step.reflected.ligands == reflected && c.reading == reading
    | _ => false

theorem bottom_pair_constitution :
    saturatedWithHalogens molecule = true ∧
    (IsotopePriority.compareIncident? molecule [0] 3 4).map (·.ordering) = some .eq ∧
    (unhinted molecule geometry [0,3] 1 1).bind (·.reading) = some ⟨.R,.S⟩ ∧
    (unhinted molecule geometry [0,4] 1 1).bind (·.reading) = some ⟨.S,.R⟩ := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩

/-- Rule 5 puts C3(R) third and C4(S) fourth at the central carbon. The
mirror reverses only these two priorities and retains lowercase s. -/
theorem bottom_pair :
    hasDecision (unhinted molecule geometry [0] 1 2) (some .five)
        [1,2,3,4] [1,2,4,3] ⟨.S,.S⟩ = true ∧
    hasDecision (unhinted molecule (mirror geometry) [0] 1 2) (some .five)
        [1,2,4,3] [1,2,3,4] ⟨.S,.S⟩ = true ∧
    (Reading.mk .S .S).label = some (.pseudoasymmetric .s) := by
  exact ⟨by decide +kernel,by decide +kernel,rfl⟩

theorem identical_arms :
    (unhinted molecule sameHand [0,4] 1 1).bind (·.reading) = some ⟨.R,.S⟩ ∧
    (unhinted molecule sameHand [0] 1 2).map (·.reading) = some none := by
  exact ⟨by decide +kernel,by decide +kernel⟩

/-- P-92.5.1. At C4 the hydroxyl leads, followed by the pseudoasymmetric
C3, then nonstereogenic C5, then hydrogen. C4 is uppercase S. -/
theorem published_rule4a :
    hasDecision (unhinted BlueBookRule4aSource.molecule BlueBookRule4aSource.geometry [4] 1 3)
      none [0,3,5,31] [0,3,5,31] ⟨.S,.R⟩ = true := by decide +kernel

/-- P-92.6 Example 2. Each hydroxyl-bearing root reads the opposite
carbon through two different ring paths. Rule 5 resolves both middle
pairs, giving the two published lowercase r descriptors. -/
theorem published_cyclobutanediol :
    hasDecision (unhinted BlueBookCyclobutanediol.molecule BlueBookCyclobutanediol.geometry [0] 2 2)
      (some .five) [4,1,3,6] [4,3,1,6] ⟨.R,.R⟩ = true ∧
    hasDecision (unhinted BlueBookCyclobutanediol.molecule BlueBookCyclobutanediol.geometry [2] 2 2)
      (some .five) [5,1,3,7] [5,3,1,7] ⟨.R,.R⟩ = true := by
  exact ⟨by decide +kernel,by decide +kernel⟩

end TetraStereo.Examples.RingDiscoveredFrames

assert_kernel_only TetraStereo.Examples.RingDiscoveredFrames.bottom_pair
assert_kernel_only TetraStereo.Examples.RingDiscoveredFrames.identical_arms
assert_kernel_only TetraStereo.Examples.RingDiscoveredFrames.published_rule4a
assert_kernel_only TetraStereo.Examples.RingDiscoveredFrames.published_cyclobutanediol
