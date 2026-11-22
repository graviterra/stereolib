import TetraStereo.Examples.RingDimethylThiiraneBoundary
import TetraStereo.Engine.RingPendantPromotedKey

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 30000

namespace TetraStereo.Examples.RingPendantMethylRoles
open OneCenter Engine CertifiedLocalizedCIPInput
open RingDimethylThiiraneBoundary (input)
open RingPendantReferenceRoles (Side rawAtom)
open RingPendantPromotedKey (side? Outward)
open LocalizedMarkedRetainedPromotedKey (ordinaryKey?)
open LocalizedMarkedRetainedSparsePromotedKey (sparseCompareAt?)

def atom (n : Fin 13) : input.certified.Atom := ⟨n.val,n.isLt⟩
def ids (xs : List (Fin 13)) := (xs.map (fun n => rawAtom (atom n))).toFinset

/-- The four vertices of each molecular side are independently checked against
every bond. Cutting C0--C3 or C0--C4 isolates an entire methyl group. -/
def left : Side input (rawAtom (atom 0)) :=
  (side? input (rawAtom (atom 0)) (rawAtom (atom 3)) (ids [3,7,8,9])).get (by decide +kernel)
def right : Side input (rawAtom (atom 0)) :=
  (side? input (rawAtom (atom 0)) (rawAtom (atom 4)) (ids [4,10,11,12])).get (by decide +kernel)

private def ns (root : Bool) : List input.certified.Atom :=
  (if root then [0,2,5,6] else [1,2,3,4] : List (Fin 13)).map atom

private theorem canonical (root : Bool) :
    (input.certified.moleculeGraph.neighborFinset (if root then atom 1 else atom 0)).sort (· ≤ ·) = ns root := by
  have eqn : input.certified.moleculeGraph.neighborFinset (if root then atom 1 else atom 0) = (ns root).toFinset := by
    ext b
    rw [input.certified.moleculeGraph.mem_neighborFinset]
    revert b
    cases root <;> decide +kernel
  rw [eqn]
  cases root <;> apply (List.toFinset_sort (· ≤ ·) (by decide +kernel)).mpr <;> decide +kernel

private def start := OfficialCIPNode.root (atom 1)
private def gate := start.extend (atom 0) 0
private def methyl (r : Bool) := atom (if r then 4 else 3)
private def head (r : Bool) := gate.extend (methyl r) 0
private def slot (r : Bool) : Nat := if r then 2 else 1

private theorem entry : (gate,0) ∈ (input.certified.executableOfficialCIPChildren start).zipIdx := by
  change _ ∈ ((input.certified.executableOfficialNeighborCopies (atom 1)).map fun x => start.extend x.1 x.2).zipIdx
  rw [executableOfficialNeighborCopies,show (input.certified.moleculeGraph.neighborFinset (atom 1)).sort (· ≤ ·) = _
    from canonical true]
  decide +kernel

private theorem branch (r : Bool) : (head r,slot r) ∈ (input.certified.executableOfficialCIPChildren gate).zipIdx := by
  change _ ∈ (((input.certified.executableOfficialNeighborCopies (atom 0)).filter fun x =>
    !(x.1 == atom 1 && x.2 == 0)).map fun x => gate.extend x.1 x.2).zipIdx
  rw [executableOfficialNeighborCopies,show (input.certified.moleculeGraph.neighborFinset (atom 0)).sort (· ≤ ·) = _
    from canonical false]
  cases r <;> decide +kernel

def focus : RingActivePairs.Site input :=
  RingRetainedConstitution.occurrence input.certified (atom 1) (.step entry (.refl _))

def arm (r : Bool) : RingActivePairs.Arm input := ⟨RingRetainedConstitution.occurrence input.certified (atom 1)
  (.step entry (.step (branch r) (.refl _))),some focus⟩

private theorem valid (r : Bool) : input.certified.LocalizedRerootCursorValid (arm r) := by
  apply (input.certified.mem_localizedRerootNeighborFrames_iff ..).mpr
  exact ⟨(arm r).occurrence.property,rfl,Or.inr ⟨rfl,rfl⟩⟩

def leftSource : Outward left (arm false) := ⟨atom 3,rfl,rfl,rfl,⟨focus,rfl,rfl,rfl,rfl⟩⟩
def rightSource : Outward right (arm true) := ⟨atom 4,rfl,rfl,rfl,⟨focus,rfl,rfl,rfl,rfl⟩⟩

/-- All older selections at the real C1 ancestor are covered, including C0
itself. At the C1→C0 target, a retained selection cannot appear in either
complete C0→methyl subtree or change any promoted comparison between them. -/
theorem methyl_promotion (mark : input.certified.Atom) (choice : input.certified.moleculeGraph.Adj (atom 1) mark)
    (view : input.certified.LocalizedDependencyView focus) (W D : Nat) :
    ∃ ka kb, ordinaryKey? input.certified focus view (arm false) = some ka ∧
      ordinaryKey? input.certified focus view (arm true) = some kb ∧
      sparseCompareAt? input.certified focus view mark W D (arm false) (arm true) =
        some (input.certified.compareLocalizedRerootCompoundThroughRule5 ka kb).ordering := by
  obtain ⟨ka,ea⟩ := LocalizedMarkedRetainedPromotedKey.ordinaryKey?_exists input.certified focus view _ (valid false)
  obtain ⟨kb,eb⟩ := LocalizedMarkedRetainedPromotedKey.ordinaryKey?_exists input.certified focus view _ (valid true)
  have l := RingPendantPromotedKey.older_mark_outside left focus rfl rfl (by decide +kernel) (atom 1) mark
    (by decide +kernel) choice
  have r := RingPendantPromotedKey.older_mark_outside right focus rfl rfl (by decide +kernel) (atom 1) mark
    (by decide +kernel) choice
  exact ⟨ka,kb,ea,eb,RingPendantPromotedKey.sparse_eq_ordinary left right focus view mark l r
    W D _ _ leftSource rightSource (valid false) (valid true) ka kb ea eb⟩

/-- Even choosing C0 itself at C1 cannot place a mark on either pendant
subtree. This choice is adjacent to both entry atoms. -/
theorem boundary_choice : input.certified.moleculeGraph.Adj (atom 1) (atom 0) ∧
    input.certified.moleculeGraph.Adj (atom 0) (atom 3) ∧ input.certified.moleculeGraph.Adj (atom 0) (atom 4) ∧
    (∀ (r : Bool) (x : RingActivePairs.Arm input),
      Relation.ReflTransGen (fun a b => b ∈ input.certified.executableLocalizedRerootChildren a) (arm r) x →
      x.occurrence.val.node.current? ≠ some (atom 0)) := by
  refine ⟨by decide +kernel,by decide +kernel,by decide +kernel,?_⟩
  intro r
  cases r
  · exact leftSource.absent (atom 0) left.outside
  · exact rightSource.absent (atom 0) right.outside

end TetraStereo.Examples.RingPendantMethylRoles
assert_kernel_only TetraStereo.Examples.RingPendantMethylRoles.methyl_promotion
assert_kernel_only TetraStereo.Examples.RingPendantMethylRoles.boundary_choice
