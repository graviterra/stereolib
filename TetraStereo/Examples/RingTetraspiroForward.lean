import TetraStereo.Examples.RingPublishedTetraspiroAuxiliary
import TetraStereo.Examples.RingTetraspiroPhysicalOrders
import TetraStereo.Engine.RingProximalPair

set_option autoImplicit false
set_option maxRecDepth 60000
set_option maxHeartbeats 6000000

namespace TetraStereo.Examples.RingTetraspiroForward
open OneCenter Engine CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open RingPublishedTetraspiro (molecule spatial reflected)
open RingPublishedTetraspiroAuxiliary (forward? sourceWalk? original_walk reflected_walk)

private abbrev Edge := Nat × Nat × Nat

/-- Order all four physical slots. The late result can refine only the named
tied pair. Every other strict direction must come from its Rule 1a spheres. -/
private def rankedHand? (xyz : SpatialConfiguration) (e : Edge) (result : RingSeededPairs.Decision) :
    Option RS := do
  let (root,left,right) := e
  let ids ← frameAtoms? molecule (canonicalCenterRoot root)
  let rows ← ids.mapM fun id => do
    return (id, ← RingChemicalPriority.ligandRows? molecule [root] id 1)
  let sign := RingActivePairs.score result
  let candidates := rows.permutations'.filter fun rank =>
    decide (rank.Pairwise fun a b => b.2 < a.2 ∨ (a.2 = b.2 ∧
      ((a.1 = left ∧ b.1 = right ∧ 0 < sign) ∨ (a.1 = right ∧ b.1 = left ∧ sign < 0))))
  let [rank] := candidates | none
  readback? (fun k => xyz.positions[k]?) (rank.map Prod.fst)

private def project (xyz mirrorXYZ : SpatialConfiguration) :
    List Edge → List RingSeededPairs.Decision → List RingSeededPairs.Decision →
    Option (List (Nat × LocalizedAuxiliaryLabel))
  | [],[],[] => some []
  | e::es,a::as',b::bs => do
    let actual ← rankedHand? xyz e a
    let mirror ← rankedHand? mirrorXYZ e b
    let label ← caseFromMirror? (some actual) (some mirror)
    return (e.1,label) :: (← project xyz mirrorXYZ es as' bs)
  | _,_,_ => none

/-- Only the molecular input and original paths supply the four stereo
decisions. Both complete priority orders are consumed by coordinate readback. -/
def report? (xyz mirrorXYZ : SpatialConfiguration) : Option (List (Nat × LocalizedAuxiliaryLabel)) := do
  let edges := RingPublishedTetraspiroAuxiliary.edges
  let actual ← edges.mapM fun (r,l,h) => forward? xyz r l h
  let mirror ← edges.mapM fun (r,l,h) => forward? mirrorXYZ r l h
  project xyz mirrorXYZ edges actual mirror

/-- Both sets of letters and casing follow from occurrence-level auxiliary
readings, the two reference orders and the four ranked coordinate frames. -/
theorem published_and_reflected :
    report? spatial reflected = some RingTetraspiroPhysicalOrders.published ∧
    report? reflected spatial =
      some [(2,.chiral .S),(3,.pseudoasymmetric .r),(6,.chiral .R),(9,.pseudoasymmetric .s)] := by
  obtain ⟨original,mirror⟩ := RingPublishedTetraspiroAuxiliary.forward_edges
  unfold report?
  dsimp only
  rw [original,mirror]
  decide +kernel

private def early? (xyz : SpatialConfiguration) (focus : Nat) := do
  let a ← RingPublishedTetraspiroAuxiliary.sourceWalk? xyz focus 9
  let b ← RingPublishedTetraspiroAuxiliary.sourceWalk? xyz focus 3
  RingSeededPairs.localSign? (a.take 3) (b.take 3)

private theorem early_of {xyz focus a b}
    (left : sourceWalk? xyz focus 9 = some a) (right : sourceWalk? xyz focus 3 = some b)
    (won : RingSeededPairs.localSign? (a.take 3) (b.take 3) = some 1) :
    early? xyz focus = some 1 := by simp [early?,left,right,won]

/-- At both chiral centers the third actual visit already decides Rule 4b.
The intervening unlabelled oxygen occupies position two in both walks. -/
theorem first_three :
    early? spatial 2 = some 1 ∧ early? reflected 2 = some 1 ∧
    early? spatial 6 = some 1 ∧ early? reflected 6 = some 1 := by
  exact ⟨early_of (original_walk 0) (original_walk 1) (by decide +kernel),
    early_of (reflected_walk 0) (reflected_walk 1) (by decide +kernel),
    early_of (original_walk 4) (original_walk 5) (by decide +kernel),
    early_of (reflected_walk 4) (reflected_walk 5) (by decide +kernel)⟩

/-- Any replacement of every tail publication or queue after those three
visits preserves the two chiral centers' decisive comparison. -/
theorem tail_independent {xyz : SpatialConfiguration} {focus : Nat} {a b : List (Option RS)}
    (site : xyz = spatial ∨ xyz = reflected) (center : focus = 2 ∨ focus = 6)
    (left : RingPublishedTetraspiroAuxiliary.sourceWalk? xyz focus 9 = some a)
    (right : RingPublishedTetraspiroAuxiliary.sourceWalk? xyz focus 3 = some b)
    (x y ar br as' bs : List (Option RS)) :
    RingSeededPairs.fromVisits? (a.take 3 ++ x) (b.take 3 ++ y) ar br as' bs = some ⟨1,none⟩ := by
  have known : early? xyz focus = some 1 := by
    rcases site with rfl | rfl <;> rcases center with rfl | rfl
    · exact first_three.1
    · exact first_three.2.2.1
    · exact first_three.2.1
    · exact first_three.2.2.2
  exact RingProximalPair.strict_prefix (by simpa [early?,left,right] using known)
    (by decide : (1 : Int) ≠ 0) x y ar br as' bs

end TetraStereo.Examples.RingTetraspiroForward
assert_kernel_only TetraStereo.Examples.RingTetraspiroForward.published_and_reflected
assert_kernel_only TetraStereo.Examples.RingTetraspiroForward.first_three
assert_kernel_only TetraStereo.Examples.RingTetraspiroForward.tail_independent
