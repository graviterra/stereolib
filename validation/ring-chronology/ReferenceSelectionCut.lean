import TetraStereo.Engine.RingReferenceVotes
import TetraStereo.Engine.RingPromotionCut
import TetraStereo.Engine.RingSphereQueue

open TetraStereo.OneCenter TetraStereo.Engine

private def xyz (n : Nat) (perm : Nat → Nat := id) : SpatialConfiguration :=
  ⟨(List.range n).map fun j =>
    let t : ℚ := perm j
    ⟨t,t*t,t*t*t⟩⟩

private def build (elements : List Element) (edges : List (Nat × Nat)) : RawMolecule :=
  {atoms := elements.map AtomSpec.aliphatic, bonds := edges.map fun (a,b) => ⟨a,b,.single⟩}

private def admit (m : RawMolecule) (g : SpatialConfiguration) : IO LocalizedChemicalRing.Input := do
  let some i := LocalizedChemicalRing.admitRawSpatial? m g | throw (IO.userError "structural admission")
  unless LocalizedChemicalRing.coordinatesAdmitted i do throw (IO.userError "coordinate admission")
  return i

private def cut : IO Unit := do
  let m := build (List.replicate 3 .C ++ List.replicate 6 .H)
    [(0,1),(1,2),(2,0),(0,3),(0,4),(1,5),(1,6),(2,7),(2,8)]
  let i ← admit m (xyz 9)
  let some a := (RingGroupedReport.centres i).find? (fun j => j.val == 0) | throw (IO.userError "cyclopropane root")
  let q := RingGroupedReport.origin i a
  let some c := RingGeometryCertificates.prepare? i q | throw (IO.userError "cyclopropane context")
  let flags := (List.finRange 4).filter (RingPromotionCut.rootFlag c.arms)
  unless flags.length == 2 && (RingGroupedOrders.marks c.arms).length == 4 &&
      (RingPromotionCut.refusal? c).isSome && RingGroupedReport.forAtoms? i [a] == some [(0,none)] do
    throw (IO.userError "missing four-mark, two-return-arm refusal certificate")
  IO.println "Cyclopropane: four eligible promotions, two root-returning arms, certified completed refusal."

  -- Differentiate the two ring paths with Br and give the root F and Cl.
  let distinct := build ([.C,.C,.C,.F,.Cl,.Br,.H,.H,.H] : List Element)
    [(0,1),(1,2),(2,0),(0,3),(0,4),(1,5),(1,6),(2,7),(2,8)]
  let strict ← admit distinct (xyz 9)
  let some a := (RingGroupedReport.centres strict).find? (fun j => j.val == 0)
    | throw (IO.userError "substituted cyclopropane root")
  let q := RingGroupedReport.origin strict a
  let some c := RingGeometryCertificates.prepare? strict q
    | throw (IO.userError "substituted cyclopropane context")
  let some s := RingSphereQueue.early? strict q | throw (IO.userError "expected a strict order")
  let some (.chiral h,.chiral mirror) := s.letters | throw (IO.userError "expected two absolute hands")
  unless mirror == h.swap && (RingGroupedOrders.marks c.arms).isEmpty &&
      (RingPromotionCut.refusal? c).isNone do
    throw (IO.userError "cut incorrectly accepted a strict root")
  IO.println "Substituted cyclopropane: opposite absolute hands and no refusal certificate."

-- In one ligand of this cyclopropyl compound a carbon supports three chiral
-- children. CH(Br)Cl is constitutionally senior to each CH(F)Cl child.
private def ranked : RawMolecule :=
  build (List.replicate 7 .C ++ [.Br,.Cl,.H,.F,.Cl,.H,.F,.Cl,.H] ++ List.replicate 5 .H)
    ([(0,1),(1,2),(2,0),(0,3),(0,16),(1,17),(1,18),(2,19),(2,20)] ++
     (List.range 3).flatMap (fun j => [(3,4+j),(4+j,7+3*j),(4+j,8+3*j),(4+j,9+3*j)]))

private def site (i : LocalizedChemicalRing.Input) (sites : List (RingActivePairs.Site i))
    (history : List Nat) : IO (RingActivePairs.Site i) := do
  let some q := sites.find? (fun q => q.val.node.provenance == .realAtom && q.val.node.history.map Fin.val == history)
    | throw (IO.userError s!"missing {history}")
  return q

private def rankSelection : IO Unit := do
  let raw ← admit ranked (xyz 21)
  let nodes := (RingActiveDistanceSchedule.sites raw).filter fun q => q.val.root.val == 0
  let flips ← (List.range 3).mapM fun j => do
    let q ← site raw nodes [4+j,3,0]
    let some s := RingSphereQueue.early? raw q | throw (IO.userError "missing constitutional assignment")
    let some (.chiral h,_) := s.letters | throw (IO.userError "expected an absolute assignment")
    return h != (if j == 0 then RS.S else .R)
  let perm (n : Nat) := if 7 ≤ n && n < 16 && flips[(n-7)/3]?.getD false then
    match (n-7)%3 with | 0 => n+1 | 1 => n-1 | _ => n
    else n
  let i ← admit ranked (xyz 21 perm)
  let sites := (RingActiveDistanceSchedule.sites i).filter fun q => q.val.root.val == 0
  let f ← site i sites [0]
  let trunk ← site i sites [3,0]
  let root := f.val.root
  let inventory := sites.filter fun q => decide (RingSphereQueue.candidate root q)
  let queue := fun d => inventory.filter fun q => RingActiveDistanceSchedule.distance q == d
  let top := RingActiveDistanceSchedule.height i
  let rows := RingSphereQueue.stored (RingGroupedPublication.publish? i) root queue top (top+1)
  let read := RingSphereQueue.reader root (RingSphereQueue.viewOf rows)
  let arm : RingActivePairs.Arm i := ⟨trunk,some f⟩
  let some p := RingGroupedStereo.arm? i read arm | throw (IO.userError "missing ligand")
  let allHands := p.hits.map (·.hand)
  unless allHands.count .S == 1 && allHands.count .R == 2 &&
      RingRetainedReferenceGroup.hands p.hits false == [.S] &&
      RingReferenceVotes.molecular? i read arm false == some [.S] &&
      RingReferenceVotes.molecular? i read arm true == some [.R] do
    throw (IO.userError s!"unexpected seniority or frozen population {repr allHands}")
  IO.println "21-atom ring: senior S beats two junior R occurrences under the same parent; reflection selects R."

def main : IO Unit := do
  cut
  rankSelection
