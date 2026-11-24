import TetraStereo.Engine.RingRootReturn

open TetraStereo.OneCenter TetraStereo.Engine
attribute [local instance] lexOrd

private def molecule (elements : List Element) (bonds : List (Nat × Nat)) : RawMolecule :=
  {atoms := elements.map AtomSpec.aliphatic, bonds := bonds.map fun (a,b) => ⟨a,b,.single⟩}

private def inspect (name : String) (m : RawMolecule) (root copies flags : Nat)
    (expectedAssigned : Option Bool) (duplicate : Option (List Nat × Nat) := none) : IO Unit := do
  let coords : SpatialConfiguration := ⟨(List.range m.atomCount).map fun j =>
    let t : ℚ := j
    ⟨t,t*t,t*t*t⟩⟩
  let some i := LocalizedChemicalRing.admitRawSpatial? m coords | throw (IO.userError s!"{name}: admission")
  let some r := (RingGroupedReport.centres i).find? (fun a => a.val == root) | throw (IO.userError s!"{name}: root")
  let some c := RingGeometryCertificates.prepare? i (RingGroupedReport.origin i r) | throw (IO.userError s!"{name}: frame")
  let actual := (RingRootReturn.rootCopies i r).length
  let flagged := ((List.finRange 4).filter (RingPromotionCut.rootFlag c.arms)).length
  unless actual == copies && flagged == flags do throw (IO.userError s!"{name}: found {actual} copies and {flagged} flagged arms")
  if let some (history,depth) := duplicate then
    let hit := (RingActiveDistanceSchedule.sites i).any fun q =>
      q.val.root == r && q.val.node.history.map Fin.val == history &&
        q.val.node.provenance == .ringDuplicate depth
    let entry := history.reverse[1]?
    let target := history.head?
    let returns := ((List.finRange 4).filter (RingPromotionCut.rootFlag c.arms)).map (RingGroupedTrials.atom c.fr)
    unless hit && entry != target && entry.any returns.contains && target.any returns.contains do
      throw (IO.userError s!"{name}: missing cross-arm duplicate or returning arm")
  let grouped := RingGroupedReport.forAtoms? i [r]
  let counted := RingRootReturn.rootByCount i r
  unless counted.isSome && counted.map (fun v => [(r.val,v)]) == grouped do
    throw (IO.userError s!"{name}: count-based result differs from grouped result")
  if let some assigned := expectedAssigned then
    let earlier := (RingGeometryCriterion.Signature.mk
      (RingOrientation.baseline c.fr * RingOrientation.orientation (c.arms.key false))
      (RingGeometryCriterion.reversals c.arms)).letters
    unless actual < 3 && earlier.isSome == assigned && counted == some earlier do
      throw (IO.userError s!"{name}: unexpected ordinary or published assignment")
  let some hydrogen := (List.finRange i.certified.certified.input.molecule.atomCount).getLast?
    | throw (IO.userError s!"{name}: no terminal hydrogen")
  unless RingRootReturn.rootByCount i hydrogen == some none do
    throw (IO.userError s!"{name}: terminal hydrogen should have a completed absence")
  IO.println s!"{name}: {actual} root duplicates, {flagged} returning arms"
  (← IO.getStdout).flush

def main : IO Unit := do
  let triangle := [(0,1),(1,2),(2,0),(0,3),(0,4),(1,5),(1,6),(2,7),(2,8)]
  inspect "cyclopropane, tied" (molecule (List.replicate 3 .C ++ List.replicate 6 .H) triangle) 0 2 2 (some false)
  inspect "substituted cyclopropane, strict" (molecule [.C,.C,.C,.F,.Cl,.Br,.H,.H,.H] triangle) 0 2 2 (some true)
  let bicyclic := [(0,1),(0,2),(2,1),(0,3),(3,1),(0,4),(1,5),(2,6),(2,7),(3,8),(3,9)]
  inspect "bicyclo[1.1.0]butane bridgehead" (molecule (List.replicate 4 .C ++ List.replicate 6 .H) bicyclic) 0 6 3 none
  -- From methyl carbon 3 the three-membered ring is wholly inside one arm.
  let methyl := [(0,1),(1,2),(2,0),(0,3),(0,4),(1,5),(1,6),(2,7),(2,8),(3,9),(3,10),(3,11)]
  inspect "methylcyclopropane, exocyclic root" (molecule (List.replicate 4 .C ++ List.replicate 8 .H) methyl) 3 0 0 (some false)
  -- Enter the second triangle through C2 and return to its duplicate. Relative
  -- to peripheral root C0 this duplicate carries a different direct neighbor.
  let spiro := molecule (List.replicate 5 .C ++ List.replicate 8 .H)
    [(0,1),(1,2),(2,0),(2,3),(3,4),(4,2),(0,5),(0,6),(1,7),(1,8),(3,9),(3,10),(4,11),(4,12)]
  inspect "spiro[2.2]pentane, peripheral root" spiro 0 2 2 (some false) (some ([2,4,3,2,1,0],2))
  inspect "spiro[2.2]pentane, shared root" spiro 2 4 4 none
