import TetraStereo.Engine.RingOriginTwinStore
/-! Hanson 3D validation molecule VS084. The V2000 coordinates were multiplied
by 10,000 exactly. Atom 1 in that file is the zero-based request [0]. -/
open TetraStereo.OneCenter TetraStereo.Engine
def VS084 : RawMolecule := { atoms := [.C,.O,.C,.C,.O,.C,.C,.O,.H,.H,.H,.H,.H,.H].map AtomSpec.aliphatic, bonds := [⟨0,6,.single⟩,⟨0,1,.single⟩,⟨0,2,.single⟩,⟨0,9,.single⟩,⟨1,2,.single⟩,⟨2,3,.single⟩,⟨2,8,.single⟩,⟨3,7,.single⟩,⟨3,4,.single⟩,⟨3,11,.single⟩,⟨4,5,.single⟩,⟨5,6,.single⟩,⟨6,7,.single⟩,⟨6,10,.single⟩,⟨12,5,.single⟩,⟨13,5,.single⟩] }
def VS084xyz : List CartesianPoint3 := [⟨-30708,-17383,-2258⟩,⟨-26035,-22287,-14998⟩,⟨-17171,-13734,-7427⟩,⟨-18475,1151,-8939⟩,⟨-26842,4159,-20227⟩,⟨-40127,1853,-15093⟩,⟨-37301,-3917,-1281⟩,⟨-26463,4505,2328⟩,⟨-8458,-17470,-2247⟩,⟨-32130,-24238,5978⟩,⟨-45624,-3375,5838⟩,⟨-8969,6635,-9237⟩,⟨-45735,-4904,-21681⟩,⟨-45261,11475,-14538⟩]
def main : IO Unit := do
  unless RingOriginTwinStore.structuralFromRaw? VS084 ⟨VS084xyz⟩ [0] == some true do
    throw (IO.userError "VS084 structural raw certificate failed")
  let some source := LocalizedChemicalRing.admitRawSpatial? VS084 ⟨VS084xyz⟩ | throw (IO.userError "admission")
  let some i := RingChemicalReport.prepared? source | throw (IO.userError "preparation")
  let some r := (List.finRange i.certified.certified.input.molecule.atomCount)[0]? | throw (IO.userError "root")
  if RingAtomicMetricPublication.check i r then throw (IO.userError "prior certificate unexpectedly passed")
  IO.println "VS084 atom 1: raw structural certificate passed; all sphere boundaries covered"
  -- For another requested root of the very same molecule the two metrics
  -- strictly reverse the result at an eligible auxiliary on a known path.
  let some r4 := (List.finRange i.certified.certified.input.molecule.atomCount)[3]? |
    throw (IO.userError "missing atom 4")
  let wanted := [4,5,6,7,1,2,3]
  let some f := (RingActiveDistanceSchedule.sites i).find? (fun f =>
    f.val.root == r4 && (f.val.node.history.reverse.map (fun a => a.val + 1)) == wanted) |
    throw (IO.userError "missing ring path")
  let n := RingActiveDistanceSchedule.height i - RingActiveDistanceSchedule.distance f
  unless n < RingActiveDistanceSchedule.height i + 1 &&
      (RingGlobalComparison.queue i r4 (RingActiveDistanceSchedule.height i - n)).contains f &&
      (RingPyramidalPublication.focusP i f).isNone do throw (IO.userError "site not scheduled as tetrahedral")
  let some active := RingOriginPriorityStore.early? i f | throw (IO.userError "active constitutional tie")
  let some native := RingSphereQueue.early? i f | throw (IO.userError "native constitutional tie")
  unless native.letters.isSome && active.letters.isSome && native.letters != active.letters do
    throw (IO.userError s!"expected opposite constitutional assignments, got {repr native.letters} and {repr active.letters}")
  IO.println s!"VS084 atom 4, path {wanted}, batch {n + 1}: public {repr native.letters}, active {repr active.letters}"
  let origin := RingGroupedReport.origin i r4
  let publicRoot := (RingSphereQueue.early? i origin).bind RingGeometryCriterion.Signature.letters
  let activeRoot := (RingOriginPriorityStore.early? i origin).bind RingGeometryCriterion.Signature.letters
  unless (RingPyramidalPublication.focusP i origin).isNone &&
      publicRoot == some (.chiral .S, .chiral .R) && activeRoot == publicRoot do
    throw (IO.userError "the published S root and its R reflection must survive the auxiliary disagreement")
  IO.println s!"VS084 atom 4 constitutional exit at the root: public {repr publicRoot}, active {repr activeRoot}"
