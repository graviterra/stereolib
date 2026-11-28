import TetraStereo.Engine.RingOriginTwinStore

/-! Blue Book P-93.6 example 1, Hanson VS279. SDF path 12–3–2 is C-10–C-9–C-8.
Coordinates from compounds_3d.sdf are scaled by 10,000. This replay checks
the constitutional exit for the auxiliary occurrence on the C-10 digraph. -/
open TetraStereo.OneCenter TetraStereo.Engine

private def m : RawMolecule := {
  atoms := ([
    .C, .C, .C, .O, .C, .C, .C, .C, .C, .C, .C, .C,
    .C, .C, .C, .C, .C, .C, .H, .H, .H, .H, .H, .H,
    .H, .H, .H, .H, .H, .H, .H, .H, .H, .H, .H, .H,
    .H, .H, .H, .H, .H, .H, .H, .H, .H, .H, .H, .H,
    .H, .H] : List Element).map AtomSpec.aliphatic
  bonds := [
    ⟨0,1,.single⟩, ⟨4,0,.single⟩, ⟨1,2,.single⟩, ⟨1,3,.single⟩, ⟨11,2,.single⟩,
    ⟨4,5,.single⟩, ⟨4,9,.single⟩, ⟨5,6,.single⟩, ⟨6,7,.single⟩, ⟨7,8,.single⟩,
    ⟨7,10,.single⟩, ⟨8,9,.single⟩, ⟨11,12,.single⟩, ⟨11,16,.single⟩, ⟨12,13,.single⟩,
    ⟨13,14,.single⟩, ⟨14,15,.single⟩, ⟨14,17,.single⟩, ⟨15,16,.single⟩, ⟨0,18,.single⟩,
    ⟨0,19,.single⟩, ⟨2,20,.single⟩, ⟨2,21,.single⟩, ⟨3,22,.single⟩, ⟨4,23,.single⟩,
    ⟨5,24,.single⟩, ⟨5,25,.single⟩, ⟨6,26,.single⟩, ⟨6,27,.single⟩, ⟨7,28,.single⟩,
    ⟨8,29,.single⟩, ⟨8,30,.single⟩, ⟨9,31,.single⟩, ⟨9,32,.single⟩, ⟨10,33,.single⟩,
    ⟨10,34,.single⟩, ⟨10,35,.single⟩, ⟨11,36,.single⟩, ⟨12,37,.single⟩, ⟨12,38,.single⟩,
    ⟨13,39,.single⟩, ⟨13,40,.single⟩, ⟨14,41,.single⟩, ⟨15,42,.single⟩, ⟨15,43,.single⟩,
    ⟨16,44,.single⟩, ⟨16,45,.single⟩, ⟨17,46,.single⟩, ⟨17,47,.single⟩, ⟨17,48,.single⟩,
    ⟨49,1,.single⟩] }

private def g : SpatialConfiguration := ⟨[
    ⟨-43095,1951,-8033⟩, ⟨-56855,7740,-3213⟩, ⟨-67577,5777,-14300⟩, ⟨-61830,-30,7953⟩,
    ⟨-30638,11286,-7509⟩, ⟨-35112,25827,-9711⟩, ⟨-23452,35599,-10094⟩, ⟨-14547,34855,2396⟩,
    ⟨-11083,20355,6224⟩, ⟨-23091,10801,5965⟩, ⟨-1837,43122,171⟩, ⟨-77973,17100,-16963⟩,
    ⟨-70475,30545,-17991⟩, ⟨-79395,42958,-17572⟩, ⟨-88652,43235,-5374⟩, ⟨-96840,30270,-4798⟩,
    ⟨-88389,17511,-5509⟩, ⟨-80996,46035,7625⟩, ⟨-43899,-1454,-18415⟩, ⟨-41057,-7093,-2239⟩,
    ⟨-73044,-3423,-11881⟩, ⟨-62726,3549,-23808⟩, ⟨-56065,40,15827⟩, ⟨-23709,8513,-15562⟩,
    ⟨-42071,28851,-1745⟩, ⟨-40657,26682,-19125⟩, ⟨-27278,45774,-11294⟩, ⟨-17443,33500,-19032⟩,
    ⟨-20088,39360,10750⟩, ⟨-6553,20234,16219⟩, ⟨-3404,16486,-580⟩, ⟨-19691,633,8089⟩,
    ⟨-29890,13527,14159⟩, ⟨4262,38953,-7944⟩, ⟨4383,43361,9187⟩, ⟨-4232,53450,-2491⟩,
    ⟨-83206,15357,-26460⟩, ⟨-64645,30747,-27223⟩, ⟨-63169,31323,-9843⟩, ⟨-85439,43273,-26670⟩,
    ⟨-73123,51920,-17733⟩, ⟨-95654,51600,-6697⟩, ⟨-103921,30217,-13120⟩, ⟨-102916,30090,4340⟩,
    ⟨-83331,16454,4108⟩, ⟨-95055,8833,-6300⟩, ⟨-73897,38074,10126⟩, ⟨-87908,47016,16083⟩,
    ⟨-75360,55378,6931⟩, ⟨-56024,18137,176⟩]⟩

def main : IO Unit := do
  let some i := LocalizedChemicalRing.admitRawSpatial? m g | throw (IO.userError "admission")
  unless LocalizedChemicalRing.coordinatesAdmitted i do throw (IO.userError "geometry")
  let some f := (RingActiveDistanceSchedule.sites i).find? (fun f =>
    f.val.root.val == 11 && f.val.node.history.reverse.map (fun a => a.val + 1) == [12,3,2]) | throw (IO.userError "path")
  let native := (RingSphereQueue.early? i f).map RingGeometryCriterion.Signature.letters
  let active := (RingOriginPriorityStore.early? i f).map RingGeometryCriterion.Signature.letters
  unless native == some (some (.chiral .S,.chiral .R)) && active.isNone do throw (IO.userError "unexpected constitutional comparison")
  IO.println "VS279 C-10 to C-8: public constitutional S (mirror R), current-root constitutional tie."
