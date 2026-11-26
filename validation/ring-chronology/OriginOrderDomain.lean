import TetraStereo.Engine.RingOriginOrderRawCheck
/-! Computed strict-domain witness for eligible-focus preservation of duplicate-origin
orders. The trivalent boron junctions are admitted, hydrogen-complete and ineligible
under the actual public predicate. All eligible non-root occurrences lie on the acyclic
C0–C6 branch. Thus multiple origin paths and two origin depths coexist with preservation
of every actual duplicate-pair order (including ties) at every scheduled auxiliary.
This executable regression uses public admission, site enumeration, eligibility, queue,
publication and raw report APIs; it is bounded computed evidence, not a kernel theorem. -/
open TetraStereo.OneCenter TetraStereo.Engine

def main : IO Unit := do
  let m : RawMolecule := {
    atoms := [.C,.B,.B,.O,.S,.F,.C,.F,.Cl,.Br].map AtomSpec.aliphatic
    bonds := [(0,1),(0,2),(1,2),(1,3),(3,4),(4,2),(0,5),(0,6),(6,7),(6,8),(6,9)].map
      (fun (a,b) => ⟨a,b,.single⟩) }
  let coords : List CartesianPoint3 := [⟨0,0,0⟩,⟨1,0,0⟩,⟨0,1,0⟩,⟨2,1,0⟩,⟨1,2,1⟩,
    ⟨0,0,1⟩,⟨-1,-1,-1⟩,⟨-2,-1,-1⟩,⟨-1,-2,-1⟩,⟨-1,-1,-2⟩]
  unless (RingHydrogenCompletion.plan m).isEmpty do throw (IO.userError "implicit H plan nonempty")
  let some i := LocalizedChemicalRing.admitRawSpatial? m ⟨coords⟩ | throw (IO.userError "admission")
  unless LocalizedChemicalRing.coordinatesAdmitted i do throw (IO.userError "coordinates")
  let atoms := List.finRange i.certified.certified.input.molecule.atomCount
  IO.println s!"eligible atoms: {(atoms.filter (RingPyramidalPublication.eligible i)).map Fin.val}"
  let some root := atoms[0]? | throw (IO.userError "missing root")
  let sites := (RingActiveDistanceSchedule.sites i).filter (fun q => q.val.root == root)
  let duplicates := sites.filterMap fun q => match q.val.node.provenance with
    | .ringDuplicate d => some (q,d,RingSingleCycleOrigin.originPath q.val.node d)
    | _ => none
  unless RingOriginOrderCheck.check i root do throw (IO.userError "reflected domain certificate failed")
  IO.println "executable certificate: eligible-focus domain true"
  let common := duplicates.all fun (_,d,p) => duplicates.all fun (_,e,q) => d == e && p == q
  unless !common do throw (IO.userError "common-origin condition unexpectedly holds")
  IO.println "common-origin condition: false"
  let origins := (duplicates.map fun (_,d,p) => (d,p.map Fin.val)).eraseDups
  IO.println s!"origins: {origins}"
  let eligible := sites.filter fun q => q.val.node.provenance == .realAtom &&
    q.val.node.current? != some root && q.val.node.current?.any (RingPyramidalPublication.eligible i)
  IO.println s!"eligible foci: {eligible.map (fun q => q.val.node.history.reverse.map Fin.val)}"
  unless origins.length > 1 && ((origins.map Prod.fst).eraseDups.length > 1) && !eligible.isEmpty do
    throw (IO.userError "vacuous witness")
  let mut count := 0
  for f in eligible do
    for (_,u,p) in duplicates do
      for (_,v,q) in duplicates do
        unless compare u v == compare
          (RingSingleCycleOrigin.pathDistance f.val.node.history.reverse p)
          (RingSingleCycleOrigin.pathDistance f.val.node.history.reverse q) do
          throw (IO.userError "order mismatch")
        count := count + 1
  IO.println s!"verified all {count} duplicate-pair/focus comparisons (ties included)"
  let some focus := eligible[0]? | throw (IO.userError "missing scheduled focus")
  let depth := focus.val.node.history.length - 1
  unless (RingEligibleGraph.queue i (RingPyramidalPublication.eligible i) root depth).contains focus do
    throw (IO.userError "eligible focus missing from actual public queue")
  let batches := RingActiveDistanceSchedule.height i + 1 - depth
  let aux := ((RingSphereStore.rows i root batches).find? (fun row => row.1 == focus)).map Prod.snd
  unless aux == some (some (some (.chiral .S,.chiral .R))) do
    throw (IO.userError s!"unexpected scheduled auxiliary {repr aux}")
  IO.println s!"scheduled sphere {depth} auxiliary: S / R"
  unless RingOriginOrderRawCheck.check m ⟨coords⟩ [0,6] == some true do
    throw (IO.userError "raw domain certificate failed")
  unless (RingOriginOrderRawCheck.check m ⟨coords⟩ [m.atomCount]).isNone do
    throw (IO.userError "raw domain certificate accepted invalid atom ID")
  IO.println "raw domain certificate [0,6]: some true; invalid ID: none"
  let native := RingHydrogenReport.fromRaw? m ⟨coords⟩ [0,6]
  let active := RingOriginMetricReport.fromRaw? m ⟨coords⟩ [0,6]
  unless native.isSome && native == active do throw (IO.userError "raw reports mismatch")
  IO.println s!"matched raw reports: {repr native}"
