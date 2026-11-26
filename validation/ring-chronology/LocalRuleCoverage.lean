import TetraStereo.Engine.PublicAPI
import TetraStereo.Engine.RingStereoInventoryReport
import TetraStereo.Engine.RingSparseTwinReport

open TetraStereo.OneCenter TetraStereo.Engine

namespace LocalRuleCoverage

private def molecule (elements : List Element) (edges : List (Nat × Nat)) : RawMolecule :=
  { atoms := elements.map AtomSpec.aliphatic
    bonds := edges.map fun (a,b) => ⟨a,b,.single⟩ }

/-- The reflection (x,y,z) ↦ (−y,−x,z) exchanges the two phosphorus arms and
fixes the oxirane ring. The ligand priority at each P is Cl, F, ring C, phantom. -/
private def positions : List CartesianPoint3 := [
  ⟨0,0,0⟩, ⟨2,2,2⟩, ⟨-2,-2,2⟩, ⟨2,-2,-2⟩, ⟨-2,2,-2⟩,
  ⟨4,1,2⟩, ⟨2,4,1⟩, ⟨-1,-4,2⟩, ⟨-4,-2,1⟩, ⟨-4,2,-3⟩, ⟨-2,4,-3⟩]

private def oxirane := molecule [.C,.P,.P,.O,.C,.Cl,.F,.Cl,.F,.H,.H]
  [(0,1),(0,2),(0,3),(0,4),(3,4),(1,5),(1,6),(2,7),(2,8),(4,9),(4,10)]

private def cyclopropane (count : Nat) : RawMolecule := molecule
  ([.C,.C,.C,.Br,.F] ++ List.replicate count .H)
  ([(0,1),(0,2),(0,3),(0,4),(1,2)] ++ [(1,5),(1,6),(2,7),(2,8)].take count)

private def checkReport (label : String) (m : RawMolecule) (points : List CartesianPoint3)
    (expected : RingGroupedReport.Report) : IO Bool := do
  let some rows := ringMolecularReportFromRaw? m ⟨points⟩ (expected.map Prod.fst)
    | throw (IO.userError s!"{label} failed admission")
  let conforms := rows == expected
  IO.println s!"{label} conforms to IUPAC = {conforms}, rows = {repr rows}"
  return conforms

/-- Check graph symmetries independently of their coordinate-frame compatibility. -/
def branchSymmetryControls : IO Unit := do
  for labelled in [false,true] do
    let m := cyclopropane 4
    let m := if labelled then {m with atoms := m.atoms.modify 5 fun a => {a with isotope? := some 2}} else m
    let some i := LocalizedChemicalRing.admitRawSpatial? m ⟨positions.take 9⟩
      | throw (IO.userError "branch cyclopropane admission failed")
    unless LocalizedChemicalRing.coordinatesAdmitted i do
      throw (IO.userError "branch cyclopropane coordinates rejected")
    if h : i.certified.certified.input.molecule.atomCount = 9 then
      let c := finCongr h
      let e9 : Equiv.Perm (Fin 9) :=
        (Equiv.swap 1 2).trans ((Equiv.swap 5 7).trans (Equiv.swap 6 8))
      let e := (c.trans e9).trans c.symm
      unless (ringCheckBranchSymmetry? i e).isSome == !labelled do
        throw (IO.userError "whole cyclopropane branch check missed the isotope distinction")
      unless (ringCheckBranchSymmetry? i ((c.trans (Equiv.swap 1 2)).trans c.symm)).isNone do
        throw (IO.userError "partial cyclopropane branch exchange accepted")
      unless (e (c.symm 1)).val == 2 && (e (c.symm 2)).val == 1 &&
          (e (c.symm 0)).val == 0 && (e (c.symm 3)).val == 3 && (e (c.symm 4)).val == 4 do
        throw (IO.userError "cyclopropane branch exchange moved a fixed neighbor")
      unless labelled do
        for id in [1,2] do
          let cs := i.certified.canonicalTetrahedralCenters.filter fun c => c.val.val == id
          unless cs.length == 1 do throw (IO.userError "missing cyclopropane CH2 center")
          for center in cs do
            unless (RingHydrogenSpelling.detectedTwinPair? i center).isSome do
              throw (IO.userError "cyclopropane CH2 twins not detected")
    else throw (IO.userError "unexpected cyclopropane atom count")
  let hand := fun (ps : List CartesianPoint3) (cl f carbon phosphorus : Nat) => do
    let a ← ps[cl]?
    let b ← ps[f]?
    let c ← ps[carbon]?
    let d ← ps[phosphorus]?
    CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints? [a,b,c,d]
  for matching in [false,true] do
    let ps := if matching then positions.set 7 ⟨-4,-2,1⟩ |>.set 8 ⟨-1,-4,2⟩ else positions
    let some i := LocalizedChemicalRing.admitRawSpatial? oxirane ⟨ps⟩
      | throw (IO.userError "branch oxirane admission failed")
    unless LocalizedChemicalRing.coordinatesAdmitted i do throw (IO.userError "branch oxirane coordinates rejected")
    if h : i.certified.certified.input.molecule.atomCount = 11 then
      let c := finCongr h
      let e11 : Equiv.Perm (Fin 11) :=
        (Equiv.swap 1 2).trans ((Equiv.swap 5 7).trans (Equiv.swap 6 8))
      let e := (c.trans e11).trans c.symm
      unless (ringCheckBranchSymmetry? i e).isSome do throw (IO.userError "whole P branch exchange rejected")
      unless (e (c.symm 0)).val == 0 && (e (c.symm 3)).val == 3 && (e (c.symm 4)).val == 4 do
        throw (IO.userError "P branch exchange moved the fixed oxirane core")
      let moved := RingNumberedHydrogenGeometry.reindexed i i e
      let p1 := hand ps 5 6 0 1
      let p2 := hand ps 7 8 0 2
      let q1 := hand moved.positions 5 6 0 1
      let q2 := hand moved.positions 7 8 0 2
      unless p1 == some RS.R && p2 == some (if matching then RS.R else RS.S) && q1 == p2 && q2 == p1 do
        throw (IO.userError "Cl,F,C0,P determinant control changed")
      unless ((p1 == q1) && (p2 == q2)) == matching do
        throw (IO.userError "off-root P frame agreement control changed")
      IO.println s!"Whole P branch graph accepted; hands {repr p1}, {repr p2} -> {repr q1}, {repr q2}; off-root agreement {matching}."
    else throw (IO.userError "unexpected oxirane atom count")
  IO.println "Whole cyclopropane branch accepted, partial/isotope exchanges rejected; CH2 twins detected."

/-- All ordinary-H spellings retain the isotope-sensitive assignments at both
ring carbons. Priority-ordered determinants use the actual prepared C1 hydrogen. -/
def monodeuteratedHydrogenSpellings : IO Unit := do
  let core := {molecule [.C,.C,.C,.Br,.F,.H]
    [(0,1),(0,2),(0,3),(0,4),(1,2),(1,5)] with
    atoms := ([.C,.C,.C,.Br,.F] : List Element).map AtomSpec.aliphatic ++
      [{AtomSpec.aliphatic .H with isotope? := some 2}]}
  let read := fun (ps : List CartesianPoint3) (ids : List Nat) => do
    let points ← ids.mapM fun n => ps[n]?
    CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints? points
  for mask in List.range 8 do
    let chosen := (List.range 3).filter fun j => mask.testBit j
    let m := {core with
      atoms := core.atoms ++ List.replicate chosen.length (.aliphatic .H)
      bonds := core.bonds ++ chosen.zipIdx.map fun (j,k) => ⟨(if j == 0 then 1 else 2),6+k,.single⟩}
    let xyz := positions.take 6 ++ chosen.filterMap fun j => positions[6+j]?
    let mut originalHands : Option (RS × RS) := none
    for reflected in [false,true] do
      let ps := if reflected then xyz.map (fun p => {p with x := -p.x}) else xyz
      let some (out,prepared) := RingHydrogenCompletion.prepare? m ⟨ps⟩
        | throw (IO.userError s!"isotope mask {mask} preparation failed")
      let hydrogen := if mask.testBit 0 then 6 else m.atomCount
      unless out.atomCount == 9 && out.atoms[5]?.bind (fun a => a.isotope?) == some 2 &&
          out.bondOrder 1 hydrogen == 1 do
        throw (IO.userError s!"isotope mask {mask} lost D or C1 ordinary H")
      let some h0 := read prepared.positions [3,4,1,2]
        | throw (IO.userError s!"isotope mask {mask} C0 determinant missing or zero")
      let some h1 := read prepared.positions [0,2,5,hydrogen]
        | throw (IO.userError s!"isotope mask {mask} C1 determinant missing or zero")
      if reflected then
        unless originalHands == some (h0.swap,h1.swap) do
          throw (IO.userError s!"isotope mask {mask} reflection did not reverse both ordered hands")
      else
        originalHands := some (h0,h1)
      let ids := List.range m.atomCount ++ [1,0,5,1]
      let expected : RingGroupedReport.Report := ids.map fun n =>
        (n,if n == 0 then some (.chiral h0,.chiral h0.swap)
           else if n == 1 then some (.chiral h1,.chiral h1.swap) else none)
      unless ringMolecularReportFromRaw? m ⟨ps⟩ ids == some expected do
        throw (IO.userError s!"isotope mask {mask}, mirror {reflected}: two assignments/refusal rows changed")
      unless (ringMolecularReportFromRaw? m ⟨ps⟩ [m.atomCount]).isNone do
        throw (IO.userError s!"isotope mask {mask} exposed a nonoriginal atom ID")
      IO.println s!"Isotope mask {mask}, mirror {reflected}: C0 {repr h0}, C1 {repr h1}, C1 H ID {hydrogen}; all other original rows refused."
  IO.println "All eight monodeuterated spellings passed both carbon hands, mirrors, original-ID refusals and repeats."

/-- At C0 the order is F, C1, C2, H. At C1 it is Cl, C0, C2, H.
The independently supplied hydrogen positions give signed volumes +160 and −144. -/
private def chiralHydrogenSpellings : IO Unit := do
  let core := molecule [.C,.C,.C,.F,.Cl] [(0,1),(1,2),(2,0),(0,3),(1,4)]
  let heavy : List CartesianPoint3 := [⟨0,0,0⟩,⟨4,0,0⟩,⟨0,4,0⟩,⟨0,0,4⟩,⟨4,0,4⟩]
  let hs : List (Nat × CartesianPoint3) := [(0,⟨-2,-1,-3⟩),(1,⟨6,-2,-3⟩),
    (2,⟨0,7,2⟩),(2,⟨1,7,-2⟩)]
  let r := LocalizedTetrahedralRSPseudoDescriptor.chiral .R
  let s := LocalizedTetrahedralRSPseudoDescriptor.chiral .S
  let expected : RingGroupedReport.Report := [(0,some (s,r)),(1,some (r,s)),(2,none)]
  for mask in List.range 16 do
    let written := (hs.zipIdx.filter fun (_,k) => mask.testBit k).map Prod.fst
    let m := {core with
      atoms := core.atoms ++ List.replicate written.length (.aliphatic .H)
      bonds := core.bonds ++ written.zipIdx.map fun ((parent,_),k) => ⟨parent,5+k,.single⟩}
    let g := heavy ++ written.map Prod.snd
    unless ringMolecularReportFromRaw? m ⟨g⟩ [0,1,2] == some expected do
      throw (IO.userError s!"chiral cyclopropane hydrogen spelling {mask} changed the report")
  IO.println "All 16 chiral cyclopropane H spellings gave S/R, R/S and a refusal."

/-- Two ordinary CH₂ hydrogens move to independent positions while every heavy
coordinate stays fixed. Their fixed labeled determinant reverses, but the public
heavy rows, repeated request IDs and completed refusals must remain identical. -/
private def ch2CoordinateMotion : IO Unit := do
  let m := molecule [.C,.C,.C,.F,.Cl,.H,.H,.H,.H]
    [(0,1),(1,2),(2,0),(0,3),(1,4),(0,5),(1,6),(2,7),(2,8)]
  let original : List CartesianPoint3 := [
    ⟨0,0,0⟩,⟨4,0,0⟩,⟨0,4,0⟩,⟨0,0,4⟩,⟨4,0,4⟩,
    ⟨-2,-1,-3⟩,⟨6,-2,-3⟩,⟨0,7,2⟩,⟨1,7,-2⟩]
  let moved := original.set 7 ⟨10,-9,-8⟩ |>.set 8 ⟨-7,14,9⟩
  let determinant := fun ps : List CartesianPoint3 => do
    let a ← ps[0]?
    let b ← ps[1]?
    let h ← ps[7]?
    let k ← ps[8]?
    return CartesianPoint3.orientedVolume a b h k
  let some before := determinant original | throw (IO.userError "CH2 original coordinates missing")
  let some after := determinant moved | throw (IO.userError "CH2 moved coordinates missing")
  unless before * after < 0 do
    throw (IO.userError "CH2 labeled determinant did not reverse nondegenerately")
  unless (original.take 7 == moved.take 7) do
    throw (IO.userError "CH2 motion changed a fixed coordinate")
  let r := LocalizedTetrahedralRSPseudoDescriptor.chiral .R
  let s := LocalizedTetrahedralRSPseudoDescriptor.chiral .S
  let expected : RingGroupedReport.Report :=
    [(0,some (s,r)),(1,some (r,s)),(2,none),(3,none),(4,none),(1,some (r,s)),(7,none),(8,none),(7,none)]
  for (label,points) in [("original",original),("moved",moved)] do
    unless ringMolecularReportFromRaw? m ⟨points⟩ (expected.map Prod.fst) == some expected do
      throw (IO.userError s!"CH2 {label} geometry changed public heavy rows")
  let rename := fun n : Nat => 8-n
  let reversed : RawMolecule := {m with
    atoms := m.atoms.reverse
    bonds := m.bonds.reverse.map fun b => {b with source := rename b.source, target := rename b.target}}
  let renamed := expected.map fun row => (rename row.1,row.2)
  for (label,points) in [("original",original), ("moved",moved)] do
    unless ringMolecularReportFromRaw? reversed ⟨points.reverse⟩ (renamed.map Prod.fst) == some renamed do
      throw (IO.userError s!"CH2 {label} reversed numbering changed public heavy rows")
  -- Inverting the single H at genuinely stereogenic C0 must change its hand.
  let inverted := original.set 5 ⟨6,5,7⟩
  unless ringMolecularReportFromRaw? m ⟨inverted⟩ [0,1,2] ==
      some [(0,some (r,s)),(1,some (r,s)),(2,none)] do
    throw (IO.userError "single-H stereocenter inversion failed the negative control")
  let flat := original.set 8 ⟨0,7,2⟩
  unless ringMolecularReportFromRaw? m ⟨flat⟩ [] == none &&
      ringMolecularReportFromRaw? m ⟨original⟩ [] == some [] do
    throw (IO.userError "empty request failed to distinguish the degenerate CH2 frame")
  IO.println s!"CH2 coordinate motion gave determinants {before} and {after} with rows {repr expected}"
  IO.println "CH2 and terminal H rows survived renumbering. The empty request detected degeneracy. Single-H inversion changed C0."

/-- Two CH₂ parents move independently in one ring. In the fixed neighbor
orders C1,C3,H8,H9 and C0,C2,H10,H11, the first target reverses one
labeled frame and preserves the other. Independent H swaps exercise all
four local parity choices without changing any original query identity. -/
private def multiCh2CoordinateMotion : IO Unit := do
  let m := molecule [.C,.C,.C,.C,.F,.Cl,.H,.H,.H,.H,.H,.H]
    [(0,1),(1,2),(2,3),(3,0),(0,4),(1,5),(0,6),(1,7),(2,8),(2,9),(3,10),(3,11)]
  let original : List CartesianPoint3 := [
    ⟨0,0,0⟩,⟨4,0,0⟩,⟨4,4,0⟩,⟨0,4,0⟩,⟨0,0,4⟩,⟨4,0,4⟩,
    ⟨-2,-1,-3⟩,⟨6,-2,-3⟩,⟨6,6,2⟩,⟨6,6,-2⟩,⟨-2,6,2⟩,⟨-2,6,-2⟩]
  let moved := original.take 8 ++ [⟨8,6,-3⟩,⟨9,5,4⟩,⟨-3,7,4⟩,⟨-4,6,-2⟩]
  let determinant := fun (ps : List CartesianPoint3) (a b h k : Nat) => do
    let p ← ps[a]?
    let q ← ps[b]?
    let u ← ps[h]?
    let v ← ps[k]?
    return CartesianPoint3.orientedVolume p q u v
  unless determinant original 1 3 8 9 == some (-128) &&
      determinant original 0 2 10 11 == some 128 &&
      determinant moved 1 3 8 9 == some 280 &&
      determinant moved 0 2 10 11 == some 240 do
    throw (IO.userError "multi-CH2 fixed-row determinant controls changed")
  unless original.take 8 == moved.take 8 do
    throw (IO.userError "multi-CH2 motion changed a retained coordinate")
  let r := LocalizedTetrahedralRSPseudoDescriptor.chiral .R
  let s := LocalizedTetrahedralRSPseudoDescriptor.chiral .S
  let ids := List.range 12 ++ [1,8,9,10,11,8,0]
  let expected : RingGroupedReport.Report := ids.map fun id =>
    (id,if id == 0 then some (s,r) else if id == 1 then some (r,s) else none)
  let check := fun (label : String) (points : List CartesianPoint3) => do
    unless ringMolecularReportFromRaw? m ⟨points⟩ ids == some expected do
      throw (IO.userError s!"multi-CH2 {label} changed chiral, refusal, H or repeated rows")
    unless (ringMolecularReportFromRaw? m ⟨points⟩ [0,12,1]).isNone do
      throw (IO.userError s!"multi-CH2 {label} admitted invalid original ID 12")
  check "original" original
  let some h8 := moved[8]? | throw (IO.userError "multi-CH2 H8 coordinate missing")
  let some h9 := moved[9]? | throw (IO.userError "multi-CH2 H9 coordinate missing")
  let some h10 := moved[10]? | throw (IO.userError "multi-CH2 H10 coordinate missing")
  let some h11 := moved[11]? | throw (IO.userError "multi-CH2 H11 coordinate missing")
  for mask in List.range 4 do
    let points := moved.set 8 (if mask.testBit 0 then h9 else h8)
      |>.set 9 (if mask.testBit 0 then h8 else h9)
      |>.set 10 (if mask.testBit 1 then h11 else h10)
      |>.set 11 (if mask.testBit 1 then h10 else h11)
    let expected2 : Rat := if mask.testBit 0 then -280 else 280
    let expected3 : Rat := if mask.testBit 1 then -240 else 240
    unless determinant points 1 3 8 9 == some expected2 &&
        determinant points 0 2 10 11 == some expected3 do
      throw (IO.userError s!"multi-CH2 local parity choice {mask} did not act independently")
    check s!"independent parity choice {mask}" points
    IO.println s!"Multi-CH2 choice {mask}: C2 -128 -> {expected2}, C3 +128 -> {expected3}; all original-ID rows preserved."
  IO.println "Multi-CH2 C0 S/R and C1 R/S survived all four independent H-pair choices; H/refusal/repeated rows and invalid-ID rejection passed."

/-- The two explicit readings differ at one P–H position only. Omitting it must
retain assignments shared by both completions and decline a request on which they differ. -/
private def oxiraneHydrogenReadings : IO Unit := do
  let heavy : RawMolecule := {
    atoms := [.C,.P,.P,.O,.C,.F,.F,.H,.H].map AtomSpec.aliphatic
    bonds := ([(0,1),(0,2),(0,3),(0,4),(3,4),(1,5),(2,6),(4,7),(4,8)] : List (Nat × Nat)).map fun (a,b) => ⟨a,b,.single⟩}
  let points : List CartesianPoint3 := [⟨0,0,0⟩,⟨2,2,2⟩,⟨-2,-2,2⟩,⟨2,-2,-2⟩,⟨-2,2,-2⟩,
    ⟨2,4,1⟩,⟨-4,-2,1⟩,⟨-4,2,-3⟩,⟨-2,4,-3⟩]
  let first : CartesianPoint3 := ⟨4,1,2⟩
  let other : CartesianPoint3 := ⟨-1,-4,2⟩
  let opposite : CartesianPoint3 := ⟨-3,0,2⟩
  let r := LocalizedTetrahedralRSPseudoDescriptor.chiral .R
  let s := LocalizedTetrahedralRSPseudoDescriptor.chiral .S
  let lower := LocalizedTetrahedralRSPseudoDescriptor.pseudoasymmetric .s
  for (key,hs,expected) in [
      ("opposite",[first,other],some [(0,some (lower,lower)),(1,some (r,s)),(2,some (s,r))]),
      ("same",[first,opposite],some [(0,none),(1,some (r,s)),(2,some (r,s))]),
      ("one",[first],none),("neither",[],none)] do
    let m := {heavy with
      atoms := heavy.atoms ++ List.replicate hs.length (.aliphatic .H)
      bonds := heavy.bonds ++ hs.zipIdx.map fun (_,i) => ⟨i+1,i+9,.single⟩}
    let g : SpatialConfiguration := ⟨points ++ hs⟩
    unless ringMolecularReportFromRaw? m g [0,1,2] == expected do
      throw (IO.userError s!"oxirane P–H {key} full request disagreed")
    if key == "one" then
      unless (ringMolecularReportFromRaw? m g [0]).isNone do
        throw (IO.userError "ambiguous P–H assigned a downstream carbon")
      unless ringMolecularReportFromRaw? m g [1,1] == some [(1,some (r,s)),(1,some (r,s))] do
        throw (IO.userError "a known phosphorus changed on the other arm")
      unless ringMolecularReportFromRaw? m g [3] == some [(3,none)] do
        throw (IO.userError "a determined refusal was lost")
      unless (ringMolecularReportFromRaw? m g [10]).isNone do
        throw (IO.userError "a generated P hydrogen was available as an original ID")
  IO.println "Oxirane P–H ambiguity and unaffected requests passed."

/-- Reverse atom IDs and bond order so the equal constitutional P arms occur
in the opposite native order. Record the real queue on either side of its
one-bond batch, before evaluating the carbon root. -/
private def oxiraneRenumberedSnapshots : IO Unit := do
  let rename := fun n : Nat => 10 - n
  let moved : RawMolecule := {oxirane with
    atoms := oxirane.atoms.reverse
    bonds := oxirane.bonds.reverse.map fun b =>
      {b with source := rename b.source, target := rename b.target}}
  let r := LocalizedTetrahedralRSPseudoDescriptor.chiral .R
  let s := LocalizedTetrahedralRSPseudoDescriptor.chiral .S
  let lower := LocalizedTetrahedralRSPseudoDescriptor.pseudoasymmetric .s
  -- Check the independent Cl,F,C,P determinant convention used for the
  -- two expected pyramidal hands, including the center in the fourth slot.
  unless CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints?
      [positions[5]'(by decide),positions[6]'(by decide),positions[0]'(by decide),positions[1]'(by decide)] == some RS.R &&
      CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints?
      [positions[7]'(by decide),positions[8]'(by decide),positions[0]'(by decide),positions[2]'(by decide)] == some RS.S do
    throw (IO.userError "oxirane independent pyramidal hand convention changed")
  for (label,m,points,rootId,ps) in [
      ("original",oxirane,positions,0,[(1,(r,s)),(2,(s,r))]),
      ("renumbered",moved,positions.reverse,10,[(9,(r,s)),(8,(s,r))])] do
    let some i := LocalizedChemicalRing.admitRawSpatial? m ⟨points⟩
      | throw (IO.userError s!"oxirane {label} snapshot admission failed")
    if bound : rootId < i.certified.certified.input.molecule.atomCount then
      let root : i.certified.Atom := ⟨rootId,bound⟩
      let queue := RingEligibleGraph.queue i (RingPyramidalPublication.eligible i) root
      let height := RingActiveDistanceSchedule.height i
      unless 1 ≤ height do throw (IO.userError s!"oxirane {label} queue has no one-bond batch")
      let batches := RingSphereQueue.stored (RingPyramidalPublication.publish i) root queue height
      let before := batches (height - 1)
      let after := batches height
      for (atom,hand) in ps do
        let entries := (queue 1).filter fun q => q.val.node.current?.map Fin.val == some atom
        unless entries.length == 1 do
          throw (IO.userError s!"oxirane {label} P{atom} one-bond occurrence count changed")
        for q in entries do
          let old := (before.find? (fun row => decide (row.1 = q))).map Prod.snd
          let committed := (after.find? (fun row => decide (row.1 = q))).map Prod.snd
          unless old == none && committed == some (some (some hand)) do
            throw (IO.userError s!"oxirane {label} P{atom} batch transition: {repr old} -> {repr committed}")
          IO.println s!"Oxirane {label} P{atom}, distance 1: {repr old} -> {repr committed}"
    else throw (IO.userError s!"oxirane {label} root is out of range")
  let original : RingGroupedReport.Report :=
    [(0,some (lower,lower)),(1,some (r,s)),(2,some (s,r)),(3,none),(1,some (r,s))]
  let expected := original.map fun row => (rename row.1,row.2)
  unless ringMolecularReportFromRaw? oxirane ⟨positions⟩ (original.map Prod.fst) == some original &&
      ringMolecularReportFromRaw? moved ⟨positions.reverse⟩ (expected.map Prod.fst) == some expected do
    throw (IO.userError "oxirane atom/bond renumbering changed duplicate or refusal report rows")
  IO.println "Oxirane reversed tied arms/bonds preserved the relabeled public report, duplicates and refusal."

/-- The proximal phosphorus hands are opposite. Each phosphorus has exactly
one further uppercase endpoint in the next sphere. The unsigned root keys
agree, but a fixed signed parent class can have different visible widths. -/
private def signedParentWidths : IO Unit := do
  let m := molecule [.C,.P,.P,.O,.C,.P,.F,.P,.F,.H,.H,.Br,.Cl,.Br,.Cl]
    [(0,1),(0,2),(0,3),(0,4),(3,4),(1,5),(1,6),(2,7),(2,8),(4,9),(4,10),
      (5,11),(5,12),(7,13),(7,14)]
  let g := positions ++ [⟨6,1,2⟩,⟨4,0,4⟩,⟨-1,-6,2⟩,⟨0,-4,4⟩]
  let some i := LocalizedChemicalRing.admitRawSpatial? m ⟨g⟩ | throw (IO.userError "diphosphane admission")
  unless LocalizedChemicalRing.coordinatesAdmitted i do throw (IO.userError "diphosphane coordinates")
  if h : 0 < i.certified.certified.input.molecule.atomCount then
    let root : i.certified.Atom := ⟨0,h⟩
    let f := RingGroupedReport.origin i root
    let rows := RingSparseTwinReport.audit i root 0
    let read := RingSphereQueue.reader root (RingSphereQueue.viewOf rows)
    let arms := RingSecondShellDecision.armsFast i f
    let get (j : Nat) := arms.find? fun a => a.occurrence.val.node.current?.map Fin.val == some j
    let some a := get 1 | throw (IO.userError "missing first P arm")
    let some b := get 2 | throw (IO.userError "missing second P arm")
    for rev in [false,true] do
      let some k := RingRetainedStereoRefinement.priority i read rev [] a | throw (IO.userError "first type")
      let some l := RingRetainedStereoRefinement.priority i read rev [] b | throw (IO.userError "second type")
      unless k.deep == l.deep do throw (IO.userError "the arms did not tie through Rule 4a")
      let some x := RingStereoSphereInventory.inventory? i read rev [] a | throw (IO.userError "first inventory")
      let some y := RingStereoSphereInventory.inventory? i read rev [] b | throw (IO.userError "second inventory")
      let width (xs : RingStereoSphereInventory.Inventory) (parent : RS) :=
        (xs.getD 1 0).countP (fun p => (p.head?.bind (·.hand)) = some parent ∧
          (p.getLast?.bind (·.hand)).isSome = true)
      let first : RS := if rev then .S else .R
      unless width x first == 1 && width y first == 0 &&
          width x first.swap == 0 && width y first.swap == 1 do
        throw (IO.userError "unexpected widths below the signed proximal P")
      unless RingStereoSphereInventory.reading .R x == RingStereoSphereInventory.reading .S y &&
          RingStereoSphereInventory.reading .S x == RingStereoSphereInventory.reading .R y &&
          RingStereoSphereInventory.reading .R x != RingStereoSphereInventory.reading .R y do
        throw (IO.userError "unexpected reference exchange")
      IO.println s!"Mirror={rev}, through-4a tie; next visible widths below {repr first}: 1 and 0. R/S exchange matches both complete words."
      (← IO.getStdout).flush
    let s := LocalizedTetrahedralRSPseudoDescriptor.chiral .S
    let r := LocalizedTetrahedralRSPseudoDescriptor.chiral .R
    let lower := LocalizedTetrahedralRSPseudoDescriptor.pseudoasymmetric .s
    let expected := [(0,some (lower,lower)),(1,some (r,s)),(2,some (s,r)),(5,some (r,s)),(7,some (s,r))]
    unless ringMolecularReportFromRaw? m ⟨g⟩ (expected.map Prod.fst) == some expected do
      throw (IO.userError "public report disagrees with Jmol on the two-tier phosphorus arms")
    IO.println "Public raw C/P/P/P/P: sRSRS on the original, sSRSR on reflection."
  else throw (IO.userError "empty graph")

def audit (args : List String) : IO Unit := do
  if args == ["--signed-parent-widths"] then
    signedParentWidths
    return
  if args == ["--inventory-report"] then
    let r := LocalizedTetrahedralRSPseudoDescriptor.chiral .R
    let s := LocalizedTetrahedralRSPseudoDescriptor.chiral .S
    let lower := LocalizedTetrahedralRSPseudoDescriptor.pseudoasymmetric .s
    let expected := [(0,some (lower,lower)),(1,some (r,s)),(2,some (s,r)),(3,none),(1,some (r,s))]
    unless RingStereoInventoryReport.fromRaw? oxirane ⟨positions⟩ (expected.map Prod.fst) == some expected do
      throw (IO.userError "inventory report changed an oxirane descriptor, refusal or repeated row")
    unless RingStereoInventoryReport.fromRaw? (cyclopropane 2) ⟨positions.take 7⟩ [0] == some [(0,none)] do
      throw (IO.userError "inventory report assigned a hand to mixed-H bromofluorocyclopropane")
    IO.println "Inventory report: oxirane s/s, R/S, S/R, refusal, repeated R/S. Mixed-H cyclopropane: refusal."
    return
  if args == ["--isotope-spellings-only"] then
    monodeuteratedHydrogenSpellings
    return
  branchSymmetryControls
  monodeuteratedHydrogenSpellings
  chiralHydrogenSpellings
  ch2CoordinateMotion
  multiCh2CoordinateMotion
  oxiraneHydrogenReadings
  oxiraneRenumberedSnapshots
  let mut conforms := true
  for (count,h1,h2) in [(0,2,2),(2,0,2),(4,0,0)] do
    let m := cyclopropane count
    unless m.implicitHydrogensAt? 1 == some h1 && m.implicitHydrogensAt? 2 == some h2 do
      throw (IO.userError "unexpected implied H count on the cyclopropane arms")
    let ok ← checkReport s!"Cyclopropane, {count} separate H atoms" m
      (positions.take (5 + count)) [(0,none)]
    conforms := conforms && ok
  -- The four H positions can independently be written as vertices. Keep
  -- each surviving H at its original position and renumber the source IDs.
  let base := cyclopropane 0
  for mask in List.range 16 do
    let chosen := (List.range 4).filter fun j => mask.testBit j
    let edges := chosen.zipIdx.map fun (j,k) => (⟨1+j/2,5+k,.single⟩ : RawBond)
    let m := {base with atoms := base.atoms ++ List.replicate chosen.length (.aliphatic .H),
                        bonds := base.bonds ++ edges}
    let xyz := positions.take 5 ++ chosen.filterMap fun j => positions[5+j]?
    unless ringMolecularReportFromRaw? m ⟨xyz⟩ [0] == some [(0,none)] do
      throw (IO.userError s!"ordinary H spelling {mask} changed carbon 0")
  IO.println "All 16 ordinary H spellings leave carbon 0 unassigned."
  let mixed := cyclopropane 2
  let bracket := {mixed with atoms := mixed.atoms.modify 2 fun a => {a with explicitHydrogens? := some 2}}
  let bracketOK ← checkReport "Cyclopropane, counted bracket hydrogens" bracket (positions.take 7) [(0,none)]
  conforms := conforms && bracketOK
  let r := LocalizedTetrahedralRSPseudoDescriptor.chiral .R
  let s := LocalizedTetrahedralRSPseudoDescriptor.chiral .S
  let lower := LocalizedTetrahedralRSPseudoDescriptor.pseudoasymmetric .s
  -- One deuterium really does distinguish the two CH₂ paths. Retain this
  -- isotope as a vertex while completing either spelling of the ordinary H.
  for count in [2,4] do
    let m := cyclopropane count
    let labelled := {m with atoms := m.atoms.modify 5 fun h => {h with isotope? := some 2}}
    let ok ← checkReport s!"Deuterated cyclopropane, {count} separate H atoms" labelled
      (positions.take (5 + count)) [(0,some (s,r))]
    conforms := conforms && ok
  unless (ringMolecularReportFromRaw? (cyclopropane 0) ⟨positions.take 5⟩ [5]).isNone do
    throw (IO.userError "generated hydrogen exposed as a source atom ID")
  for (label,points,p1,p2) in [("original",positions,r,s),
      ("mirror",positions.map (fun p => {p with x := -p.x}),s,r)] do
    let ok ← checkReport s!"Oxirane, {label}" oxirane points
      [(0,some (lower,lower)),(1,some (p1,p2)),(2,some (p2,p1))]
    conforms := conforms && ok
  -- Exchanging Cl and F coordinates at only the second phosphorus makes
  -- both arms R. The carbon now has two identical ligands.
  let equalHands := positions.set 7 ⟨-4,-2,1⟩ |>.set 8 ⟨-1,-4,2⟩
  let ok ← checkReport "Oxirane, same-handed phosphorus arms" oxirane equalHands
    [(0,none),(1,some (r,s)),(2,some (r,s))]
  conforms := conforms && ok
  if args == ["--require-conformance"] && !conforms then
    throw (IO.userError "public report disagrees with the IUPAC controls")

end LocalRuleCoverage

def main := LocalRuleCoverage.audit
