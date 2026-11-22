import TetraStereo.Examples.RingDimethylThiiraneBoundary
import TetraStereo.Engine.RingTerminalReferenceRoles
import TetraStereo.Engine.RingMolecularSchedule
import TetraStereo.Engine.RingRetainedProtiumClass
import TetraStereo.Engine.CentresRing

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace TetraStereo.Examples.RingMethylAncestorRoles
open OneCenter Engine RingTerminalReferenceRoles
open RingDimethylThiiraneBoundary (input molecule spatial)
open RingRetainedTerminalClass (Atom)

def carbon0 : input.certified.Atom := ⟨0,by decide +kernel⟩
def carbon3 : input.certified.Atom := ⟨3,by decide +kernel⟩

private def numbered (n : Fin 13) : input.certified.Atom := ⟨n.val,n.isLt⟩

private theorem root_neighbors : (input.certified.moleculeGraph.neighborFinset carbon0).sort (· ≤ ·) =
    [numbered 1,numbered 2,numbered 3,numbered 4] := by
  let ns := [numbered 1,numbered 2,numbered 3,numbered 4]
  have same : input.certified.moleculeGraph.neighborFinset carbon0 = ns.toFinset := by
    ext b
    rw [input.certified.moleculeGraph.mem_neighborFinset]
    revert b
    decide +kernel
  rw [same]
  apply (List.toFinset_sort (· ≤ ·) (by decide +kernel)).mpr
  decide +kernel

/-- The actual carbon-3 occurrence reached along the C0--C3 molecular bond. -/
def focus : RingActivePairs.Site input := RingRetainedConstitution.occurrence input.certified carbon0
  (.step (slot := 2) (child := (OfficialCIPNode.root carbon0).extend carbon3 0)
    (by
      change _ ∈ ((input.certified.executableOfficialNeighborCopies carbon0).map
        (fun x => (OfficialCIPNode.root carbon0).extend x.1 x.2)).zipIdx
      rw [CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,root_neighbors]
      decide +kernel) (.refl _))

def found := RingRetainedTerminalClass.find? input focus

def methyl : Atom input := ⟨3,by decide +kernel⟩
def olderCenter : Atom input := ⟨0,by decide +kernel⟩
def earlierMark : Atom input := ⟨1,by decide +kernel⟩
def localMark : Atom input := ⟨7,by decide +kernel⟩
def hydrogen8 : Atom input := ⟨8,by decide +kernel⟩
def hydrogen9 : Atom input := ⟨9,by decide +kernel⟩

/-- The three pairwise equivalences, original center and ancestry are direct
facts about the calibrated molecule and its addressed C0--C3 occurrence. -/
theorem found_triple : focus.val.node.provenance = .realAtom ∧
    focus.val.node.current?.map Fin.val = some methyl.val ∧
    olderCenter.val ∈ focus.val.node.history.tail.map Fin.val ∧
    input.molecule.toMoleculeGraph.Adj olderCenter earlierMark ∧
    RingTerminalPair.Equivalent input.molecule methyl localMark hydrogen8 ∧
    RingTerminalPair.Equivalent input.molecule methyl localMark hydrogen9 ∧
    RingTerminalPair.Equivalent input.molecule methyl hydrogen8 hydrogen9 := by decide +kernel

/-- Both marked comparisons can be taken on either geometry. The C0--C1 choice
is a genuine incident reference choice; on dimethylthiirane the separate two-plus-one-plus-one
rule already stops C0 before promotion. -/
theorem methyl_refuses :
    LocalizedChemicalRing.coordinatesAdmitted input = true ∧
      ∀ (rev : Bool) (interpret : Bool → (Nat × Nat × (List Bool × Bool)) → (Nat × Nat × (List Bool × Bool)) → Prop)
        (_ : ∀ b o, ¬interpret b o o) (other : Bool → Atom input → Atom input → Prop)
        (order : List (Atom input)), hydrogen8 ∈ order → hydrogen9 ∈ order →
        ¬order.Pairwise (Higher methyl (historyRoles [(olderCenter,earlierMark)] (some localMark))
          (interpret rev) (other rev)) := by
  refine ⟨RingDimethylThiiraneBoundary.admitted.2,?_⟩
  intro rev interpret ir other order h8 h9 pairs
  have e := found_triple.2.2.2.2.2.2
  let word := ((input.molecule.atoms.get hydrogen9).element.atomicNumber,
    (input.molecule.atomMassAt? hydrogen9).getD 0,
    historyRoles [(olderCenter,earlierMark)] (some localMark) hydrogen9)
  obtain ⟨a,ea⟩ := List.mem_iff_get.mp h8
  obtain ⟨b,eb⟩ := List.mem_iff_get.mp h9
  rcases lt_trichotomy a b with lt | eqn | gt
  · have hit := pairs.rel_get_of_lt lt
    rw [ea,eb] at hit
    rw [Higher,if_pos ⟨e.2.1,e.2.2.1⟩] at hit
    exact ir rev word hit
  · exact e.1 (ea.symm.trans ((congrArg order.get eqn).trans eb))
  · have hit := pairs.rel_get_of_lt gt
    rw [ea,eb] at hit
    rw [Higher,if_pos ⟨e.2.2.1,e.2.1⟩] at hit
    exact ir rev word hit

/-- 1,1-Dimethylcyclopropane. Both carbon ligands in the ring have identical
substitution and both methyls have three protium atoms. -/
def cyclopropane : RawMolecule where
  atoms := List.replicate 5 (.aliphatic .C) ++ List.replicate 10 (.aliphatic .H)
  bonds := molecule.bonds ++ [⟨2,13,.single⟩,⟨2,14,.single⟩]

def moment : SpatialConfiguration := ⟨(List.range 15).map fun n =>
  let t : ℚ := n
  ⟨t,t*t,t*t*t⟩⟩

private def molecularRequest (reflected : Bool) : String :=
  let frames := if reflected then
    ["f 0 S 1 2 3 4","f 1 S 0 2 5 6","f 2 R 1 0 13 14","f 3 S 0 7 8 9","f 4 S 0 10 11 12"]
    else ["f 0 R 1 2 3 4","f 1 R 0 2 5 6","f 2 S 1 0 13 14","f 3 R 0 7 8 9","f 4 R 0 10 11 12"]
  String.intercalate "\n" (["centres-1.0"] ++
    cyclopropane.atoms.map (fun a => s!"a {a.element.atomicNumber} 0 0") ++
    cyclopropane.bonds.map (fun b => s!"b {b.source} {b.target}") ++ frames) ++ "\n"

private def methylRequest (m : RawMolecule) (reflected : Bool) : String :=
  let frames := if reflected then
    ["f 0 S 1 2 3 4","f 1 R 0 2 5 6","f 3 R 0 7 8 9","f 4 S 0 10 11 12"]
    else ["f 0 R 1 2 3 4","f 1 S 0 2 5 6","f 3 S 0 7 8 9","f 4 R 0 10 11 12"]
  String.intercalate "\n" (["centres-1.0"] ++
    m.atoms.map (fun a => s!"a {a.element.atomicNumber} {a.isotope?.getD 0} {a.charge}") ++
    m.bonds.map (fun b => s!"b {b.source} {b.target}") ++ frames) ++ "\n"

private def verifyHydrogens (deuterium reflected : Bool) : IO Unit := do
  let written := molecule.atoms.set 8 {element := .H,isotope? := some 1}
  let atoms := if deuterium then written.set 9 {element := .H,isotope? := some 2} else written
  let m := {molecule with atoms}
  let g := if reflected then ⟨spatial.positions.map CartesianPoint3.reflectX⟩ else spatial
  let some i := LocalizedChemicalRing.admitRawSpatial? m g | throw (IO.userError "isotope intake failed")
  unless LocalizedChemicalRing.coordinatesAdmitted i do throw (IO.userError "unadmitted isotope geometry")
  let request ← IO.ofExcept (CentresRing.request i)
  unless request == methylRequest m reflected do throw (IO.userError s!"unmatched isotope request: {request}")
  let root : i.certified.Atom ← if h : 0 < i.certified.certified.input.molecule.atomCount then pure ⟨0,h⟩
    else throw (IO.userError "absent isotope root")
  let some q := (RingActiveDistanceSchedule.sites i).find? fun q => q.val.root == root &&
      q.val.node.provenance == .realAtom && q.val.node.history.map Fin.val == [3,0] |
    throw (IO.userError "missing original methyl occurrence")
  let result := RingRetainedProtiumClass.find? i q
  if deuterium then
    unless result.isNone do throw (IO.userError "D admitted to a protium triple")
  else
    let some row := result | throw (IO.userError "missing ordinary H/H/¹H equivalence")
    unless row.focus.val == 3 && ([row.a.atom.val,row.b.atom.val,row.c.atom.val].mergeSort (· ≤ ·)) == [7,8,9] &&
        (RingRetainedTerminalClass.find? i q).isNone do
      throw (IO.userError "incorrect ordinary and explicit ¹H class")
  let view := RingActiveDistanceSchedule.snapshot (RingMolecularSchedule.publicationTable i root)
  unless view q == some none do throw (IO.userError s!"C3 ordinary/labelled isotope comparison is unresolved: {repr (view q)}")
  IO.println s!"C0--C3 methyl: H8=¹H, H9 deuterium={deuterium}, reflected={reflected}, triple={result.isSome}, certified absence"

/-- Run the same occurrence experiment when the older center itself has two tied
pairs. The companion pinned request performs a C1 trial at C0 and an H7 trial
at C3. The observable conditional covers their simultaneous retention. -/
def validate : IO Unit := do
  unless (found.map fun c => (c.focus.val,c.a.val,c.b.val,c.c.val)) == some (3,7,8,9) do
    throw (IO.userError "missing dimethylthiirane methyl certificate")
  for rev in [false,true] do
    verifyHydrogens false rev
    verifyHydrogens true rev
    let spatial := if rev then ⟨moment.positions.map CartesianPoint3.reflectX⟩ else moment
    let some i := LocalizedChemicalRing.admitRawSpatial? cyclopropane spatial |
      throw (IO.userError "failed cyclopropane admission")
    unless LocalizedChemicalRing.coordinatesAdmitted i do throw (IO.userError "missing calibrated coordinates")
    let request ← IO.ofExcept (CentresRing.request i)
    unless request == molecularRequest rev do throw (IO.userError s!"unmatched cyclopropane molecular request: {request}")
    let root : i.certified.Atom ← if h : 0 < i.certified.certified.input.molecule.atomCount then pure ⟨0,h⟩
      else throw (IO.userError "absent root")
    let some q := (RingActiveDistanceSchedule.sites i).find? fun q => q.val.root == root &&
        q.val.node.provenance == .realAtom && q.val.node.history.map Fin.val == [3,0] |
      throw (IO.userError "missing retained C3")
    let some c := RingRetainedTerminalClass.find? i q | throw (IO.userError "missing equivalent terminal triple")
    unless (c.focus.val,c.a.val,c.b.val,c.c.val) == (3,7,8,9) do throw (IO.userError "incorrect occurrence binding")
    let center : Atom i ← if h : 0 < i.molecule.atomCount then pure ⟨0,h⟩ else throw (IO.userError "absent C0")
    let older : Atom i ← if h : 1 < i.molecule.atomCount then pure ⟨1,h⟩ else throw (IO.userError "absent C1")
    let current : Atom i ← if h : 7 < i.molecule.atomCount then pure ⟨7,h⟩ else throw (IO.userError "absent H7")
    if remote : center.val ∈ q.val.node.history.tail.map Fin.val ∧
        i.molecule.toMoleculeGraph.Adj center older ∧ i.molecule.toMoleculeGraph.Adj c.focus current then
      have result := ancestor_no_ranking (triple c) [(center,older)] (some current) c.real c.atFocus
        (by simpa using And.intro remote.1 remote.2.1)
      let _ := result
    else throw (IO.userError "unbound marked molecular roles")
    let rows := RingMolecularSchedule.publicationTable i root
    unless RingActiveDistanceSchedule.snapshot rows q == some none do throw (IO.userError "methyl refusal not published")
    IO.println s!"1,1-dimethylcyclopropane reflected={rev}: C0--C3 methyl [7,8,9] refuses"

end TetraStereo.Examples.RingMethylAncestorRoles
assert_kernel_only TetraStereo.Examples.RingMethylAncestorRoles.found_triple
assert_kernel_only TetraStereo.Examples.RingMethylAncestorRoles.methyl_refuses
