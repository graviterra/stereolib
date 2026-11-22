import TetraStereo.Examples.LocalizedChemicalRingNestedLifetime
import TetraStereo.OneCenter.LocalizedChemicalRingPartitionTable

set_option autoImplicit false

namespace TetraStereo.Examples.LocalizedChemicalRingPropellaneLifetime

open OneCenter Engine.LocalizedChemicalRing
open LocalizedGenericMarkedRecalculation
open LocalizedChemicalRingPreparedContextRecursion
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedChemicalRingNestedLifetime (replacement)

def point (x y z : ℚ) : CartesianPoint3 := ⟨x,y,z⟩

/-- Rational test coordinates with the bridgeheads on the z-axis and the three methylenes
in the equatorial plane. All five four-neighbor frames have nonzero volume. -/
def spatial : SpatialConfiguration := ⟨[
  point 0 0 1, point 0 0 (-1), point 2 0 0, point (-1) 2 0, point (-1) (-2) 0,
  point 3 1 0, point 3 (-1) 0, point (-1) 3 0, point (-2) 2 0,
  point (-2) (-2) 0, point (-1) (-3) 0]⟩

def smiles := "C123C(C1)(C2)C3"

/-- The same parser expansion used by public admission. Absence can never witness the
graph theorem below since the inventory and all thirteen bonds are checked. -/
def parsedMol : RawMolecule :=
  match parseAndNormalizeOpenSMILESCertified smiles [] with
  | .ok parsed => parsed.result.parsed.withExplicitHydrogens
  | .error _ => {atoms := [], bonds := []}

private abbrev Id := Fin 11

def PreservesGraph (e : Equiv.Perm (Fin 11)) : Prop :=
  (∀ i : Id, parsedMol.atoms[(e i).val]? = parsedMol.atoms[i.val]?) ∧
    ∀ i j : Id, parsedMol.bondOrder (e i) (e j) = parsedMol.bondOrder i j

/-- Exchange the first and third methylenes, carrying their attached hydrogens. -/
private def exchange : Equiv.Perm Id :=
  ((Equiv.swap 2 4).trans (Equiv.swap 5 9)).trans (Equiv.swap 6 10)

theorem scalar_exchange : ∃ e : Equiv.Perm Id, PreservesGraph e ∧
    e 0 = 0 ∧ e 1 = 1 ∧ e 3 = 3 ∧ e 2 = 4 ∧ e 4 = 2 := by
  refine ⟨exchange, ?_, ?_⟩
  · unfold PreservesGraph
    decide +kernel
  · decide +kernel

private theorem neighbors (i : Id) :
    parsedMol.bondOrder 1 i ≠ 0 ↔ i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
  fin_cases i <;> decide +kernel

/-- With both references fixed every atom of the distal frame is fixed. With only
reference 3, the preceding theorem exhibits the symmetry behind the surviving tie. -/
theorem retaining_fixes_frame (e : Equiv.Perm Id) (graph : PreservesGraph e)
    (root : e 0 = 0) (distal : e 1 = 1) (old : e 2 = 2) (newMark : e 3 = 3) :
    ∀ i : Id, parsedMol.bondOrder 1 i ≠ 0 → e i = i := by
  have bond := graph.2 1 4
  rw [distal] at bond
  change parsedMol.bondOrder 1 (e 4) = parsedMol.bondOrder 1 (4 : Id) at bond
  have edge : parsedMol.bondOrder 1 (4 : Id) ≠ 0 := (neighbors 4).mpr (by decide)
  have image := (neighbors (e 4)).mp (by rw [bond]; exact edge)
  have last : e 4 = 4 := by
    rcases image with a | b | c | d
    · exact False.elim ((by decide : (4 : Id) ≠ 0) (e.injective (a.trans root.symm)))
    · exact False.elim ((by decide : (4 : Id) ≠ 2) (e.injective (b.trans old.symm)))
    · exact False.elim ((by decide : (4 : Id) ≠ 3) (e.injective (c.trans newMark.symm)))
    · exact d
  intro i hi
  rcases (neighbors i).mp hi with rfl | rfl | rfl | rfl
  exacts [root,old,newMark,last]

/-- Geometric readback from the two strict priority orders in the nested comparison. -/
theorem coordinate_readings :
    readback? (fun i => spatial.positions[i]?) [0,2,3,4] = some .S ∧
    readback? (fun i => spatial.positions[i]?) [0,2,4,3] = some .R := by decide +kernel

private def get {α : Type} (reason : String) : Option α → IO α
  | some value => pure value
  | none => throw (IO.userError reason)

private def expect (ok : Bool) (message : String) : IO Unit := unless ok do throw (IO.userError message)

private def framesBelow (mol : RawMolecule) : Nat → RawMolecule.CanonicalBranchNode →
    List RawMolecule.CanonicalBranchNode
  | 0, _ => []
  | fuel+1, node =>
    (if (frameAtoms? mol node).isSome then [node] else []) ++
      (mol.canonicalChildren node).flatMap (framesBelow mol fuel)

def run (includeReports : Bool := false) : IO Unit := do
  let input ← match admitSmilesSpatial? smiles spatial with
    | .ok (some input) => pure input
    | _ => throw (IO.userError "propellane admission")
  let mol := input.molecule
  expect (mol == parsedMol) "public intake differs from symmetry witness"
  expect (coordinatesAdmitted input && mol.valenceOK?) "valence and geometry"
  expect ((mol.atoms.map AtomSpec.element == List.replicate 5 .C ++ List.replicate 6 .H) &&
    mol.bonds.length == 13 && mol.bondOrder 0 1 == 1 &&
    [2,3,4].all (fun bridge => mol.bondOrder 0 bridge == 1 && mol.bondOrder 1 bridge == 1)) "connectivity"
  let full := input.certified.localizedRerootCarrierCache
    (LocalizedMarkedRetainedMolecularSelection.retainedCarrierFuel input.certified)
  let rootAtom : input.certified.Atom ← if h : 0 < input.certified.certified.input.molecule.atomCount
    then pure ⟨0,h⟩ else throw (IO.userError "empty input")
  let slice := CertifiedLocalizedCIPInput.localizedRerootRootSliceCache full rootAtom
  let root := canonicalCenterRoot 0
  let ids := List.range mol.atoms.length
  let pairs := ids.flatMap fun i => ids.map fun j => [i,j]
  let contexts := [] :: ((ids.map fun i => [i]) ++ pairs ++
    ([2,3,4].flatMap fun i => pairs.map fun pair => i :: pair))
  let ops := LocalizedChemicalRingPartitionTable.operations input.certified slice.reader mol
    (framesBelow mol (structuralDepth mol root + 2) root) contexts
  let node ← get "central bond" ((mol.canonicalChildren root).find? (·.atom == 1))
  let atoms ← get "distal bridgehead" (frameAtoms? mol node)
  let geom := inputGeometry input.certified
  for keep in [true,false] do
    let step := if keep then rawStepPrepared? ops else replacement ops
    let rootUnder := childrenUnder mol (factsOfStep step mol (structuralDepth mol root)) geom [] root
    let observed ← get "unmarked root observations" (prepareComparison? [] rootUnder [])
    let rootAtoms ← get "root ligands" (frameAtoms? mol root)
    let (pos,adjacent) ← get "unmarked root order" (ops.contextOrder observed root [])
    let eligible := eligibleOf rootAtoms pos adjacent
    expect (consistent adjacent && eligible.length == 3 && [2,3,4].all eligible.contains)
      "actual unmarked root must select the three methylenes"
    IO.println s!"root eligible={eligible}"
    let under := childrenUnder mol (factsOfStep step mol (structuralDepth mol node)) geom [] node
    let obs ← get "descendants" (prepareComparison? [] under [2])
    let (ord,rel) ← get "inherited ranking" (ops.contextOrder obs node [2])
    let selected := eligibleOf atoms ord rel
    expect (selected.length == 2 && selected.contains 3 && selected.contains 4) "nested eligibility"
    let inherited ← get "inherited ligand order" (atomsAt? atoms ord)
    expect (inherited.take 2 == [0,2] && rel == [some .gt,some .gt,some .eq])
      "inherited partition must be 0 > 2 > {3,4}"
    let refs := if keep then [2] else []
    let letters := selected.map (evaluateFallback? mol ops geom [] node refs under)
    expect (if keep then (letters == [some .R,some .S] || letters == [some .S,some .R])
      else letters == [none,none]) "lifetime comparison"
    for mark in selected do
      let ctx := refs ++ [mark]
      let aux ← get "regenerated auxiliary facts" (prepareComparison? [] under ctx)
      let (order,adjacent) ← get "promoted ranking" (ops.contextOrder aux node ctx)
      let actual ← get "ranked atoms" (atomsAt? atoms order)
      let other := if mark == 3 then 4 else 3
      let expectedOrder := if keep then [0,2,mark,other] else [0,mark,2,other]
      let expectedAdjacent := if keep then [some .gt,some .gt,some .gt] else [some .gt,some .gt,some .eq]
      expect (aux.isEmpty && actual == expectedOrder && adjacent == expectedAdjacent)
        "unexpected regenerated state or promoted partition"
      -- The copied ranks are 0,1,2,2 in the inherited order. Only the tied
      -- methylenes consult the fresh scalar. Compare every pair, including ties.
      let before := fun a b => compare (min (inherited.idxOf b) 2) (min (inherited.idxOf a) 2)
      let fresh := fun a b => compare (a == mark) (b == mark)
      let strictOrder := [0,2,mark,other]
      expect (atoms.all fun a => atoms.all fun b =>
        copyPriorities before fresh a b == compare (strictOrder.idxOf b) (strictOrder.idxOf a))
        "copied priorities disagree with accumulated order"
      IO.println s!"retaining={keep} context={ctx} atoms={actual} eligible={eligibleOf atoms order adjacent} aux={aux.length}"
    IO.println s!"selected={selected} nested={repr letters}"
  if includeReports then
    let rows ← input.certified.canonicalTetrahedralCenters.mapM fun c => do
      let q := canonicalCenterRoot c.1.val
      let slice := CertifiedLocalizedCIPInput.localizedRerootRootSliceCache full c.1
      let cached := LocalizedChemicalRingPartitionTable.operations input.certified slice.reader mol
        (framesBelow mol (structuralDepth mol q + 2) q) contexts
      let read := fun op => LocalizedChemicalRingPartitionTable.descriptor op mol geom [] contexts
        (structuralDepth mol q) [] q
      let replaced := read (replacement cached)
      let retained := read (rawStepPrepared? cached)
      IO.println s!"center={c.1.val} replacement={repr replaced} retained={repr retained}"
      pure (c.1.val, replaced, retained)
    let retained := rows.map (fun (i,_,v) => (i,v))
    let replaced := rows.map (fun (i,v,_) => (i,v))
    let s := some (LocalizedTetrahedralRSPseudoDescriptor.pseudoasymmetric .s)
    let expected := [(0,s),(1,s),(2,none),(3,none),(4,none)]
    expect (retained == expected) "accumulated bridgehead report"
    expect (replaced == expected) "replacement bridgehead report"
    IO.println s!"replacement report={repr replaced}"
    IO.println s!"retained report={repr retained}"

#eval run true

end TetraStereo.Examples.LocalizedChemicalRingPropellaneLifetime
assert_kernel_only TetraStereo.Examples.LocalizedChemicalRingPropellaneLifetime.scalar_exchange
assert_kernel_only TetraStereo.Examples.LocalizedChemicalRingPropellaneLifetime.retaining_fixes_frame
assert_kernel_only TetraStereo.Examples.LocalizedChemicalRingPropellaneLifetime.coordinate_readings
