import TetraStereo.Engine.RingNumericPairReport

/-! A C–O–S ring bears constitutionally identical P–P arms. Terminal Cl/Br
coordinates control the second hand in each pair. All four auxiliary hands
are determined by atomic numbers and nonzero physical frames. -/
open TetraStereo.OneCenter TetraStereo.Engine
namespace NumericPairReport

def molecule : RawMolecule where
  atoms := [.C,.O,.S,.P,.P,.F,.F,.P,.P,.Cl,.Cl,.Br,.Br].map AtomSpec.aliphatic
  bonds := ([(0,1),(1,2),(2,0),(0,3),(0,4),(3,5),(4,6),(3,7),(4,8),(7,9),(8,10),(7,11),(8,12)] :
    List (Nat × Nat)).map (fun (a,b) => ⟨a,b,.single⟩)

def geometry (swapArms : Bool) : SpatialConfiguration :=
  let clA : CartesianPoint3 := ⟨-2,1,0⟩
  let brA : CartesianPoint3 := ⟨-2,2,-1⟩
  let clB : CartesianPoint3 := ⟨-2,-1,0⟩
  let brB : CartesianPoint3 := ⟨-2,-2,1⟩
  ⟨[⟨0,0,0⟩,⟨1,1,1⟩,⟨1,-1,-1⟩,⟨-1,1,-1⟩,⟨-1,-1,1⟩,⟨-1,2,-1⟩,⟨-1,-2,1⟩,
    ⟨-2,1,-1⟩,⟨-2,-1,1⟩,if swapArms then brA else clA,if swapArms then clB else brB,
    if swapArms then clA else brA,if swapArms then brB else clB]⟩

def audit (swapped : Bool) : IO RS := do
  let xyz := geometry swapped
  let physical (ids : List Nat) := (ids.mapM (fun a => xyz.positions[a]?)).bind
    CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints?
  let some a₁ := physical [7,5,0,3] | throw (IO.userError "flat proximal A")
  let some b₁ := physical [8,6,0,4] | throw (IO.userError "flat proximal B")
  let some a₂ := physical [11,9,3,7] | throw (IO.userError "flat distal A")
  let some b₂ := physical [12,10,4,8] | throw (IO.userError "flat distal B")
  -- Independent Jmol 14.29.17 control reads root, proximal A, distal A,
  -- proximal B, distal B as SRSRR and RRRRS, respectively.
  let knownHands : List RS := if swapped then [.R,.R,.R,.S] else [.R,.S,.R,.R]
  unless [a₁,a₂,b₁,b₂] == knownHands do throw (IO.userError "auxiliary control mismatch")
  let likeA := a₁ == a₂
  unless a₁ == b₁ && likeA != (b₁ == b₂) do throw (IO.userError "expected one like pair")
  let some hand := physical (if likeA then [2,3,4,1] else [2,4,3,1]) | throw (IO.userError "flat ring carbon")
  unless hand == (if swapped then RS.R else RS.S) do throw (IO.userError "ring-carbon control mismatch")
  let some i := LocalizedChemicalRing.admitRawSpatial? molecule xyz | throw (IO.userError "ring admission")
  if nonempty : 0 < i.certified.certified.input.molecule.atomCount then
    let c : i.certified.Atom := ⟨0,nonempty⟩
    let q := RingGroupedReport.origin i c
    let rows := RingSphereStore.rows i c (RingActiveDistanceSchedule.height i + 1)
    IO.eprintln s!"swapped={swapped} scored from {rows.length} stored occurrences"
    let r := RingSphereQueue.reader c (RingSphereQueue.viewOf rows)
    let arms := RingRetainedAuxiliary.frame i.certified q
    let key (id : Nat) : Option RingFullPathEligibility.Key := do
      let arm ← arms.find? (fun (u : RingActivePairs.Arm i) => u.occurrence.val.node.current?.map Fin.val == some id)
      RingFullPathEligibility.key? i r false arm
    let some a := key 3 | throw (IO.userError "proximal A has no priority")
    let some b := key 4 | throw (IO.userError "proximal B has no priority")
    unless a.throughFourA == b.throughFourA do throw (IO.userError "arms separated before Rule 4b")
    let scores := (RingBinaryPairScore.value a.bestFourB,RingBinaryPairScore.value b.bestFourB)
    unless scores == (if likeA then (3,2) else (2,3)) do throw (IO.userError s!"Rule 4b scores {repr scores}")
    IO.println s!"swapped={swapped} Rule 4a tie, Rule 4b scores {repr scores}"
  else throw (IO.userError "missing carbon")
  let expected : RingGroupedReport.Report := [(0,some (.chiral hand,.chiral hand.swap))]
  IO.eprintln s!"swapped={swapped} starting public ring report"
  let native := RingHydrogenReport.fromRaw? molecule xyz [0]
  unless native == some expected do throw (IO.userError s!"native {repr native}, expected {repr expected}")
  IO.eprintln s!"swapped={swapped} starting numeric ring report"
  let actual := RingNumericPairReport.fromRaw? molecule xyz [0]
  unless actual == native do throw (IO.userError s!"numeric {repr actual}, native {repr native}")
  IO.println s!"swapped={swapped} physical hands A={repr (a₁,a₂)} B={repr (b₁,b₂)} numeric and public root={repr hand}"
  return hand

end NumericPairReport

def main : IO Unit := do
  let a ← NumericPairReport.audit false
  let b ← NumericPairReport.audit true
  unless a == b.swap do throw (IO.userError "exchanging the two ligand configurations failed to invert the ring assignment")
