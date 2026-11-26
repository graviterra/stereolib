import TetraStereo.Engine.RingBridgeheadReport
import TetraStereo.Engine.RingBridgeheadNitrogen
import TetraStereo.Engine.RingOxaziridineNitrogen

/-! Executable graph transcription for the adamantan-2-one-derived
N-tert-butyl spiro-oxaziridine identified as VI by Bjørgo and Boyd (1973),
DOI 10.1039/P29730001575. Coordinates below are synthetic moment-curve
coordinates; no experimental geometry or normative absolute configuration is claimed.

Adamantane is K4 with every edge subdivided once. Vertices 0..3 are its
four degree-three bridgeheads; vertices 4..9 subdivide edges 01,02,03,12,13,23.
The former methylene 4 is the oxaziridine spiro carbon. The N10-O11-C4
triangle is attached to a pendant tert-butyl carbon 12 (methyls 13..15).
This regression covers a particular stable nitrogen with a pendant alkyl arm;
it does not claim that every three-membered N ring is stable. -/
open TetraStereo.OneCenter TetraStereo.Engine
open RingHydrogenCompletion CertifiedLocalizedCIPInput

private def cageEdges : List (Nat × Nat) :=
  [(0,4),(4,1),(0,5),(5,2),(0,6),(6,3),
   (1,7),(7,2),(1,8),(8,3),(2,9),(9,3)]

private def molecule : RawMolecule where
  atoms := (List.replicate 10 (.aliphatic .C)) ++
    [.aliphatic .N,.aliphatic .O] ++ List.replicate 4 (.aliphatic .C)
  bonds := (cageEdges ++ [(4,10),(10,11),(11,4),(10,12),(12,13),(12,14),(12,15)]).map
    fun (a,b) => ⟨a,b,.single⟩

private def geometry (mirror : Bool) : SpatialConfiguration :=
  let ps := (List.range 16).map fun n =>
    let t : ℚ := n + 1
    (⟨t,t*t,t*t*t⟩ : CartesianPoint3)
  ⟨if mirror then ps.map CartesianPoint3.reflectX else ps⟩

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def neighborNumbers (m : RawMolecule) (a excluded : Nat) : List Nat :=
  (((m.writtenNeighbors a).filter (· != excluded)).filterMap fun n =>
    (m.atoms[n]?).map fun atom => atom.element.atomicNumber).mergeSort (· ≥ ·)

private def independentHand (g : SpatialConfiguration) : Option RS := do
  let o ← g.positions[11]?
  let spiro ← g.positions[4]?
  let tertButyl ← g.positions[12]?
  let nitrogen ← g.positions[10]?
  descriptorOfPriorityOrderedPoints? [o,spiro,tertButyl,
    RingPyramidalPublication.phantomPoint o spiro tertButyl nitrogen]

/-- Minimal neutral N-alkyl oxaziridine, with the ring methylene and N-methyl
hydrogens left implicit. These controls test the graph family, not configurational
stability of every possible substitution pattern. -/
private def smallOxaziridine : RawMolecule where
  atoms := ([.N,.O,.C,.C] : List Element).map AtomSpec.aliphatic
  bonds := [(0,1),(1,2),(2,0),(0,3)].map fun (a,b) => ⟨a,b,.single⟩

private def graphControls : IO Unit := do
  let positive := smallOxaziridine
  let openChain := { positive with bonds := positive.bonds.filter fun b => !(b.source == 1 && b.target == 2) }
  let aziridine := { positive with atoms := positive.atoms.set 1 (.aliphatic .C) }
  let nHydrogen := { positive with atoms := positive.atoms.set 3 (.aliphatic .H) }
  let nOxygen := { positive with atoms := positive.atoms.set 3 (.aliphatic .O) }
  let externalCarbonOH := { positive with
    atoms := positive.atoms ++ [.aliphatic .O]
    bonds := positive.bonds ++ [⟨3,4,.single⟩] }
  check (positive.stereochemicalAdmissible? && RingOxaziridineNitrogen.constrainedRaw positive 0)
    "neutral N-alkyl oxaziridine positive control"
  for (name,m) in [("open chain",openChain),("aziridine",aziridine),
      ("N-H",nHydrogen),("N-heteroatom substituent",nOxygen),
      ("external carbon bonded to oxygen",externalCarbonOH)] do
    check m.stereochemicalAdmissible? s!"{name} control unexpectedly inadmissible"
    check (!RingOxaziridineNitrogen.constrainedRaw m 0) s!"{name} incorrectly selected as N-alkyl oxaziridine"

def main : IO Unit := do
  graphControls
  check (molecule.atomCount == 16 && molecule.bonds.length == 19) "heavy graph inventory"
  check (molecule.stereochemicalAdmissible?) "source structural admission"
  check ((molecule.writtenNeighbors 10).length == 3) "N must have degree three"
  check (neighborNumbers molecule 4 10 == [8,6,6]) "spiro-carbon ligand sphere must be O,C,C"
  check (neighborNumbers molecule 12 10 == [6,6,6]) "tert-butyl ligand sphere must be C,C,C"
  check (RingOxaziridineNitrogen.constrainedRaw molecule 10) "spiro oxaziridine family selection"
  check (!RingBridgeheadNitrogen.constrainedRaw molecule 10) "theta gate unexpectedly includes pendant N arm"
  let hand := independentHand (geometry false)
  let mirrorHand := independentHand (geometry true)
  check (hand == some .S && mirrorHand == some .R) "synthetic independent original/reflected S/R readings"
  check (hand.isSome && mirrorHand == hand.map RS.swap) "independent phantom frame must be nonzero and reflect"
  for mirror in [false,true] do
    let g := geometry mirror
    let some source := LocalizedChemicalRing.admitRawSpatial? molecule g
      | throw (IO.userError "actual source admission failed")
    check (LocalizedChemicalRing.coordinatesAdmitted source) "source coordinate admission"
    let some (out,pos) := prepare? molecule g
      | throw (IO.userError "actual H completion failed")
    check (out.atomCount == 39 && (plan out).isEmpty) "C14H23NO completion inventory/closure"
    check ((out.writtenNeighbors 10).length == 3 && !RingBridgeheadNitrogen.constrainedRaw out 10)
      "completed N topology/gate changed"
    let some completed := LocalizedChemicalRing.admitRawSpatial? out pos
      | throw (IO.userError "completed graph admission failed")
    check (LocalizedChemicalRing.coordinatesAdmitted completed) "completed coordinate admission"
    let expected := (independentHand g).map fun h =>
      [(10,some (LocalizedTetrahedralRSPseudoDescriptor.chiral h,
        LocalizedTetrahedralRSPseudoDescriptor.chiral h.swap))]
    let actual := RingHydrogenReport.fromRaw? molecule g [10]
    check (actual == expected) "public spiro N assignment differs from independent priorities/phantom frame"
    let some root := (List.finRange completed.certified.certified.input.molecule.atomCount)[4]?
      | throw (IO.userError "spiro root missing")
    let some auxiliary := (RingGlobalComparison.queue completed root 1).find? fun q =>
        q.val.node.current?.map Fin.val == some 10 && decide (q.val.node.provenance = .realAtom)
      | throw (IO.userError "real N auxiliary occurrence below spiro root missing")
    check (!auxiliary.val.address.isEmpty &&
      (RingPyramidalPublication.focusP completed auxiliary).map Fin.val == some 10)
      "public pyramidal selector omitted N at an auxiliary occurrence"
    IO.println s!"spiro oxaziridine: mirror={mirror}, independent hand={repr (independentHand g)}, public N row={repr actual}; root and auxiliary selection passed"

  -- The arithmetic centroid of O11=(12,144,1728), C4=(5,25,125),
  -- and C12=(13,169,2197) is (10,338/3,1350). Only N10 moves.
  let flat : SpatialConfiguration :=
    ⟨(geometry false).positions.set 10 ⟨10,(338 : ℚ)/3,1350⟩⟩
  check (independentHand flat == none) "centroid nitrogen must have zero phantom determinant"
  let some flatSource := LocalizedChemicalRing.admitRawSpatial? molecule flat
    | throw (IO.userError "flat-N source admission failed")
  check (LocalizedChemicalRing.coordinatesAdmitted flatSource) "flat N must not invalidate carbon coordinates"
  let some (flatOut,flatPositions) := prepare? molecule flat
    | throw (IO.userError "flat-N completion failed")
  let some flatCompleted := LocalizedChemicalRing.admitRawSpatial? flatOut flatPositions
    | throw (IO.userError "flat-N completed admission failed")
  check (LocalizedChemicalRing.coordinatesAdmitted flatCompleted) "flat-N completed carbon coordinates"
  check (RingHydrogenReport.fromRaw? molecule flat [10] == some [(10,none)])
    "admitted flat nitrogen must yield a completed refusal"
  IO.println "spiro oxaziridine: admitted centroid-flat N gives a completed refusal; external-carbon heteroatom control excluded"
