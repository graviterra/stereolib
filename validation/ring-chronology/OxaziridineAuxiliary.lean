import TetraStereo.Engine.RingSparseTwinReport
import TetraStereo.Engine.RingOxaziridinePublication
import TetraStereo.Engine.RingOriginPyramidalEarly

/-! Occurrence-specific oxaziridine nitrogen controls on synthetic coordinates.
The same N has different constitutional ligand orders when reached directly or
through O. A second graph admits a simple path visiting both carbon ligands
before N; their closure origins, rather than their identical terminal atomic
words, decide their order. These are molecular evaluator regressions, not
experimental geometry or an absolute-configuration attribution. -/
open TetraStereo.OneCenter TetraStereo.Engine
open CertifiedLocalizedCIPInput
open RingActivePairs (Site Arm)
open RingActiveDistanceSchedule (distance)

namespace OxaziridineAuxiliary

private def molecule (linked : Bool) : RawMolecule where
  atoms := (([.N,.O,.C,.C] : List Element) ++ if linked then [Element.C,Element.C] else []).map AtomSpec.aliphatic
  bonds := ([(0,1),(1,2),(2,0),(0,3)] ++
    if linked then [(3,4),(4,5),(5,2)] else []).map fun (a,b) => ⟨a,b,.single⟩

private def spatial (linked reflected : Bool) : SpatialConfiguration :=
  let ps := (List.range (if linked then 6 else 4)).map fun n =>
    let t : ℚ := n + 1
    (⟨t,t*t,t*t*t⟩ : CartesianPoint3)
  ⟨if reflected then ps.map CartesianPoint3.reflectX else ps⟩

private def check (ok : Bool) (why : String) : IO Unit :=
  unless ok do throw (IO.userError why)

private def input (linked reflected : Bool) : IO LocalizedChemicalRing.Input := do
  let m := molecule linked
  let g := spatial linked reflected
  let some (out,pos) := RingHydrogenCompletion.prepare? m g
    | throw (IO.userError "hydrogen completion failed")
  check ((RingHydrogenCompletion.plan out).isEmpty) "completion did not close H plan"
  let some i := LocalizedChemicalRing.admitRawSpatial? out pos
    | throw (IO.userError "completed structural admission failed")
  check (LocalizedChemicalRing.coordinatesAdmitted i) "completed coordinate admission failed"
  check (RingOxaziridineNitrogen.constrainedRaw out 0) "completed oxaziridine motif missing"
  return i

private def physical (i : LocalizedChemicalRing.Input) (row : List Nat) : Option RingNestedActivePair.Labels :=
  let hand := do
    let points ← row.mapM (fun n => i.spatial.positions[n]?)
    match points with
    | [o,c,k,n] => descriptorOfPriorityOrderedPoints? [o,c,k,RingPyramidalPublication.phantomPoint o c k n]
    | _ => none
  hand.map fun h => (.chiral h,.chiral h.swap)

private def atom (i : LocalizedChemicalRing.Input) (n : Nat) : IO i.certified.Atom := do
  let some a := (List.finRange i.certified.certified.input.molecule.atomCount)[n]?
    | throw (IO.userError s!"missing atom {n}")
  return a

private def occurrence (i : LocalizedChemicalRing.Input) (root : i.certified.Atom)
    (history : List Nat) : IO (Site i) := do
  let depth := history.length - 1
  let some q := (RingGlobalComparison.queue i root depth).find? fun q =>
      q.val.node.history.map Fin.val == history && q.val.node.provenance == .realAtom
    | throw (IO.userError s!"missing real eligible occurrence {history}")
  check ((RingPyramidalPublication.focusP i q).map Fin.val == some 0) "auxiliary nitrogen not selected"
  return q

private def arm (i : LocalizedChemicalRing.Input) (q : Site i) (n : Nat) : IO (Arm i) := do
  let some a := (RingRetainedAuxiliary.frame i.certified q).find? fun a =>
      a.occurrence.val.node.current?.map Fin.val == some n
    | throw (IO.userError s!"missing incident direction {n}")
  return a

private def key (i : LocalizedChemicalRing.Input) (a : Arm i) : IO RingRetainedChemicalTrace.Key := do
  let some k := RingRetainedChemicalTrace.key? i a
    | throw (IO.userError "missing constitutional key")
  return k

/-- Inspect the exact committed prefix and its predecessor. `audit_exact`
proves these restored sparse rows equal the actual public sphere-store rows. -/
private def stored (i : LocalizedChemicalRing.Input) (root : i.certified.Atom)
    (q : Site i) (expected : Option RingNestedActivePair.Labels) : IO Unit := do
  let cut := distance q
  let rows := RingSparseTwinReport.audit i root cut
  let preceding := RingSparseTwinReport.audit i root (cut+1)
  let entry := (rows.find? fun p => p.1 == q).map Prod.snd
  check (entry == some (some expected)) s!"wrong addressed row at {q.val.node.history.map Fin.val}: {repr entry}"
  check (!(preceding.any fun p => p.1 == q)) "occurrence was stored before its sphere committed"
  check ((rows.filter fun p => p.1 == q).length == 1) "addressed occurrence duplicated"

private def small (reflected : Bool) : IO Unit := do
  let i ← input false reflected
  let root ← atom i 2
  let direct ← occurrence i root [0,2]
  let viaO ← occurrence i root [0,1,2]
  let directC ← arm i direct 2
  let directK ← arm i direct 3
  let viaC ← arm i viaO 2
  let viaK ← arm i viaO 3
  check (directC.occurrence.val.node.provenance == .realAtom &&
    directK.occurrence.val.node.provenance == .realAtom) "direct carbon directions must both be real"
  check (viaC.occurrence.val.node.provenance == .ringDuplicate 0 &&
    viaK.occurrence.val.node.provenance == .realAtom) "via-O carbon direction provenance"
  let dc ← key i directC
  let dk ← key i directK
  let vc ← key i viaC
  let vk ← key i viaK
  check (decide (RingRetainedChemicalPreorder.orderWord dk < RingRetainedChemicalPreorder.orderWord dc))
    "direct order must put ring carbon above methyl"
  check (decide (RingRetainedChemicalPreorder.orderWord vc < RingRetainedChemicalPreorder.orderWord vk))
    "via-O order must put real methyl above terminal ring-carbon duplicate"
  let a := physical i [1,2,3,0]
  let b := physical i [1,3,2,0]
  check (a == some (.chiral (if reflected then .R else .S),.chiral (if reflected then .S else .R)))
    "independent direct phantom frame must give S/R and reflect"
  check (a.isSome && b == a.map (fun p => (p.2,p.1))) "carbon exchange must reverse the physical hand"
  check (RingOriginPyramidalEarly.early? i direct == some a &&
    RingOriginPyramidalEarly.early? i viaO == some b) "moving the focus changed a single-cycle hand"
  stored i root direct a
  stored i root viaO b
  IO.println s!"small oxaziridine mirror={reflected}: direct={repr a}, via-O={repr b}; distinct addressed public rows"

private def bothDuplicates (reflected : Bool) : IO Unit := do
  let i ← input true reflected
  let root ← atom i 3
  -- The alternate carbon path visits C2 and C3 before reaching N through O1.
  let q ← occurrence i root [0,1,2,5,4,3]
  let c ← arm i q 2
  let k ← arm i q 3
  check (c.occurrence.val.node.provenance == .ringDuplicate 3 &&
    k.occurrence.val.node.provenance == .ringDuplicate 0)
    "both-carbon duplicate origins must be distinct (3 and 0)"
  let ck ← key i c
  let kk ← key i k
  check (ck.atomic.word == kk.atomic.word) "terminal carbon atomic words must tie"
  check (decide (ck.duplicate.word < kk.duplicate.word)) "the earlier origin must win Rule 1b"
  check (decide (RingRetainedChemicalPreorder.orderWord ck < RingRetainedChemicalPreorder.orderWord kk))
    "complete carbon order must retain the duplicate-origin decision"
  let expected := physical i [1,3,2,0]
  check expected.isSome "synthetic physical frame degenerate"
  let alternative := physical i [1,2,3,0]
  check (alternative == expected.map Prod.swap && alternative != expected) "exchanging carbon arms must reverse the hand"
  check (RingOriginPyramidalEarly.early? i q == some alternative) "focus-distance ranking must give the opposite auxiliary hand"
  stored i root q expected
  IO.println s!"linked oxaziridine mirror={reflected}: both carbon ligands duplicate, origins3/0, public={repr expected}, active={repr alternative}"

end OxaziridineAuxiliary

def main : IO Unit := do
  for reflected in [false,true] do
    OxaziridineAuxiliary.small reflected
    OxaziridineAuxiliary.bothDuplicates reflected
