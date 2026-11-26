import TetraStereo.Engine.PublicAPI
import TetraStereo.Engine.RingMarkedTreeReport
import TetraStereo.Engine.RingMarkedDistanceOrder
import TetraStereo.Engine.RingSparseTwinReport
import TetraStereo.Engine.RingBridgeheadNitrogen

open TetraStereo.OneCenter TetraStereo.Engine
namespace EqualDistanceSource
open private indexedKey indexedKey_exact from TetraStereo.Engine.RingFullPathEligibility

/-- Share both unmarked priority readers across the compared molecular arms. -/
def cachedKeys (i : LocalizedChemicalRing.Input) (r : RingNestedActivePair.Reader i)
    (root a b : RingActivePairs.Arm i) : Option (RingFullPathEligibility.Key × RingFullPathEligibility.Key) :=
  RingOccurrenceStereo.withRankReaders i r false [] root fun edges unitRank =>
    RingOccurrenceStereo.withRankReaders i r false [.lowercase] root fun lowerEdges lowerRank =>
      let key := fun q => do
        let u ← unitRank q
        let l ← lowerRank q
        let ar ← RingFullPathPairs.wordWith r false edges unitRank .R q
        let as' ← RingFullPathPairs.wordWith r false edges unitRank .S q
        let fixed ← RingFullPathPairs.wordWith r false lowerEdges lowerRank .R q
        return (⟨u.deep,max ar as',l.word,fixed⟩ : RingFullPathEligibility.Key)
      do return (← key a, ← key b)

theorem cachedKeys_exact (i : LocalizedChemicalRing.Input) (r : RingNestedActivePair.Reader i)
    (root a b : RingActivePairs.Arm i) : cachedKeys i r root a b =
    (do return (← RingFullPathEligibility.key? i r false a,
      ← RingFullPathEligibility.key? i r false b)) := by
  rw [indexedKey_exact]
  simp only [cachedKeys,indexedKey,RingOccurrenceStereo.withRankReaders_eq]


private def atD {i : LocalizedChemicalRing.Input} (edges : RingActivePairs.Arm i → List (RingActivePairs.Arm i)) :
    Nat → List (RingActivePairs.Arm i) → List (RingActivePairs.Arm i)
  | 0,qs => qs
  | n+1,qs => atD edges n (qs.flatMap edges)

private theorem atD_exact (i : LocalizedChemicalRing.Input) (d : Nat) (qs : List (RingActivePairs.Arm i)) :
    atD (RingRule5Shape.kids i) d qs = RingSpherePopulation.atDistance i d qs := by
  induction d generalizing qs with
  | zero => rfl
  | succ n ih => exact ih (qs.flatMap (RingRule5Shape.kids i))

/-- Preserve multiplicity: both arms must carry exactly one mark at distance2. -/
def hitCounts (i : LocalizedChemicalRing.Input) (r : RingNestedActivePair.Reader i)
    (root a b : RingActivePairs.Arm i) : List (Nat × Nat) :=
  RingOccurrenceStereo.withRankReaders i r false [] root fun edges _ =>
    (List.range 3).map fun d =>
      let count := fun q => ((atD edges d [q]).filter fun c =>
        c.occurrence.val.node.current?.map Fin.val == some 1).length
      (count a,count b)

theorem hitCounts_exact (i : LocalizedChemicalRing.Input) (r : RingNestedActivePair.Reader i)
    (root a b : RingActivePairs.Arm i) : hitCounts i r root a b =
    (List.range 3).map (fun d =>
      let count := fun q => ((RingSpherePopulation.atDistance i d [q]).filter fun c =>
        c.occurrence.val.node.current?.map Fin.val == some 1).length
      (count a,count b)) := by
  simp only [hitCounts,RingOccurrenceStereo.withRankReaders_eq,atD_exact]

private def viewWith {i : LocalizedChemicalRing.Input}
    (edges : RingActivePairs.Arm i → List (RingActivePairs.Arm i))
    (rank : RingActivePairs.Arm i → Option RingStereoSiblingPass.Branch) (atom : Nat) :
    (n : Nat) → RingActivePairs.Arm i → RingMarkedTreeFold.Shape n
  | 0,_ => ()
  | n+1,q => ((((rank q).map RingStereoSiblingPass.Branch.deep).getD [],RingGroupedMark.bit atom q),
      ((edges q).map (viewWith edges rank atom n) : Multiset (RingMarkedTreeFold.Shape n)))

private theorem viewWith_exact (i : LocalizedChemicalRing.Input) (r : RingNestedActivePair.Reader i)
    (atom : Nat) : ∀ n q,
    viewWith (RingRule5Shape.kids i) (RingRetainedStereoRefinement.priority i r false [.lowercase]) atom n q =
      RingMarkedTreeFold.view i r atom n q := by
  intro n
  induction n with
  | zero => intro q; rfl
  | succ n ih =>
    intro q
    have funcs := funext ih
    simp only [viewWith,RingMarkedTreeFold.view,RingRule5Shape.key,funcs]

/-- Decode the same unordered tree with one shared through-4c reader. -/
def cachedTreeWord (i : LocalizedChemicalRing.Input) (r : RingNestedActivePair.Reader i)
    (root q : RingActivePairs.Arm i) (atom : Nat) : Option RingRetainedChemicalTrace.Word :=
  RingOccurrenceStereo.withRankReaders i r false [.lowercase] root fun edges rank =>
    let n := i.certified.localizedRerootCursorBudget q + 1
    (RingMarkedTreeOrder.reconstruct n (viewWith edges rank atom n q)).map RingStereoSiblingPass.Branch.word

theorem cachedTreeWord_exact (i : LocalizedChemicalRing.Input) (r : RingNestedActivePair.Reader i)
    (root q : RingActivePairs.Arm i) (atom : Nat) :
    cachedTreeWord i r root q atom = RingMarkedTreeReport.word? i r atom q := by
  simp only [cachedTreeWord,RingOccurrenceStereo.withRankReaders_eq,RingMarkedTreeReport.word?]
  exact congrArg (fun t => (RingMarkedTreeOrder.reconstruct _ t).map RingStereoSiblingPass.Branch.word)
    (viewWith_exact i r atom (i.certified.localizedRerootCursorBudget q + 1) q)

/-- Unconstrained three-coordinate nitrogen remains outside the selected
pyramidal policy. The structural exclusion is an explicit hypothesis. -/
theorem nitrogen_degree_three_ineligible {i : LocalizedChemicalRing.Input} (a : i.certified.Atom)
    (nitrogen : (i.molecule.atoms[a.val]?).map AtomSpec.element = some .N)
    (degree : Fintype.card (i.certified.moleculeGraph.Neighbor a) = 3)
    (unconstrained : RingPyramidalNitrogen.constrained i a = false) :
    RingPyramidalPublication.eligible i a = false := by
  have off : RingPyramidalPublication.phosphorus i a = false := by
    cases found : i.molecule.atoms[a.val]? with
    | none => simp only [found,Option.map_none] at nitrogen; contradiction
    | some spec =>
      have element : spec.element = .N := by simpa only [found,Option.map_some,Option.some.injEq] using nitrogen
      simp [RingPyramidalPublication.phosphorus,found,element,unconstrained]
  simp [RingPyramidalPublication.eligible,degree,off]

theorem nitrogen_degree_three_not_eligible {i : LocalizedChemicalRing.Input} (a : i.certified.Atom)
    (nitrogen : (i.molecule.atoms[a.val]?).map AtomSpec.element = some .N)
    (degree : Fintype.card (i.certified.moleculeGraph.Neighbor a) = 3)
    (unconstrained : RingPyramidalNitrogen.constrained i a = false)
    (q : RingActivePairs.Site i) (current : q.val.node.current? = some a) :
    ¬ RingEligibleGraph.Eligible (RingPyramidalPublication.eligible i) q := by
  rintro ⟨_,b,hb,allowed⟩
  have same : a = b := Option.some.inj (current.symm.trans hb)
  subst b
  rw [nitrogen_degree_three_ineligible a nitrogen degree unconstrained] at allowed
  contradiction

/-- Every occurrence of this atom is omitted from every auxiliary inventory,
for any original root and any scheduled distance. -/
theorem nitrogen_degree_three_not_auxiliary {i : LocalizedChemicalRing.Input} (a : i.certified.Atom)
    (nitrogen : (i.molecule.atoms[a.val]?).map AtomSpec.element = some .N)
    (degree : Fintype.card (i.certified.moleculeGraph.Neighbor a) = 3)
    (unconstrained : RingPyramidalNitrogen.constrained i a = false)
    (root : i.certified.Atom) (d : Nat) (q : RingActivePairs.Site i)
    (current : q.val.node.current? = some a) :
    q ∉ RingEligibleGraph.queue i (RingPyramidalPublication.eligible i) root d := by
  intro listed
  have candidate := ((RingEligibleGraph.inventory i (RingPyramidalPublication.eligible i) root) d q).mp listed
  exact nitrogen_degree_three_not_eligible a nitrogen degree unconstrained q current candidate.1.2.2

/-- The local evaluator emits known absence at every such occurrence for any
incoming reader, independently of geometry or previously published labels. -/
theorem nitrogen_degree_three_publish_none {i : LocalizedChemicalRing.Input} (a : i.certified.Atom)
    (nitrogen : (i.molecule.atoms[a.val]?).map AtomSpec.element = some .N)
    (degree : Fintype.card (i.certified.moleculeGraph.Neighbor a) = 3)
    (unconstrained : RingPyramidalNitrogen.constrained i a = false)
    (q : RingActivePairs.Site i) (current : q.val.node.current? = some a)
    (r : RingActiveDistanceSchedule.View i) :
    RingPyramidalPublication.publish i q r = some none :=
  RingChemicalGraphProof.skips i q r (nitrogen_degree_three_not_eligible a nitrogen degree unconstrained q current)

theorem nitrogen_degree_three_state_none {i : LocalizedChemicalRing.Input} (a : i.certified.Atom)
    (nitrogen : (i.molecule.atoms[a.val]?).map AtomSpec.element = some .N)
    (degree : Fintype.card (i.certified.moleculeGraph.Neighbor a) = 3)
    (unconstrained : RingPyramidalNitrogen.constrained i a = false)
    (q : RingActivePairs.Site i) (current : q.val.node.current? = some a) :
    RingChemicalGraphProof.state i q = some none :=
  (RingChemicalGraphProof.state_eq i q).trans
    (nitrogen_degree_three_publish_none a nitrogen degree unconstrained q current _)

/-- Three-coordinate prepared nitrogen lacking the structural constraint
receives no root descriptor under this policy. Geometry is not a premise. -/
theorem nitrogen_degree_three_root_none {i : LocalizedChemicalRing.Input} (a : i.certified.Atom)
    (nitrogen : (i.molecule.atoms[a.val]?).map AtomSpec.element = some .N)
    (degree : Fintype.card (i.certified.moleculeGraph.Neighbor a) = 3)
    (unconstrained : RingPyramidalNitrogen.constrained i a = false) :
    RingChemicalGraphProof.root i a = some none := by
  rw [RingChemicalGraphProof.root,RingEligibleGraph.root_exact _ (RingChemicalGraphProof.skips i)]
  exact nitrogen_degree_three_state_none a nitrogen degree unconstrained (RingGroupedReport.origin i a)
    (RingGroupedReport.origin_address i a).2.2

def molecule : RawMolecule where
  atoms := [.C,.N,.N,.N,.N,.O,.S,.O,.S].map AtomSpec.aliphatic
  bonds := ([(0,1),(0,2),(0,3),(0,4),(1,5),(5,2),(2,6),(6,3),(3,7),(7,4),(4,8),(8,1)] :
    List (Nat × Nat)).map (fun (a,b) => ⟨a,b,.single⟩)

def spatial (reflected : Bool) : SpatialConfiguration := ⟨(List.range 9).map fun t =>
  let x : ℚ := t
  ⟨if reflected then -x else x,x*x,x*x*x⟩⟩

private def firstDifference {α : Type} [BEq α] : Nat → List α → List α → Option Nat
  | _,[],[] => none
  | n,a::as,b::bs => if a == b then firstDifference (n+1) as bs else some n
  | n,_,_ => some n

private def require (ok : Bool) (why : String) : IO Unit := unless ok do throw (IO.userError why)
private def progress (message : String) : IO Unit := do
  IO.println message
  (← IO.getStdout).flush

def audit (dir : String) (report : Bool) (reflected : Bool) : IO Unit := do
  let some i := LocalizedChemicalRing.admitRawSpatial? molecule (spatial reflected)
    | throw (IO.userError "equal-distance input admission")
  require (LocalizedChemicalRing.coordinatesAdmitted i && molecule.valenceOK?) "valence/geometry"
  let tag := if reflected then "mirror" else "original"
  let packet : CentresRing.Molecular.SourceReceipt ← IO.ofExcept
    ((Lean.Json.parse (← IO.FS.readFile (dir ++ "/" ++ tag ++ ".source.json"))).bind Lean.fromJson?)
  require (packet.receipt.release == CentresRing.releaseCommit &&
    packet.receipt.molecularRequest == (← IO.ofExcept (CentresRing.request i [0]))) "source request/release"
  require (packet.observed.length == 18 && packet.receipt.traces.length == 1) "source inventory"
  let some trace := packet.receipt.traces[0]? | throw (IO.userError "source trace")
  require (trace.atom == 0 && trace.label == (if reflected then "S" else "R") &&
    trace.updates.isEmpty && trace.passes.length == 2) "source root trace"
  let some pass := trace.passes[1]? | throw (IO.userError "source final pass")
  let some trial := pass.trials[1]? | throw (IO.userError "source marked trial")
  require (trial.mark == some 1 && trial.start == [1,2,3,4] &&
    trial.comparisons == [⟨1,2,1⟩,⟨2,3,1⟩,⟨3,4,-1⟩,⟨2,4,-1⟩,⟨1,4,1⟩]) "source mark1 trial identity"
  let expected : CentresRing.Molecular.Observation := ⟨2,4,
    [("Rule1a",0),("Rule1b",0),("Rule2",0),("Rule3",0),("Rule4a",0),
      ("Rule4b",0),("Rule4c",0),("Rule5New",0),("Rule6",-1)]⟩
  require (packet.observed[12]? == some expected &&
    (packet.observed.filter (fun x => x.left == 2 && x.right == 4 &&
      x.rules.getLast?.map Prod.snd == some (-1))).length == 1 &&
    (trace.comparisons.filter (fun x => x.left == 2 && x.right == 4 && x.value == -1)).length == 1)
    "unique ordered source prefix bound to mark1 trial"
  progress s!"{tag}: pinned mark1 comparison2<4 after eight zero rules"
  if h : 0 < i.certified.certified.input.molecule.atomCount then
    let c : i.certified.Atom := ⟨0,h⟩
    let f := RingGroupedReport.origin i c
    -- This is the source packet's explicitly configured inventory [0]. Its
    -- empty auxiliary store is a controlled Rule6 input, not the closed graph's
    -- scheduled public store once constrained nitrogen sites are selected.
    let r := RingSphereQueue.reader c (RingSphereQueue.viewOf [])
    progress s!"{tag}: configured source inventory=[0]; explicit empty auxiliary store (not the closed graph prior)"
    let arms := RingRetainedAuxiliary.frame i.certified f
    let arm (a : Nat) := arms.find? (fun q => q.occurrence.val.node.current?.map Fin.val == some a)
    let some a := arm 2 | throw (IO.userError "arm2")
    let some b := arm 4 | throw (IO.userError "arm4")
    let rootArm : RingActivePairs.Arm i := ⟨f,none⟩
    require (hitCounts i r rootArm a b == [(0,0),(0,0),(1,1)]) "one mark each at equal distance2"
    progress s!"{tag}: explicit empty-store control; equal-distance counts=(1,1) at sphere2"
    let some (oldA,oldB) := cachedKeys i r rootArm a b | throw (IO.userError "ordinary cached pair")
    require (oldA == oldB) "complete ordinary arms must tie"
    let some left := RingGroupedMark.arm? i r 1 a | throw (IO.userError "marked arm2")
    let some right := RingGroupedMark.arm? i r 1 b | throw (IO.userError "marked arm4")
    require (compare left.2.word right.2.word == .lt && left.2.value == 0 && right.2.value == 0)
      "native marked arm4 must win"
    let zeroLevel := fun level : List (List Nat) => level.all (fun row => row.all (· == 0))
    require (zeroLevel (left.2.levels[0]?.getD []) && zeroLevel (right.2.levels[0]?.getD []) &&
      firstDifference 0 left.2.levels right.2.levels == some 1) "first discordant sphere must be2"
    let thirdLeft := left.2.levels[1]?.getD []
    let thirdRight := right.2.levels[1]?.getD []
    let offset := 1 + ((left.2.levels.take 1).map List.length).sum
    let within := firstDifference 0 thirdLeft thirdRight
    require (firstDifference 0 left.2.word right.2.word == within.map (offset + ·)) "sphere row offset"
    let some treeLeft := cachedTreeWord i r rootArm a 1 | throw (IO.userError "tree arm2")
    let some treeRight := cachedTreeWord i r rootArm b 1 | throw (IO.userError "tree arm4")
    require (treeLeft == left.2.word && treeRight == right.2.word) "independent tree decoding"
    progress s!"{tag}: ordinary tie; native/tree2<4; first flat row={firstDifference 0 left.2.word right.2.word}"
    progress s!"left2={left.2.word} right4={right.2.word}"
    if report then
      progress s!"{tag}: source final label={trace.label} for configured inventory[0]; no closed-graph carbon assignment is asserted"
  else throw (IO.userError "empty input")
/-- Protect the reflection-consistency control used in source review: lowercase
s/r is rejected, whereas uppercase S/R is accepted. This is a finite kernel
calculation, not a universal external nomenclature correspondence theorem. -/
theorem reflection_case_control :
    RingNestedActivePair.consistent (.pseudoasymmetric .s,.pseudoasymmetric .r) = false ∧
      RingNestedActivePair.consistent (.chiral .S,.chiral .R) = true := by
  decide +kernel

/-- Check the measured Jmol-agreeing carbon and established bridgehead N
assignments on both physical geometries, before and after the coordinate swap.
These finite outcomes do not assert universal external-source correspondence. -/
def auditBridgeheads (swapBridges : Bool) : IO Unit := do
  let g := spatial false
  let g := if swapBridges then
    ⟨(g.positions.set 7 (g.positions[8]?.getD ⟨0,0,0⟩)).set 8 (g.positions[7]?.getD ⟨0,0,0⟩)⟩ else g
  let tag := if swapBridges then "bridge7/8-coordinates-swapped" else "original"
  let some i := LocalizedChemicalRing.admitRawSpatial? molecule g | throw (IO.userError "bridgehead admission")
  for n in [1,2,3,4] do
    if h : n < i.certified.certified.input.molecule.atomCount then
      let a : i.certified.Atom := ⟨n,h⟩
      require ((i.molecule.atoms[n]?).map AtomSpec.element == some .N &&
        decide (Fintype.card (i.certified.moleculeGraph.Neighbor a) = 3) &&
        RingBridgeheadNitrogen.constrained i a && RingPyramidalPublication.eligible i a)
        "prepared constrained three-coordinate N must be selected"
    else throw (IO.userError "missing bridgehead")
  let expected : List RS := if swapBridges then [.S,.S,.R,.R] else [.S,.S,.R,.S]
  -- S>O>C are strict atomic-number priorities; the focus as the fourth
  -- determinant point has the same sign as its constructed lowest phantom.
  let frames : List (List Nat) := [[8,5,0,1],[6,5,0,2],[6,7,0,3],[8,7,0,4]]
  let direct := frames.map fun ids => (ids.mapM (fun n => g.positions[n]?)).bind
    CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints?
  require (direct == expected.map some) "independent S>O>C>phantom determinant"
  progress s!"{tag}: starting actual raw report IDs[0,1,2,3,4]; N expectation={repr expected}"
  let actual := RingHydrogenReport.fromRaw? molecule g [0,1,2,3,4]
  progress s!"{tag}: actual raw report={repr actual}"
  let some rows := actual | throw (IO.userError "raw bridgehead report failed")
  require (rows.map Prod.fst == [0,1,2,3,4]) "raw diagnostic requested inventory"
  let expectedPairs := expected.map fun h => some
    (LocalizedTetrahedralRSPseudoDescriptor.chiral h,LocalizedTetrahedralRSPseudoDescriptor.chiral h.swap)
  require ((rows.drop 1).map Prod.snd == expectedPairs) "bridgehead N original/mirror label pairs"
  let carbonHand : RS := if swapBridges then .S else .R
  let carbonExpected : Option RingNestedActivePair.Labels := some
    (.chiral carbonHand,.chiral carbonHand.swap)
  require (rows.head?.map Prod.snd == some carbonExpected) "measured Jmol-agreeing carbon original/mirror pair"
  progress s!"{tag}: N pairs and measured Jmol-agreeing carbon pair verified; lowercase s/r rejected and uppercase S/R accepted by kernel-checked control"

/-- All 24 presentations change only the order of the four C0--N raw bond
records. Atom IDs, positions, the remaining bond records and expected physical
assignments remain fixed. No source replay is repeated in this mode. -/
def auditBondOrders : IO Unit := do
  let g := spatial false
  let g : SpatialConfiguration :=
    ⟨(g.positions.set 7 (g.positions[8]?.getD ⟨0,0,0⟩)).set 8 (g.positions[7]?.getD ⟨0,0,0⟩)⟩
  let rootRecords := molecule.bonds.take 4
  let otherRecords := molecule.bonds.drop 4
  let orders := rootRecords.permutations
  let distinctTargets := (orders.map (fun bs => bs.map (fun b => b.target))).eraseDups
  require (orders.length == 24 && distinctTargets.length == 24)
    "four C--N records must give 24 distinct permutations"
  let expected : RingGroupedReport.Report := [
    (0,some (.chiral .S,.chiral .R)),
    (1,some (.chiral .S,.chiral .R)),
    (2,some (.chiral .S,.chiral .R)),
    (3,some (.chiral .R,.chiral .S)),
    (4,some (.chiral .R,.chiral .S))]
  for (order,k) in orders.zipIdx do
    let m : RawMolecule := {molecule with bonds := order ++ otherRecords}
    progress s!"bond-order variant{k}: C--N records={order.map (fun b => (b.source,b.target))}"
    let actual := RingHydrogenReport.fromRaw? m g [0,1,2,3,4]
    require (actual == some expected) s!"bond-order variant{k} label pairs differ: {repr actual}"
    progress s!"bond-order variant{k}: public carbon S/R and N SSRR/RRSS verified"
  progress "All 24 raw C--N bond-record orders preserve the measured swapped-geometry carbon and N assignments."

end EqualDistanceSource

def main (args : List String) : IO Unit := do
  if args.contains "--bond-orders" then
    EqualDistanceSource.auditBondOrders
    return
  if args.contains "--bridgeheads" then
    EqualDistanceSource.auditBridgeheads false
    EqualDistanceSource.auditBridgeheads true
    return
  let dir ← match args[0]? with
    | some dir => pure dir
    | none => throw (IO.userError "expected receipt directory and optional --report, or --bridgeheads / --bond-orders")
  EqualDistanceSource.audit dir (args.contains "--report") false
  EqualDistanceSource.audit dir (args.contains "--report") true

assert_kernel_only EqualDistanceSource.cachedKeys_exact
assert_kernel_only EqualDistanceSource.hitCounts_exact
assert_kernel_only EqualDistanceSource.cachedTreeWord_exact

assert_kernel_only EqualDistanceSource.nitrogen_degree_three_ineligible
assert_kernel_only EqualDistanceSource.nitrogen_degree_three_not_auxiliary
assert_kernel_only EqualDistanceSource.nitrogen_degree_three_publish_none
assert_kernel_only EqualDistanceSource.nitrogen_degree_three_state_none
assert_kernel_only EqualDistanceSource.nitrogen_degree_three_root_none

assert_kernel_only EqualDistanceSource.reflection_case_control
