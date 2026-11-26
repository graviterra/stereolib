import TetraStereo.Engine.PublicAPI
import TetraStereo.Engine.RingMarkedTreeReport
import TetraStereo.Engine.RingMarkedDistanceOrder
import TetraStereo.Engine.RingSparseTwinReport

open TetraStereo.OneCenter TetraStereo.Engine
namespace DeepMarkedSource
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

/-- Reuse one checked molecular child reader for every compared distance. -/
def cachedGraph (i : LocalizedChemicalRing.Input) (r : RingNestedActivePair.Reader i)
    (root a b : RingActivePairs.Arm i) : Bool :=
  RingOccurrenceStereo.withRankReaders i r false [] root fun edges _ =>
    let hit := fun q d => (atD edges d [q]).any fun c => c.occurrence.val.node.current?.map Fin.val == some 1
    (hit a 3 && (List.range 4).all (fun j => !hit b j)) &&
      (List.range 3).all (fun d => !hit a d && !hit b d)

theorem cachedGraph_exact (i : LocalizedChemicalRing.Input) (r : RingNestedActivePair.Reader i)
    (root a b : RingActivePairs.Arm i) : cachedGraph i r root a b =
    (RingMarkedDistanceOrder.winsAt i 1 a b 3 &&
      (List.range 3).all (fun d => !RingMarkedDistanceOrder.hitsAt i 1 a d &&
        !RingMarkedDistanceOrder.hitsAt i 1 b d)) := by
  simp only [cachedGraph,RingOccurrenceStereo.withRankReaders_eq,atD_exact,
    RingMarkedDistanceOrder.winsAt,RingMarkedDistanceOrder.hitsAt]

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

def molecule : RawMolecule where
  atoms := List.replicate 9 (.aliphatic .C) ++ List.replicate 16 (.aliphatic .H)
  bonds := (([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(5,6),(6,7),(7,8),(8,0)] : List (Nat × Nat)) ++
    (List.range 8).flatMap (fun k => [(k+1,9+2*k),(k+1,10+2*k)] )).map
      (fun (a,b) => ⟨a,b,.single⟩)

def spatial (reflected : Bool) : SpatialConfiguration := ⟨(List.range 25).map fun t =>
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

def audit (dir : String) (native tree : Bool) (reflected : Bool) : IO Unit := do
  let some i := LocalizedChemicalRing.admitRawSpatial? molecule (spatial reflected)
    | throw (IO.userError "spiro[4.4]nonane admission")
  require (LocalizedChemicalRing.coordinatesAdmitted i && molecule.valenceOK?) "valence/geometry"
  let packet : CentresRing.Molecular.SourceReceipt ← IO.ofExcept
    ((Lean.Json.parse (← IO.FS.readFile (dir ++ "/" ++
      (if reflected then "mirror" else "original") ++ "-root.source.json"))).bind Lean.fromJson?)
  require (packet.receipt.release == CentresRing.releaseCommit &&
    packet.receipt.molecularRequest == (← IO.ofExcept (CentresRing.request i [0]))) "source request/release"
  require (packet.observed.length == 15 && packet.receipt.traces.length == 1) "source inventory"
  let some trace := packet.receipt.traces[0]? | throw (IO.userError "source trace")
  require (trace.atom == 0 && trace.label == "-" && trace.updates.isEmpty && trace.passes.length == 2)
    "root trace and empty source prior"
  let some pass := trace.passes[1]? | throw (IO.userError "source final pass")
  let some trial := pass.trials[1]? | throw (IO.userError "source marked trial")
  require (trial.mark == some 1 && trial.start == [1,4,5,8] &&
    trial.comparisons == [⟨1,4,1⟩,⟨4,5,1⟩,⟨5,8,0⟩]) "source mark1 trial identity"
  let expected : CentresRing.Molecular.Observation := ⟨4,5,
    [("Rule1a",0),("Rule1b",0),("Rule2",0),("Rule3",0),("Rule4a",0),
      ("Rule4b",0),("Rule4c",0),("Rule5New",0),("Rule6",1)]⟩
  require (packet.observed[10]? == some expected &&
    (packet.observed.filter (fun x => x.left == 4 && x.right == 5 &&
      x.rules.getLast?.map Prod.snd == some 1)).length == 1 &&
    (trace.comparisons.filter (fun x => x.left == 4 && x.right == 5 && x.value == 1)).length == 1)
    "unique ordered source Rule6 prefix bound to mark1 trial"
  progress s!"mirror={reflected} source mark1/4>5 prefix bound to molecular request"
  if h : 0 < i.certified.certified.input.molecule.atomCount then
    let c : i.certified.Atom := ⟨0,h⟩
    let f := RingGroupedReport.origin i c
    let sparse := RingSparseTwinReport.sparse i c 0
    require sparse.isEmpty "public final sparse prior must be empty"
    let r := RingSphereQueue.reader c (RingSphereQueue.viewOf sparse)
    progress s!"mirror={reflected} public final sparse reader empty (sparse_exact)"
    let arms := RingRetainedAuxiliary.frame i.certified f
    let arm (a : Nat) := arms.find? (fun q => q.occurrence.val.node.current?.map Fin.val == some a)
    let some a := arm 4 | throw (IO.userError "arm 4")
    let some b := arm 5 | throw (IO.userError "arm 5")
    let rootArm : RingActivePairs.Arm i := ⟨f,none⟩
    require (cachedGraph i r rootArm a b) "first marked sphere must be3"
    progress s!"mirror={reflected} native graph first distinguishing marked sphere=3: path0-4-3-2-1"
    unless native do return
    progress "starting complete ordinary keys"
    let some (oldA,oldB) := cachedKeys i r rootArm a b | throw (IO.userError "ordinary cached pair")
    require (oldA == oldB) "ordinary arms must tie through Rule5"
    progress "ordinary complete keys tie; starting native marked words"
    let some left := RingGroupedMark.arm? i r 1 a | throw (IO.userError "marked left4")
    let some right := RingGroupedMark.arm? i r 1 b | throw (IO.userError "marked right5")
    require (compare left.2.word right.2.word == .gt) "marked comparison must favor 4"
    let zeroLevel := fun level : List (List Nat) => level.all (fun row => row.all (· == 0))
    require (left.2.value == 0 && right.2.value == 0 && (left.2.levels.take 2).all zeroLevel)
      "left own bit and first two spheres zero"
    require ((right.2.levels.take 2).all zeroLevel) "right first two spheres zero"
    require ((left.2.levels[2]?.getD []).any (fun row => row.contains 1) &&
      zeroLevel (right.2.levels[2]?.getD []) &&
      firstDifference 0 left.2.levels right.2.levels == some 2) "first differing sphere must be3"
    let offset := 1 + ((left.2.levels.take 2).map List.length).sum
    let within := firstDifference 0 (left.2.levels[2]?.getD []) (right.2.levels[2]?.getD [])
    require (firstDifference 0 left.2.word right.2.word == within.map (offset + ·))
      "flattened first difference must match sphere3 row widths"
    progress s!"mirror={reflected} native first difference sphere3/word-row={firstDifference 0 left.2.word right.2.word}; left4={left.2.word} right5={right.2.word}"
    if tree then
      progress "starting independent tree decoder"
      let some treeLeft := cachedTreeWord i r rootArm a 1 | throw (IO.userError "tree left4")
      let some treeRight := cachedTreeWord i r rootArm b 1 | throw (IO.userError "tree right5")
      require (treeLeft == left.2.word && treeRight == right.2.word) "tree decoder"
    IO.println s!"mirror={reflected} first difference={firstDifference 0 left.2.word right.2.word}"
    IO.println s!"left4={left.2.word} right5={right.2.word}"
    IO.println s!"source comparisons={packet.observed.length}"
  else throw (IO.userError "empty input")
end DeepMarkedSource

def main (args : List String) : IO Unit := do
  let dir ← match args[0]? with
    | some dir => pure dir
    | none => throw (IO.userError "expected receipt directory and optional --native / --tree")
  let tree := args.contains "--tree"
  let native := tree || args.contains "--native"
  DeepMarkedSource.audit dir native tree false
  DeepMarkedSource.audit dir native tree true

assert_kernel_only DeepMarkedSource.cachedKeys_exact

assert_kernel_only DeepMarkedSource.cachedGraph_exact

assert_kernel_only DeepMarkedSource.cachedTreeWord_exact
