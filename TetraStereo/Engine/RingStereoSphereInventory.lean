import TetraStereo.Engine.RingUnorderedSphereReading
import TetraStereo.Engine.RingFullPathEligibility

/-! One reference-independent molecular inventory serves both fixed reference hands.
Each edge carries its earlier-stage priority and its actual auxiliary hand, when visible.
The unordered expansion visits children of neutral occurrences as well. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingStereoSphereInventory
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm)
open RingNestedActivePair (Reader)
open RingRetainedChemicalTrace (Word)
open RingRetainedReferenceGroup (Path)
open RingStereoSiblingPass (Branch)
open RingFullPathPairs (FullVisit Oracle stepKey bitOf handAt likeAt)
open RingUnorderedSphereReading (layers? readRow)

structure Edge where
  earlier : List Word
  hand : Option RS
  deriving DecidableEq, Repr

abbrev SignedPath := List Edge

def project (seed : RS) (p : SignedPath) : Path :=
  p.map fun e => stepKey e.earlier (e.hand.map (· == seed))

structure Visit (i : Input) where
  arm : Arm i
  path : SignedPath

private def image {i : Input} (seed : RS) (v : Visit i) : FullVisit i :=
  ⟨v.arm,project seed v.path⟩

private def start {i : Input} (r : Reader i) (rev : Bool) (q : Arm i) : Visit i :=
  ⟨q,[⟨[],handAt i r rev q⟩]⟩

private def nextWith {i : Input} (r : Reader i) (rev : Bool)
    (children : Arm i → List (Arm i)) (rank : Arm i → Option Branch) (v : Visit i) :
    Option (List (Visit i)) :=
  (children v.arm).mapM fun c => do
    let k ← rank c
    return ⟨c,v.path ++ [⟨k.deep,handAt i r rev c⟩]⟩

private theorem map_traversal {α β γ : Type} (f : α → Option β) (g : β → γ) (xs : List α) :
    (xs.mapM f).map (List.map g) = xs.mapM (fun x => (f x).map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mapM_cons,← ih]
    cases f x <;> cases xs.mapM f <;> rfl

private theorem next_projects {i : Input} (o : Oracle i) (r : Reader i) (rev : Bool)
    (seed : RS) (v : Visit i) :
    ((nextWith r rev i.certified.executableLocalizedRerootChildren o.rank?) v).map (List.map (image seed)) =
      o.next? (likeAt i r rev seed) (image seed v) := by
  unfold nextWith Oracle.next?
  rw [map_traversal]
  apply congrArg (fun read => (i.certified.executableLocalizedRerootChildren v.arm).mapM read)
  funext c
  cases o.rank? c <;> simp [image,project,likeAt]

/-- Forget occurrence identities after expansion. Each distance retains an
unordered multiset of full paths, with all multiplicities. -/
abbrev Inventory := List (Multiset SignedPath)

private def eraseVisits {i : Input} (spheres : List (List (Visit i))) : Inventory :=
  spheres.map fun row => ↑(row.map Visit.path)

def inventoryWith {i : Input} (r : Reader i) (rev : Bool) (children : Arm i → List (Arm i))
    (rank : Arm i → Option Branch) (q : Arm i) : Option Inventory :=
  (layers? (nextWith r rev children rank) (i.certified.localizedRerootCursorBudget q + 1)
    [start r rev q]).map eraseVisits

def inventory? (i : Input) (r : Reader i) (rev : Bool)
    (stages : List RingRetainedStereoRefinement.Observation) (q : Arm i) : Option Inventory :=
  inventoryWith r rev i.certified.executableLocalizedRerootChildren
    (RingRetainedStereoRefinement.priority i r rev stages) q

private def cachedInventory (i : Input) (r : Reader i) (rev : Bool)
    (stages : List RingRetainedStereoRefinement.Observation) (q : Arm i) : Option Inventory :=
  RingOccurrenceStereo.withRankReaders i r rev stages q fun edges rank => inventoryWith r rev edges rank q

@[csimp] private theorem cached_exact : @inventory? = @cachedInventory := by
  funext i r rev stages q
  unfold cachedInventory inventory?
  rw [RingOccurrenceStereo.withRankReaders_eq]
  rfl

def sphere (seed : RS) (s : Multiset SignedPath) : List Bool :=
  Quotient.liftOn s (readRow (project seed) bitOf) (fun _ _ p =>
    RingUnorderedSphereReading.readRow_perm (project seed) bitOf p)

def reading (seed : RS) (spheres : Inventory) : List Bool := spheres.flatMap (sphere seed)

private theorem erase_reading {i : Input} (seed : RS) (xs : List (List (Visit i))) :
    reading seed (eraseVisits xs) =
      xs.flatMap (readRow (FullVisit.path ∘ image seed) bitOf) := by
  simp only [reading,eraseVisits,List.flatMap_map]
  apply List.flatMap_congr
  intro row _
  change readRow (project seed) bitOf (row.map Visit.path) = _
  rw [← RingUnorderedSphereReading.readRow_map]
  rfl

/-- A single inventory reconstructs every bit of either reference reading,
including failure, for every molecular arm, stage list, reader and geometry. -/
theorem reading_exact (i : Input) (r : Reader i) (rev : Bool)
    (stages : List RingRetainedStereoRefinement.Observation) (seed : RS) (q : Arm i) :
    (inventory? i r rev stages q).map (reading seed) =
      RingFullPathPairs.stageWords i r rev stages seed q := by
  let o := RingFullPathPairs.stage i r rev stages
  let bit := likeAt i r rev seed
  let v := start r rev q
  let next := nextWith r rev i.certified.executableLocalizedRerootChildren o.rank?
  let n := i.certified.localizedRerootCursorBudget q + 1
  have run := RingUnorderedSphereReading.read_exact (image seed) FullVisit.path bitOf next
    (o.next? bit) (next_projects o r rev seed) v n
  change ((layers? next n [v]).map eraseVisits).map (reading seed) = _
  simp only [Option.map_map,Function.comp_def,erase_reading]
  refine run.trans ?_
  change (RingFullPathPairs.sphereRun FullVisit.path (o.next? bit) n [Oracle.root bit q]).map
      (List.filterMap (bitOf ∘ FullVisit.path)) =
    (RingFullPathPairs.sphereRun FullVisit.path (o.next? bit) n [Oracle.root bit q]).map
      (List.filterMap (fun v => bit v.cursor))
  cases h : RingFullPathPairs.sphereRun FullVisit.path (o.next? bit) n [Oracle.root bit q] with
  | none => rfl
  | some out =>
    have walk := RingFullPathPairs.sphereRun_sound (o.next_sound bit) _ _ _ h
    simpa only [Option.map_some,List.filterMap_map,Function.comp_def] using
      congrArg some (Oracle.walk_bits walk).symm

/-- Reconstruct the complete ordinary trial key. Both Rule 4b reference hands
come from the same expansion of its unordered inventory. -/
def key? (i : Input) (r : Reader i) (rev : Bool) (q : Arm i) : Option RingFullPathEligibility.Key := do
  let u ← RingRetainedStereoRefinement.priority i r rev [] q
  let l ← RingRetainedStereoRefinement.priority i r rev [.lowercase] q
  let b ← inventory? i r rev [] q
  let f ← inventory? i r rev [.lowercase] q
  return ⟨u.deep,max (reading .R b) (reading .S b),l.word,reading .R f⟩

/-- Reuse each stage's molecular child and rank readers for its top priority
and its entire sphere inventory. -/
private def keyWithReaders (i : Input) (r : Reader i) (rev : Bool) (q : Arm i) :
    Option RingFullPathEligibility.Key :=
  RingOccurrenceStereo.withRankReaders i r rev [] q fun edges unitRank =>
    RingOccurrenceStereo.withRankReaders i r rev [.lowercase] q fun lowerEdges lowerRank => do
      let u ← unitRank q
      let l ← lowerRank q
      let b ← inventoryWith r rev edges unitRank q
      let f ← inventoryWith r rev lowerEdges lowerRank q
      return ⟨u.deep,max (reading .R b) (reading .S b),l.word,reading .R f⟩

@[csimp] private theorem keyWithReaders_exact : @key? = @keyWithReaders := by
  funext i r rev q
  unfold keyWithReaders
  simp only [RingOccurrenceStereo.withRankReaders_eq]
  rfl

theorem key_exact (i : Input) (r : Reader i) (rev : Bool) (q : Arm i) :
    key? i r rev q = RingFullPathEligibility.key? i r rev q := by
  unfold key? RingFullPathEligibility.key? RingFullPathPairs.pairs? RingFullPathRule5.word?
  simp only [← reading_exact]
  cases RingRetainedStereoRefinement.priority i r rev [] q <;>
    cases RingRetainedStereoRefinement.priority i r rev [.lowercase] q <;>
    cases inventory? i r rev [] q <;> cases inventory? i r rev [.lowercase] q <;> rfl

end TetraStereo.Engine.RingStereoSphereInventory
assert_kernel_only TetraStereo.Engine.RingStereoSphereInventory.reading_exact
assert_kernel_only TetraStereo.Engine.RingStereoSphereInventory.key_exact
