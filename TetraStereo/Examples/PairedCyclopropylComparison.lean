import TetraStereo.Examples.PairedCyclopropylDonorStore
import TetraStereo.Engine.RingEqualPathHandCounts
import TetraStereo.Engine.RingMolecularDonorVerdict
import TetraStereo.Engine.RingPathRankTransport

/-! Five signed visits on each cyclopropyl arm, from three physical chiral frames. -/
set_option autoImplicit false
namespace TetraStereo.Examples.PairedCyclopropylComparison
open OneCenter Engine LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm)
open RingNestedActivePair (Reader)
open RingStereoSphereInventory (SignedPath Edge Inventory project sphere reading inventory?)
open RingRetainedChemicalTrace (Word)
open RingFullPathPairs (bitOf)
open RingEqualPathHandCounts (lastHand visible quiet)
open RingFullPathEligibility (Key)
open RingResidualPairDecision (Verdict)
open private sphere_visible silence bit_project from TetraStereo.Engine.RingEqualPathHandCounts
open private readRow_sorted from TetraStereo.Engine.RingUnorderedSphereReading
attribute [local instance] lexOrd

structure Hands where
  entry : RS
  exitHand : RS
  distal : RS
  deriving DecidableEq, Repr

def Hands.mirror (h : Hands) : Hands := ⟨h.entry.swap,h.exitHand.swap,h.distal.swap⟩

def fromGeometry? (g : Geometry) (side : Bool) : Option Hands := do
  let h ← readback? g (PairedCyclopropylPaths.order side 0)
  let x ← readback? g (PairedCyclopropylPaths.order side 1)
  let d ← readback? g (PairedCyclopropylPaths.order side 2)
  return ⟨h,x,d⟩

def visit (h : Hands) (v : Fin 5) := ![h.entry,h.exitHand,h.distal,h.exitHand.swap,h.distal] v

theorem physical_visits {g : Geometry} {side : Bool} {h : Hands} (got : fromGeometry? g side = some h)
    (v : Fin 5) : readback? g (PairedCyclopropylPaths.order side v) = some (visit h v) := by
  unfold fromGeometry? at got
  obtain ⟨e,he,go⟩ := Option.bind_eq_some_iff.mp got
  obtain ⟨x,hx,go⟩ := Option.bind_eq_some_iff.mp go
  obtain ⟨d,hd,out⟩ := Option.bind_eq_some_iff.mp go
  cases Option.some.inj out
  have other : readback? g (PairedCyclopropylPaths.order side 3) =
      (readback? g (PairedCyclopropylPaths.order side 1)).map RS.swap := by
    cases side <;> exact LocalizedMarkedTerminalGaugeSwap.readback_swap23 _ _ _ _ _
  rw [hx] at other
  fin_cases v <;> first | exact he | exact hx | exact hd | exact other

/-- The three coordinate readings exist and explain the actual publications
at all five histories on either arm of every admitted geometry of this graph. -/
theorem public_visits {i : Input} (graph : i.molecule = PairedCyclopropylPaths.molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (side : Bool) :
    ∃ h, fromGeometry? (RingWrittenPHReadings.geometry i.spatial) side = some h ∧
      ∀ (v : Fin 5) (q : RingActivePairs.Site i),
        DecalinAuxiliary.history q = PairedCyclopropylPaths.route side v →
        RingChemicalGraphProof.state i q = some (some (.chiral (visit h v),.chiral (visit h v).swap)) := by
  have nonflat (v : Fin 5) : ∃ h, readback? (RingWrittenPHReadings.geometry i.spatial) (PairedCyclopropylPaths.order side v) = some h := by
    obtain ⟨q,_,_,path⟩ := PairedCyclopropylPaths.route_exists i graph side v
    obtain ⟨h,read,_⟩ := PairedCyclopropylDonorStore.public_hand graph ok side v path
    exact ⟨h,read⟩
  obtain ⟨e,he⟩ := nonflat 0
  obtain ⟨x,hx⟩ := nonflat 1
  obtain ⟨d,hd⟩ := nonflat 2
  let h : Hands := ⟨e,x,d⟩
  have found : fromGeometry? (RingWrittenPHReadings.geometry i.spatial) side = some h := by
    simp [fromGeometry?,he,hx,hd,h]
  refine ⟨h,found,?_⟩
  intro v q path
  obtain ⟨t,ht,value⟩ := PairedCyclopropylDonorStore.public_hand graph ok side v path
  exact (Option.some.inj (ht.symm.trans (physical_visits found v))) ▸ value

/-- Group by distance from the molecular root. The direct distal visit
and the detour exit share the third sphere. -/
def spheres (h : Hands) (s : RS) : List (List Bool) :=
  [[h.entry == s],[h.exitHand == s],[h.distal == s,h.exitHand.swap == s],[h.distal == s]]

def word (h : Hands) (s : RS) := (spheres h s).flatten

/-- The exit comparison is senior to the distal comparison. -/
def pattern (h : Hands) := [h.exitHand == h.entry,h.distal == h.entry]

def verdict (a b : Hands) : Verdict :=
  match compare (pattern a) (pattern b) with
  | .gt => .left .rule4b
  | .lt => .right .rule4b
  | .eq => if a.entry = b.entry then .tie else if a.entry = .R then .left .rule5 else .right .rule5

theorem best (h : Hands) : max (word h .R) (word h .S) = word h h.entry := by
  obtain ⟨(_|_),(_|_),(_|_)⟩ := h <;> decide

theorem stages (a b : Hands) :
    (verdict a b = .tie ↔ a = b) ∧
    (verdict a b = .left .rule4b ↔ pattern b < pattern a) ∧
    (verdict a b = .right .rule4b ↔ pattern a < pattern b) ∧
    (verdict a b = .left .rule5 ↔ b = a.mirror ∧ a.entry = .R) ∧
    (verdict a b = .right .rule5 ↔ b = a.mirror ∧ a.entry = .S) := by
  obtain ⟨(_|_),(_|_),(_|_)⟩ := a <;> obtain ⟨(_|_),(_|_),(_|_)⟩ := b <;> decide

/-- One-based molecular distances of the first disputed sphere. After a
best-word tie, complementary triples differ in the fixed-R entry itself. -/
def decidingSphere (a b : Hands) : Option Nat :=
  if (a.exitHand == a.entry) != (b.exitHand == b.entry) then some 2
  else if (a.distal == a.entry) != (b.distal == b.entry) then some 3
  else if a.entry != b.entry then some 1 else none

theorem first_sphere (a b : Hands) :
    let rule5 := pattern a = pattern b
    let as := spheres a (if rule5 then .R else a.entry)
    let bs := spheres b (if rule5 then .R else b.entry)
    match decidingSphere a b with
    | none => as = bs ∧ verdict a b = .tie
    | some n => as.take (n-1) = bs.take (n-1) ∧ as[n-1]? ≠ bs[n-1]? ∧
        compare (as[n-1]?.getD []) (bs[n-1]?.getD []) = (verdict a b).order := by
  obtain ⟨(_|_),(_|_),(_|_)⟩ := a <;> obtain ⟨(_|_),(_|_),(_|_)⟩ := b <;>
    dsimp [decidingSphere,pattern] <;> decide

def profiles : List Hands := do
  let e ← [.R,.S]
  let x ← [.R,.S]
  let d ← [.R,.S]
  return ⟨e,x,d⟩

theorem family_counts :
    let vs := profiles.flatMap fun a => profiles.map (verdict a)
    vs.count (.left .rule4b) = 24 ∧ vs.count (.right .rule4b) = 24 ∧
      vs.count (.left .rule5) = 4 ∧ vs.count (.right .rule5) = 4 ∧ vs.count .tie = 8 := by decide +kernel

/-- Forget neutral endpoints, retaining all signed parent edges of every
visible visit. The single nontrivial within-sphere precedence follows from
the strictly larger earlier priority of the exit carbon than the CH₂ carbon. -/
structure Census (h : Hands) (inv : Inventory) where
  path : Fin 5 → SignedPath
  entry : Multiset SignedPath
  exitRow : Multiset SignedPath
  shared : Multiset SignedPath
  last : Multiset SignedPath
  following : Inventory
  layers : inv = entry :: exitRow :: shared :: last :: following
  silent : quiet following
  entryVisits : visible entry = ↑[path 0]
  exitVisits : visible exitRow = ↑[path 1]
  sharedVisits : visible shared = ↑[path 2,path 3]
  lastVisits : visible last = ↑[path 4]
  hands : ∀ v, lastHand (path v) = some (visit h v)
  sameParent : ∃ e direct detour tailA tailB,
    path 2 = e :: direct :: tailA ∧ path 3 = e :: detour :: tailB ∧
    detour.earlier.length = direct.earlier.length ∧ detour.earlier < direct.earlier

private theorem shared_order {h inv} (c : Census h inv) (s : RS) :
    project s (c.path 3) < project s (c.path 2) := by
  obtain ⟨e,a,b,l,r,ha,hb,w,senior⟩ := c.sameParent
  rw [ha,hb]
  exact List.Lex.cons (List.Lex.rel ((RingPathRankTransport.stepKey_lt w _ _).mpr (Or.inl senior)))

theorem census_word {h inv} (c : Census h inv) (s : RS) : reading s inv = word h s := by
  have emit (k : Fin 5) : bitOf (project s (c.path k)) = some (visit h k == s) := by
    rw [bit_project,c.hands]; rfl
  have read (vs : List (Fin 5)) (sorted : ((vs.map c.path).map (project s)).Pairwise (· ≥ ·)) :
      sphere s (↑(vs.map c.path)) = vs.map (fun k => visit h k == s) := by
    change RingUnorderedSphereReading.readRow (project s) bitOf (vs.map c.path) = _
    rw [readRow_sorted _ _ _ sorted,List.filterMap_map]
    simp [Function.comp_def,emit]
  have singleton (v : Fin 5) : sphere s (↑[c.path v]) = [visit h v == s] := read [v] (by simp)
  have pair : sphere s (↑[c.path 2,c.path 3]) = [visit h 2 == s,visit h 3 == s] :=
    read [2,3] (by simpa using (shared_order c s).le)
  have cells {r : Multiset SignedPath} : sphere s r = sphere s (visible r) := (sphere_visible s r).symm
  rw [c.layers]
  change sphere s c.entry ++ (sphere s c.exitRow ++ (sphere s c.shared ++
    (sphere s c.last ++ reading s c.following))) = _
  rw [cells (r := c.entry),cells (r := c.exitRow),cells (r := c.shared),cells (r := c.last),
    c.entryVisits,c.exitVisits,c.sharedVisits,c.lastVisits,singleton,singleton,pair,singleton,silence c.silent]
  rfl

/-- Molecular premise for the graph-to-word bridge. Only two unseeded
inventories are needed; both Rule 4b references use the same census. -/
def Complete {i : Input} (r : Reader i) (rev : Bool) (q : Arm i) (h : Hands) : Prop :=
  ∀ os, os = [] ∨ os = [.lowercase] → ∃ inv, inventory? i r rev os q = some inv ∧ Nonempty (Census h inv)

theorem stage_words {i r rev q h} (ok : @Complete i r rev q h) (os)
    (stage : os = [] ∨ os = [.lowercase]) (seed : RS) :
    RingFullPathPairs.stageWords i r rev os seed q = some (word h seed) := by
  obtain ⟨inv,found,⟨c⟩⟩ := ok os stage
  rw [←RingStereoSphereInventory.reading_exact,found,Option.map_some,census_word c]

theorem fields {i r rev q h k} (ok : @Complete i r rev q h) (got : RingFullPathEligibility.key? i r rev q = some k) :
    k.bestFourB = word h h.entry ∧ k.fixedR = word h .R := by
  unfold RingFullPathEligibility.key? at got
  simp only [RingFullPathPairs.pairs?,RingFullPathRule5.word?,stage_words ok [] (.inl rfl),
    stage_words ok [.lowercase] (.inr rfl)] at got
  cases u : RingRetainedStereoRefinement.priority i r rev [] q <;>
    cases l : RingRetainedStereoRefinement.priority i r rev [.lowercase] q <;> simp [u,l] at got
  subst k
  exact ⟨best h,rfl⟩

theorem native_verdict {i r rev u v a b x y}
    (l : @Complete i r rev u a) (rhs : @Complete i r rev v b)
    (hx : RingFullPathEligibility.key? i r rev u = some x) (hy : RingFullPathEligibility.key? i r rev v = some y)
    (lower : x.fourC = y.fourC) :
    RingMolecularDonorVerdict.residual x y = verdict a b := by
  obtain ⟨x4,x5⟩ := fields l hx
  obtain ⟨y4,y5⟩ := fields rhs hy
  unfold RingMolecularDonorVerdict.residual
  rw [x4,y4,x5,y5,lower]
  simp only [Std.ReflCmp.compare_self]
  obtain ⟨(_|_),(_|_),(_|_)⟩ := a <;> obtain ⟨(_|_),(_|_),(_|_)⟩ := b <;> decide

theorem native_order {i r rev u v a b x y}
    (l : @Complete i r rev u a) (rhs : @Complete i r rev v b)
    (hx : RingFullPathEligibility.key? i r rev u = some x) (hy : RingFullPathEligibility.key? i r rev v = some y)
    (prior : x.throughFourA = y.throughFourA) (lower : x.fourC = y.fourC) :
    compare (RingFullPathTrialReadings.trialKey x []) (RingFullPathTrialReadings.trialKey y []) = (verdict a b).order :=
  (RingMolecularDonorVerdict.residual_order prior).trans (congrArg Verdict.order (native_verdict l rhs hx hy lower))

end TetraStereo.Examples.PairedCyclopropylComparison
assert_kernel_only TetraStereo.Examples.PairedCyclopropylComparison.physical_visits
assert_kernel_only TetraStereo.Examples.PairedCyclopropylComparison.stages
assert_kernel_only TetraStereo.Examples.PairedCyclopropylComparison.census_word
assert_kernel_only TetraStereo.Examples.PairedCyclopropylComparison.native_verdict
assert_kernel_only TetraStereo.Examples.PairedCyclopropylComparison.native_order
assert_kernel_only TetraStereo.Examples.PairedCyclopropylComparison.public_visits
assert_kernel_only TetraStereo.Examples.PairedCyclopropylComparison.first_sphere
assert_kernel_only TetraStereo.Examples.PairedCyclopropylComparison.family_counts
