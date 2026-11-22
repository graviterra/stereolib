import TetraStereo.Engine.RingAuxiliaryInventory

set_option autoImplicit false

namespace TetraStereo.Engine
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation RingChemicalPriority Recursive

/-- A checked outward arm containing its full candidate inventory. A
nonstereogenic candidate remains in the inventory, while its positively
classified descendants can furnish Rule 4b references and later pairs. -/
structure SignedRankedRingArm (m : RawMolecule) (g : Geometry) (path : List Nat) (reverse : Bool) where
  domain : saturatedWithHalogens m = true
  hasParent : 2 ≤ path.length
  inventory : RingAuxiliaryInventory.ArmInventory m g path
  unique : (inventory.entries.map Prod.fst).Nodup
  population : ReferencePopulation m inventory.node (InventoryPriority.positives inventory.entries) reverse
  selected : referencePopulation? m inventory.node (InventoryPriority.positives inventory.entries) reverse =
    some population
  bounds : PairSpheres.Interval
  ranked : rankedArm? m inventory.node (InventoryPriority.positives inventory.entries) reverse =
    some (population.references,bounds)

/-- Rank the same certified inventory on either geometry without recomputing
its molecular assignments or its negative certificates. -/
private def rankInventory? {m : RawMolecule} {g : Geometry} {path : List Nat}
    (inventory : RingAuxiliaryInventory.ArmInventory m g path) (reverse : Bool) :
    Option {r : SignedRankedRingArm m g path reverse // r.inventory = inventory} := do
  if domain : saturatedWithHalogens m = true then
    if parent : 2 ≤ path.length then
      let fs := InventoryPriority.positives inventory.entries
      let ⟨population,selected⟩ ← (referencePopulation? m inventory.node fs reverse).attach
      let ⟨bounds,range⟩ ← population.range?.attach
      return ⟨⟨domain,parent,inventory,inventory.unique,population,selected,bounds,by
        change rankedArm? m inventory.node fs reverse = _
        simp [rankedArm?,selected,range]⟩,rfl⟩
  none

def rankRingArmInventory? {m : RawMolecule} {g : Geometry} {path : List Nat}
    (inventory : RingAuxiliaryInventory.ArmInventory m g path) (reverse : Bool) :
    Option (SignedRankedRingArm m g path reverse) :=
  (rankInventory? inventory reverse).map Subtype.val

/-- Obtain a signed occurrence inventory from the molecule, then rank its
chiral sites. Any unresolved candidate leaves the arm unranked. -/
def rankSignedRingArm? (m : RawMolecule) (g : Geometry) (path : List Nat) (reverse : Bool)
    (fuel : Nat) (hint : List Nat → Option Recursive.Frame) (radius : List Nat → Nat) :
    Option (SignedRankedRingArm m g path reverse) := do
  let inventory ← RingAuxiliaryInventory.arm? m g path fuel hint radius
  rankRingArmInventory? inventory reverse

namespace SignedRankedRingArm

def facts {m g p rev} (a : SignedRankedRingArm m g p rev) := InventoryPriority.positives a.inventory.entries

/-- The positive projection is exact at every occurrence, including all
occurrences farther along paths through a certified negative candidate. -/
theorem mem_facts {m g p rev} (a : SignedRankedRingArm m g p rev) {q r} :
    (q,r) ∈ a.facts ↔ (q,some r) ∈ a.inventory.entries := by
  constructor
  · intro h
    obtain ⟨⟨path,v⟩,member,eqn⟩ := List.mem_filterMap.mp h
    cases v with
    | none => contradiction
    | some value => cases eqn; exact member
  · intro h
    exact List.mem_filterMap.mpr ⟨(q,some r),h,rfl⟩

/-- Certifying absence at an address excludes every positive reading there. -/
theorem absent_not_in_facts {m g p rev} (a : SignedRankedRingArm m g p rev) {q}
    (absent : (q,none) ∈ a.inventory.entries) (r : Reading) : (q,r) ∉ a.facts := by
  intro h
  have same := List.inj_on_of_nodup_map a.unique absent (a.mem_facts.mp h) rfl
  cases same

theorem justified {m g p rev} (a : SignedRankedRingArm m g p rev) {q r}
    (member : (q,r) ∈ a.facts) : Promotion.Justified m g q r :=
  a.inventory.positive q r (a.mem_facts.mp member)

/-- A retained negative has its own molecular derivation; every positive
observation used in that derivation also appears in this ranking. -/
theorem negative_dependencies {m g p rev} (a : SignedRankedRingArm m g p rev) {q}
    (member : (q,none) ∈ a.inventory.entries) :
    ∃ es, Promotion.Negative m q es ∧ es ⊆ a.inventory.entries ∧
      ∀ t r, (t,some r) ∈ es → (t,r) ∈ a.facts := by
  obtain ⟨es,negative,inside⟩ := a.inventory.negatives q member
  exact ⟨es,negative,inside,fun _ _ h => a.mem_facts.mpr (inside h)⟩

/-- The selected one- or two-reference population has at least one complete
reading and the interval contains every admitted molecular ordering. -/
theorem readings {m g p rev} (a : SignedRankedRingArm m g p rev) :
    (∃ w, BestWord m a.inventory.node a.facts rev a.population.references w) ∧
    ∀ w, BestWord m a.inventory.node a.facts rev a.population.references w → a.bounds.Allows w :=
  rankedArm_sound a.ranked

/-- Compare the two arms' Rule 4b words. Applying this comparison as a
priority judgment additionally requires a complete tie through Rule 4a. -/
theorem comparison {m g p q rev o} (l : SignedRankedRingArm m g p rev)
    (r : SignedRankedRingArm m g q rev)
    (decision : rankedDecision? l.population.references r.population.references l.bounds r.bounds = some o) :
    (∃ x y, BestWord m l.inventory.node l.facts rev l.population.references x ∧
      BestWord m r.inventory.node r.facts rev r.population.references y) ∧
    ∀ x y, BestWord m l.inventory.node l.facts rev l.population.references x →
      BestWord m r.inventory.node r.facts rev r.population.references y →
      RankResult l.population.references r.population.references x y o :=
  rankedDecision_sound l.ranked r.ranked decision

end SignedRankedRingArm

/-- The complete pre-4b molecular observation at this cursor. The class
lookup uses the certified arm inventories and checks every unlisted carbon
with the same noncandidate test as the Rule 4a evaluator. -/
def signedPriorObservation? (m : RawMolecule) (p : List Nat) (es : InventoryPriority.Entries)
    (c : CanonicalRerootCursor) : Option (IsotopePriority.FullObservation × Nat) := do
  return (← IsotopePriority.fullObservation? m p c, ← UnitClasses.classAt? m es ⟨c,[c.node],[],true⟩)

/-- The two exact outward cursors belong to the same incident frame. A
single tree correspondence preserves all prior observations together at
every paired occurrence, including its duplicate origin, isotope and class. -/
structure SignedRule4bFrame (m : RawMolecule) (g : Geometry) (p : List Nat)
    (f : Recursive.Frame) (depth : Nat) where
  stage : f.stage = .fourB
  frame : frameOK m p depth f = true
  prior : IsotopePriority.IncidentComparison m p f.left f.right
  checked : IsotopePriority.compareIncident? m p f.left f.right = some prior
  tied : prior.ordering = .eq
  left : RingAuxiliaryInventory.ArmInventory m g (p ++ [f.left])
  right : RingAuxiliaryInventory.ArmInventory m g (p ++ [f.right])
  leftCursor : prior.pair.left.cursor = ⟨left.node,some prior.pair.focus⟩
  rightCursor : prior.pair.right.cursor = ⟨right.node,some prior.pair.focus⟩
  distinct : ((left.entries ++ right.entries).map Prod.fst).Nodup
  throughClasses : IsotopePriority.TreesMatch m (signedPriorObservation? m p (left.entries ++ right.entries))
    (IsotopePriority.budget m+1) prior.pair.left.cursor prior.pair.right.cursor

def prepareSignedRule4bFrame? (m : RawMolecule) (g : Geometry) (p : List Nat)
    (f : Recursive.Frame) (depth fuel : Nat) (hint : List Nat → Option Recursive.Frame)
    (radius : List Nat → Nat) : Option (SignedRule4bFrame m g p f depth) := do
  if stage : f.stage = .fourB then
    if frame : frameOK m p depth f = true then
      let ⟨prior,checked⟩ ← (IsotopePriority.compareIncident? m p f.left f.right).attach
      if tied : prior.ordering = .eq then
        let l ← RingAuxiliaryInventory.arm? m g (p ++ [f.left]) fuel hint radius
        let r ← RingAuxiliaryInventory.arm? m g (p ++ [f.right]) fuel hint radius
        if left : prior.pair.left.cursor = ⟨l.node,some prior.pair.focus⟩ then
          if right : prior.pair.right.cursor = ⟨r.node,some prior.pair.focus⟩ then
            let es := l.entries ++ r.entries
            if unique : (es.map Prod.fst).Nodup then
              if matched : IsotopePriority.treesMatch m (signedPriorObservation? m p es)
                  (IsotopePriority.budget m+1) prior.pair.left.cursor prior.pair.right.cursor = true then
                return ⟨stage,frame,prior,checked,tied,l,r,left,right,unique,IsotopePriority.treesMatch_sound matched⟩
  none

namespace SignedRule4bFrame

theorem earlier_observer {m g p f depth} (frame : SignedRule4bFrame m g p f depth) {α : Type}
    (reader : Nat → CanonicalRerootCursor → α)
    (combine : (IsotopePriority.FullObservation × Nat) → List α → α)
    (atNode : ∀ n c o, signedPriorObservation? m p (frame.left.entries ++ frame.right.entries) c = some o →
      reader (n+1) c = combine o ((c.children m).map (reader n)))
    (symmetric : ∀ o {xs ys : List α}, xs.Perm ys → combine o xs = combine o ys) :
    reader (IsotopePriority.budget m+1) frame.prior.pair.left.cursor =
      reader (IsotopePriority.budget m+1) frame.prior.pair.right.cursor :=
  frame.throughClasses.observer_eq reader combine atNode symmetric

structure Comparison {m g p f depth} (frame : SignedRule4bFrame m g p f depth) (reverse : Bool) where
  left : SignedRankedRingArm m g (p ++ [f.left]) reverse
  right : SignedRankedRingArm m g (p ++ [f.right]) reverse
  leftInventory : left.inventory = frame.left
  rightInventory : right.inventory = frame.right
  sameSpheres : (sphereSites left.facts reverse).map List.length = (sphereSites right.facts reverse).map List.length
  result : Ordering
  decision : rankedDecision? left.population.references right.population.references left.bounds right.bounds = some result

def compare? {m g p f depth} (frame : SignedRule4bFrame m g p f depth) (reverse : Bool) :
    Option (Comparison frame reverse) := do
  let ⟨l,left⟩ ← rankInventory? frame.left reverse
  let ⟨r,right⟩ ← rankInventory? frame.right reverse
  if shape : (sphereSites l.facts reverse).map List.length = (sphereSites r.facts reverse).map List.length then
    let ⟨o,decision⟩ ← (rankedDecision? l.population.references r.population.references l.bounds r.bounds).attach
    return ⟨l,r,left,right,shape,o,decision⟩
  none

/-- The result, including an exact tie, holds for every complete word.
Each ligand admits at least one such word. -/
theorem Comparison.all_readings {m g p f d rev} {frame : SignedRule4bFrame m g p f d}
    (c : Comparison frame rev) :
    (∃ x y, BestWord m c.left.inventory.node c.left.facts rev c.left.population.references x ∧
      BestWord m c.right.inventory.node c.right.facts rev c.right.population.references y) ∧
    ∀ x y, BestWord m c.left.inventory.node c.left.facts rev c.left.population.references x →
      BestWord m c.right.inventory.node c.right.facts rev c.right.population.references y →
      RankResult c.left.population.references c.right.population.references x y c.result :=
  c.left.comparison c.right c.decision

theorem Comparison.tied_words {m g p f d rev} {frame : SignedRule4bFrame m g p f d}
    (c : Comparison frame rev) (tied : c.result = .eq) {x y}
    (left : BestWord m c.left.inventory.node c.left.facts rev c.left.population.references x)
    (right : BestWord m c.right.inventory.node c.right.facts rev c.right.population.references y) :
    c.left.population.references.length = c.right.population.references.length ∧ x = y := by
  have result := c.all_readings.2 x y left right
  rw [tied] at result
  exact result

end SignedRule4bFrame

def compareSignedRingRule4b? (m : RawMolecule) (g : Geometry) (p : List Nat)
    (f : Recursive.Frame) (depth : Nat) (reverse : Bool) (fuel : Nat)
    (hint : List Nat → Option Recursive.Frame) (radius : List Nat → Nat) :
    Option ((frame : SignedRule4bFrame m g p f depth) × frame.Comparison reverse) := do
  let frame ← prepareSignedRule4bFrame? m g p f depth fuel hint radius
  return ⟨frame,← frame.compare? reverse⟩

/-- Both geometry readings share exactly the same molecular inventory and
earlier-rule proof. Each may choose its own natural reference population. -/
structure SignedRule4bBoth (m : RawMolecule) (g : Geometry) (p : List Nat) (f : Recursive.Frame)
    (depth : Nat) where
  frame : SignedRule4bFrame m g p f depth
  actual : frame.Comparison false
  reflected : frame.Comparison true
  sameResult : actual.result = reflected.result

/-- A strict Rule 4b outcome supplies the same priority order on both
geometries. Its actual directed volume gives the uppercase letter. -/
def SignedRule4bBoth.reading? {m g p f depth} (c : SignedRule4bBoth m g p f depth) :
    Option {r : Reading // c.actual.result ≠ .eq ∧
      geometric g (f.order (c.actual.result == .gt)) (f.order (c.reflected.result == .gt)) = some r ∧
      r.reflected = r.actual.swap ∧ r.label = some (.chiral r.actual)} := do
  if strict : c.actual.result ≠ .eq then
    let order := f.order (c.actual.result == .gt)
    let ⟨r,computed⟩ ← (geometric g order order).attach
    return ⟨r,strict,by rw [← c.sameResult]; exact computed,(constitutional_casing computed).2⟩
  none

theorem SignedRule4bBoth.tied {m g p f d} (c : SignedRule4bBoth m g p f d)
    (tie : c.actual.result = .eq) : c.reflected.result = .eq ∧ c.reading? = none := by
  exact ⟨c.sameResult.symm.trans tie,by simp [SignedRule4bBoth.reading?,tie]⟩

theorem SignedRule4bBoth.strict_casing {m g p f d} (c : SignedRule4bBoth m g p f d)
    (_strict : c.actual.result ≠ .eq) {r : Reading}
    (read : geometric g (f.order (c.actual.result == .gt)) (f.order (c.reflected.result == .gt)) = some r) :
    readback? g (f.order (c.actual.result == .gt)) = some r.actual ∧
    r.reflected = r.actual.swap ∧ r.label = some (.chiral r.actual) := by
  rw [← c.sameResult] at read
  exact constitutional_casing read

def compareSignedRingRule4bBoth? (m : RawMolecule) (g : Geometry) (p : List Nat)
    (f : Recursive.Frame) (depth fuel : Nat)
    (hint : List Nat → Option Recursive.Frame) (radius : List Nat → Nat) :
    Option (SignedRule4bBoth m g p f depth) := do
  let frame ← prepareSignedRule4bFrame? m g p f depth fuel hint radius
  let actual ← frame.compare? false
  let reflected ← frame.compare? true
  if agree : actual.result = reflected.result then return ⟨frame,actual,reflected,agree⟩
  none

end TetraStereo.Engine

assert_kernel_only TetraStereo.Engine.rankSignedRingArm?
assert_kernel_only TetraStereo.Engine.SignedRankedRingArm.mem_facts
assert_kernel_only TetraStereo.Engine.SignedRankedRingArm.absent_not_in_facts
assert_kernel_only TetraStereo.Engine.SignedRankedRingArm.justified
assert_kernel_only TetraStereo.Engine.SignedRankedRingArm.negative_dependencies
assert_kernel_only TetraStereo.Engine.SignedRankedRingArm.readings
assert_kernel_only TetraStereo.Engine.SignedRankedRingArm.comparison
assert_kernel_only TetraStereo.Engine.SignedRule4bFrame.earlier_observer
assert_kernel_only TetraStereo.Engine.SignedRule4bFrame.Comparison.all_readings
assert_kernel_only TetraStereo.Engine.SignedRule4bFrame.Comparison.tied_words
assert_kernel_only TetraStereo.Engine.SignedRule4bBoth.tied
assert_kernel_only TetraStereo.Engine.SignedRule4bBoth.strict_casing
assert_kernel_only TetraStereo.Engine.SignedRule4bBoth.reading?
assert_kernel_only TetraStereo.Engine.compareSignedRingRule4bBoth?
