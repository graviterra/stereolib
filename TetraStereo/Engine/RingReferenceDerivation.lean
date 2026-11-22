import TetraStereo.Engine.RingReferenceCasing
import TetraStereo.Engine.RingOccurrenceTable

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority.ReferenceDerivation
open OneCenter LocalizedGenericMarkedRecalculation Recursive
open InventoryPriority (Entries)

/-- A finite molecular derivation at the specified occurrence. Every
recursive premise at every depth reads the same signed publication at
that address. A promotion reconstructs every trial by its actual
constitutional, stereochemical or marked occurrence comparisons. -/
inductive Derives (m : RawMolecule) (g : Geometry) (published : Entries) :
    List Nat → Option Reading → Prop where
  | isotopic {p r} (ranking : IsotopePriority.Ranking m p)
      (hand : geometric g ranking.order ranking.order = some r) : Derives m g published p (some r)
  | atomic {p depth order r}
      (ranked : atomicOrder? m p depth = some order)
      (hand : geometric g order order = some r) : Derives m g published p (some r)
  | distinguished {p ls rs r} (s : DiscoveredPriority.Step m p ls rs)
      (bound : ls ++ rs ⊆ published) (subs : ∀ x ∈ ls ++ rs, Derives m g published x.1 x.2)
      (hand : geometric g s.actual.ligands s.reflected.ligands = some r) : Derives m g published p (some r)
  | indistinguishable {p} (s : SignedPair.Pair m p)
      (bound : s.required ⊆ published) (subs : ∀ x ∈ s.required, Derives m g published x.1 x.2) :
      Derives m g published p none
  | ordinary {p v} (f : ReferenceFrame.MolecularFrame m g p) (s : ReferenceFrame.Ordinary f)
      (bound : f.inputs ⊆ published) (subs : ∀ x ∈ f.inputs, Derives m g published x.1 x.2)
      (observed : s.outcome.reading? = v) : Derives m g published p v
  | promotion {p v} (s : ReferenceFrame.Population m g p)
      (bound : s.inputs ⊆ published) (subs : ∀ x ∈ s.inputs, Derives m g published x.1 x.2)
      (consensus : s.consensus? = some v) : Derives m g published p v

theorem Derives.weaken {m g es p v} (d : Derives m g es p v) {later : Entries} (sub : es ⊆ later) :
    Derives m g later p v := by
  induction d with
  | atomic ranked hand => exact .atomic ranked hand
  | isotopic ranking hand => exact .isotopic ranking hand
  | distinguished s bound _ hand ih => exact .distinguished s (fun _ h => sub (bound h)) ih hand
  | indistinguishable s bound _ ih => exact .indistinguishable s (fun _ h => sub (bound h)) ih
  | ordinary f s bound _ observed ih => exact .ordinary f s (fun _ h => sub (bound h)) ih observed
  | promotion s bound _ consensus ih => exact .promotion s (fun _ h => sub (bound h)) ih consensus

/-- Molecular witnesses for the actual priority order and the number of
reversing pairs. Signed inputs used to select the witness are derived in
the given occurrence table. -/
inductive LetterBasis (m : RawMolecule) (g : Geometry) (published : Entries) (p : List Nat) :
    List Nat → Nat → Prop where
  | atomic {depth order} (ranked : atomicOrder? m p depth = some order) : LetterBasis m g published p order 0
  | isotopic (ranking : IsotopePriority.Ranking m p) : LetterBasis m g published p ranking.order 0
  | single {ls rs} (s : DiscoveredPriority.Step m p ls rs)
      (bound : ls ++ rs ⊆ published) (subs : ∀ x ∈ ls ++ rs, Derives m g published x.1 x.2) :
      LetterBasis m g published p s.actual.ligands s.basis.five.toNat
  | ordinary (f : ReferenceFrame.MolecularFrame m g p)
      (bound : f.inputs ⊆ published) (subs : ∀ x ∈ f.inputs, Derives m g published x.1 x.2)
      {a b} (actual : ReferenceFrame.orders f.ids (ReferenceFrame.entries f.rows) false = [a])
      (reflected : ReferenceFrame.orders f.ids (ReferenceFrame.entries f.rows) true = [b]) :
      LetterBasis m g published p a f.reversals
  | promoted (s : ReferenceFrame.Population m g p) (t : ReferenceFrame.Trial s.frame)
      (bound : s.inputs ⊆ published) (subs : ∀ x ∈ s.inputs, Derives m g published x.1 x.2)
      (used : t ∈ s.trials) {a b} (actual : ReferenceFrame.orders s.frame.ids t.table false = [a])
      (reflected : ReferenceFrame.orders s.frame.ids t.table true = [b]) :
      LetterBasis m g published p a s.frame.reversals

/-- Four distinct ligands have six unordered pairs. Ordinary multi-pair
rankings can reverse two pairs; promotion frames obey the stronger
zero/three/four classification. -/
theorem LetterBasis.reversal_count {m g es p a n} (b : LetterBasis m g es p a n) : n ≤ 6 := by
  cases b with
  | atomic | isotopic => decide
  | single s => cases s.basis.five <;> decide
  | ordinary f => exact f.reversals_le_six
  | promoted s => exact s.frame.toMolecularFrame.reversals_le_six

/-- A positive auxiliary at any recursion depth has a molecular order
that gives its absolute letter. An odd number of reversing pairs gives
lowercase; an even number gives uppercase. -/
theorem Derives.chemical_letter {m g es p r} (d : Derives m g es p (some r)) :
    ∃ a n, LetterBasis m g es p a n ∧ readback? g a = some r.actual ∧
      r.label = some (if n % 2 = 0 then .chiral r.actual else .pseudoasymmetric (pseudoRSOfRS r.actual)) := by
  cases d with
  | atomic ranked hand =>
    have h := constitutional_casing hand
    exact ⟨_,0,.atomic ranked,h.1,h.2.2⟩
  | isotopic ranking hand =>
    have h := constitutional_casing hand
    exact ⟨_,0,.isotopic ranking,h.1,h.2.2⟩
  | distinguished s bound subs hand =>
    obtain ⟨order,label⟩ := s.chemical_letter hand
    exact ⟨_,_,.single s bound subs,order,by cases h : s.basis.five <;> simpa [h] using label⟩
  | ordinary f s bound subs observed =>
    cases eqn : s.outcome with
    | tied => simp [eqn,ReferenceFrame.Outcome.reading?] at observed
    | assigned a b ha hb v hv =>
      obtain rfl : v = r := by simpa [eqn,ReferenceFrame.Outcome.reading?] using observed
      exact ⟨_,_,.ordinary f bound subs ha hb,f.chemical_letter ha hb hv⟩
  | promotion s bound subs agree =>
    have nonempty : ReferenceFrame.marks s.frame.ids (ReferenceFrame.entries s.frame.rows) ≠ [] := by
      intro h
      have pop := s.frame.eligible
      simp [h] at pop
    obtain ⟨k,hk⟩ := List.exists_mem_of_ne_nil _ nonempty
    obtain ⟨t,a,b,member,_,ha,hb,raw,label⟩ := s.chemical_letter agree k hk
    exact ⟨a,_,.promoted s t bound subs member ha hb,raw,label⟩

structure Certificate (m : RawMolecule) (g : Geometry) (p : List Nat) where
  verdict : Option Reading
  published : Entries
  consistent : (published.map Prod.fst).Nodup
  below : ∀ x ∈ published, p <+: x.1 ∧ p.length < x.1.length
  issued : ∀ x ∈ published, Derives m g published x.1 x.2
  derived : Derives m g published p verdict

/-- A published lookup returns a strict descendant and a derivation for
that very signed value against the same table as the parent. -/
theorem Certificate.lookup_derived {m g p} (c : Certificate m g p) {q v}
    (found : c.published.lookup q = some v) :
    p <+: q ∧ p.length < q.length ∧ Derives m g c.published q v := by
  obtain ⟨l,r,h,_⟩ := List.lookup_eq_some_iff.mp found
  have member : (q,v) ∈ c.published := by rw [h]; simp
  exact ⟨(c.below _ member).1,(c.below _ member).2,c.issued _ member⟩

private structure Located (m : RawMolecule) (g : Geometry) where
  path : List Nat
  result : Certificate m g path

private def Located.entry {m g} (row : Located m g) := (row.path,row.result.verdict)

private def finish {m g p} (v : Option Reading) (needed : Entries) (rows : List (Located m g))
    (rule : ∀ env : Entries, (∀ x ∈ needed, x ∈ env ∧ Derives m g env x.1 x.2) → Derives m g env p v) :
    Option (Certificate m g p) := do
  let used := rows.filter (fun row => needed.contains row.entry)
  let env := (used.flatMap (fun row => row.entry :: row.result.published)).dedup
  if unique : (env.map Prod.fst).Nodup then
    if covered : needed.all (fun x => used.any (fun row => row.entry == x)) = true then
      if below : ∀ x ∈ env, p <+: x.1 ∧ p.length < x.1.length then
        have includes (row : Located m g) (member : row ∈ used) (y) (h : y ∈ row.entry :: row.result.published) :
            y ∈ env := List.mem_dedup.mpr (List.mem_flatMap.mpr ⟨row,member,h⟩)
        have issued : ∀ x ∈ env, Derives m g env x.1 x.2 := by
          intro x hx
          obtain ⟨row,member,inside⟩ := List.mem_flatMap.mp (List.mem_dedup.mp hx)
          have sub : row.result.published ⊆ env := fun _ h => includes row member _ (List.mem_cons_of_mem _ h)
          rcases List.mem_cons.mp inside with rfl | deeper
          · exact row.result.derived.weaken sub
          · exact (row.result.issued x deeper).weaken sub
        return ⟨v,env,unique,below,issued,rule env (by
          intro x hx
          obtain ⟨row,member,same⟩ := List.any_eq_true.mp (List.all_eq_true.mp covered x hx)
          obtain rfl := eq_of_beq same
          have inside := includes row member _ List.mem_cons_self
          exact ⟨inside,issued _ inside⟩)⟩
  none

private def project (es : Entries) (paths : List (List Nat)) : Option Entries :=
  paths.mapM fun q => do return (q,← es.lookup q)

/-- Bind every carbon site on an arm to its signed entry at the exact occurrence. -/
def armFrom {m : RawMolecule} (es : Entries) (p : List Nat) : Option (ReferenceDistance.Arm m p) := do
  let ⟨node,reached⟩ ← (occurrence? m p).attach
  let ⟨paths,sites⟩ ← (carbonSites m (m.atomCount+1) node).attach
  let facts ← project es paths
  if cover : facts.map Prod.fst = paths then
    if unique : (facts.map Prod.fst).Nodup then
      return ⟨node,reached,facts,cover ▸ sites,unique⟩
  none

/-- Inspect the twelve ordinary incident comparisons against this
occurrence's own signed publications. A frame may require further promotion. -/
structure PublishedFrame {m g p} (c : Certificate m g p) extends ReferenceFrame.MolecularFrame m g p where
  bound : ∀ x ∈ toMolecularFrame.inputs, c.published.lookup x.1 = some x.2

def Certificate.frame? {m g p} (c : Certificate m g p) (depth : Nat) : Option (PublishedFrame c) := do
  let f ← ReferenceFrame.molecularFrame? m g p depth (armFrom c.published)
  if bound : ∀ x ∈ f.inputs, c.published.lookup x.1 = some x.2 then return ⟨f,bound⟩
  none

theorem PublishedFrame.input_derived {m g p} {c : Certificate m g p} (f : PublishedFrame c) {x}
    (used : x ∈ f.toMolecularFrame.inputs) : Derives m g c.published x.1 x.2 :=
  (c.lookup_derived (f.bound x used)).2.2

/-- A marked comparison whose two signed arm inventories are read from
one recursively justified certificate for the focus. -/
structure PublishedComparison {m g p} (c : Certificate m g p) (i j mark : Nat)
    extends ReferenceDistance.Comparison m p i j mark where
  bound : ∀ x ∈ left.entries ++ right.entries, c.published.lookup x.1 = some x.2

def Certificate.compare? {m g p} (c : Certificate m g p) (i j mark : Nat) :
    Option (PublishedComparison c i j mark) := do
  let pair ← ReferenceDistance.pairWith? p i j (armFrom c.published)
  let r ← pair.atMark? mark
  if bound : ∀ x ∈ r.left.entries ++ r.right.entries, c.published.lookup x.1 = some x.2 then
    return ⟨r,bound⟩
  none

theorem PublishedComparison.input_derived {m g p i j mark} {c : Certificate m g p}
    (comparison : PublishedComparison c i j mark) {x} (used : x ∈ comparison.left.entries ++ comparison.right.entries) :
    p <+: x.1 ∧ p.length < x.1.length ∧ Derives m g c.published x.1 x.2 :=
  c.lookup_derived (comparison.bound x used)

private def stereoAt? {m g} (p : List Nat) (focus : RawMolecule.CanonicalBranchNode) (depth : Nat)
    (child : (q : List Nat) → Option (Certificate m g q)) : Option (Certificate m g p) := do
  let collect (paths : List (List Nat)) := paths.eraseDups.filterMap fun q => do
    return (⟨q,← child q⟩ : Located m g)
  let single := do
    let f ← SignedPair.frame? m p depth
    let rows := collect (f.leftPaths ++ f.rightPaths)
    let table := rows.map Located.entry
    let ls ← project table f.leftPaths
    let rs ← project table f.rightPaths
    if let some step := DiscoveredPriority.check? f ls rs then
      let ⟨r,read⟩ ← (geometric g step.actual.ligands step.reflected.ligands).attach
      return ← finish (some r) (ls ++ rs) rows (fun _ subs => .distinguished step (fun x h => (subs x h).1) (fun x h => (subs x h).2) read)
    let pair ← f.checkWith? table
    return ← finish none pair.val.required rows (fun _ subs => .indistinguishable pair.val (fun x h => (subs x h).1) (fun x h => (subs x h).2))
  if let some result := single then return result
  let rows := collect (RingAuxiliaryInventory.promotionPaths m focus)
  let f ← ReferenceFrame.molecularFrame? m g p depth (armFrom (rows.map Located.entry))
  if let some s := f.ordinary? then
    return ← finish s.outcome.reading? f.inputs rows (fun _ subs =>
      .ordinary f s (fun x h => (subs x h).1) (fun x h => (subs x h).2) rfl)
  let pop ← (← f.promotion?).population?
  let ⟨v,agree⟩ ← pop.consensus?.attach
  finish v pop.inputs rows (fun _ subs => .promotion pop (fun x h => (subs x h).1) (fun x h => (subs x h).2) agree)

private def atPath? {m g} (p : List Nat) (depth : Nat)
    (child : (q : List Nat) → Option (Certificate m g q)) : Option (Certificate m g p) := do
  let focus ← occurrence? m p
  guard ((m.atoms[focus.atom]?).any fun a => a.element == .C)
  if let some ⟨order,ranked⟩ := (atomicOrder? m p depth).attach then
    let ⟨r,read⟩ ← (geometric g order order).attach
    return ⟨some r,[],by simp,by simp,by simp,.atomic ranked read⟩
  -- Each stereo decision checks the earlier constitution of the tied arms.
  if let some result := stereoAt? p focus depth child then return result
  let ranking ← IsotopePriority.rank? m p
  let ⟨r,read⟩ ← (geometric g ranking.order ranking.order).attach
  return ⟨some r,[],by simp,by simp,by simp,.isotopic ranking read⟩

private def descendants {m g} (p : List Nat) (child : (q : List Nat) → Option (Certificate m g q))
    (q : List Nat) : Option (Certificate m g q) :=
  if p.length < q.length ∧ p <+: q then child q else none

/-- Bottom-up comparison and auxiliary assignment on one digraph. Fuel
exhaustion leaves the occurrence unresolved. The outer option preserves
this distinction from a proved absence. -/
def derive? (m : RawMolecule) (g : Geometry) (depth : Nat) : Nat → (p : List Nat) →
    Option (Certificate m g p)
  | 0,_ => none
  | fuel+1,p => if saturatedWithHalogens m then atPath? p depth (descendants p (derive? m g depth fuel)) else none

/-- Beyond the maximum remaining length of a real retained path, more
recursion fuel leaves the complete certificate unchanged. This includes
unresolved occurrences, negative verdicts and every published child. -/
theorem derive_stable (m : RawMolecule) (g : Geometry) (depth fuel extra : Nat) (p : List Nat)
    (enough : m.atomCount < p.length + fuel) :
    derive? m g depth fuel p = derive? m g depth (fuel+extra) p := by
  induction fuel generalizing p with
  | zero =>
    cases extra with
    | zero => rfl
    | succ extra =>
      simp only [derive?]
      split <;> rename_i admitted
      · have missing : occurrence? m p = none := by
          cases reached : occurrence? m p with
          | none => rfl
          | some focus =>
            have short := OccurrenceTable.reached_length (OccurrenceTable.endpoints_of_saturated admitted) reached
            omega
        simp [atPath?,missing]
      · rfl
  | succ fuel ih =>
    simp only [Nat.succ_add,derive?]
    split
    · congr 1
      funext q
      unfold descendants
      split
      · rename_i h
        exact ih q (by have := h.1; omega)
      · rfl
    · rfl

/-- Store the whole dependent result, including unresolved and negative
results. A row is bound to one molecular occurrence and one observation depth. -/
structure CacheRow (m : RawMolecule) (g : Geometry) (depth : Nat) where
  path : List Nat
  result : Option (Certificate m g path)
  exactResult : result = derive? m g depth (m.atomCount+1) path

abbrev Cache (m : RawMolecule) (g : Geometry) (depth : Nat) := List (CacheRow m g depth)

def Cache.read {m g depth} (p : List Nat) : Cache m g depth → Option (Certificate m g p)
  | [] => derive? m g depth (m.atomCount+1) p
  | row :: rows => if same : row.path = p then same ▸ row.result else Cache.read p rows

theorem Cache.read_exact {m g depth} (p : List Nat) (rows : Cache m g depth) :
    rows.read p = derive? m g depth (m.atomCount+1) p := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    by_cases same : row.path = p
    · subst p
      simpa [Cache.read] using row.exactResult
    · simpa [Cache.read,same] using ih

private def cacheRow {m g depth} (rows : Cache m g depth) (p : List Nat) : CacheRow m g depth :=
  let result := if saturatedWithHalogens m then atPath? p depth (descendants p (fun q => rows.read q)) else none
  ⟨p,result,by
    unfold result
    rw [derive?]
    split
    · congr 1
      funext q
      unfold descendants
      split
      · rename_i h
        change rows.read q = derive? m g depth m.atomCount q
        rw [Cache.read_exact]
        exact (derive_stable m g depth m.atomCount 1 q (by have := h.1; omega)).symm
      · rfl
    · rfl⟩

/-- Materialize descendant certificates before their parents. The same
cache serves repeated comparisons and auxiliary updates at a shared path.
An address outside the batch still receives its ordinary molecular computation. -/
def cache (m : RawMolecule) (g : Geometry) (depth : Nat) (paths : List (List Nat)) : Cache m g depth :=
  (paths.eraseDups.mergeSort fun p q => decide (q.length ≤ p.length)).foldl
    (fun rows p => cacheRow rows p :: rows) []

def cacheAtRoot (m : RawMolecule) (g : Geometry) (depth root : Nat) (extra : List (List Nat)) :
    Cache m g depth :=
  let paths := ((occurrence? m [root]).map (RingAuxiliaryInventory.promotionPaths m)).getD []
  cache m g depth ([root] :: (paths ++ extra))

end TetraStereo.Engine.RingChemicalPriority.ReferenceDerivation

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceDerivation.Derives.weaken
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceDerivation.derive?
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceDerivation.Certificate.lookup_derived

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceDerivation.Derives.chemical_letter
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceDerivation.PublishedComparison.input_derived
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceDerivation.LetterBasis.reversal_count
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceDerivation.PublishedFrame.input_derived
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceDerivation.derive_stable
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceDerivation.Cache.read_exact
