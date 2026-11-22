import TetraStereo.Engine.RingFrameCoverage
import TetraStereo.Engine.RingCursorMass

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority.RecursiveSigned
open OneCenter LocalizedGenericMarkedRecalculation Recursive ReferenceFrame
open InventoryPriority (Entries)
open LocalizedChemicalRingPromotionAggregation (readingBalance)

/-- The two surviving hands of a completed population, for publication at a child occurrence.
The population mirror law determines the reflected hand even with mixed strict and tied trials. -/
def populationReading {m g p} (s : Population m g p) : Option Reading :=
  (survivingHand (readingBalance (s.hands false))).map fun hand =>
    ⟨hand, if s.frame.reversals % 2 = 0 then hand.swap else hand⟩

theorem populationReading_label {m g p} (s : Population m g p) :
    (populationReading s).bind Reading.label = s.signedDescriptor := by
  rw [s.signedDescriptor_eq]
  unfold populationReading
  cases survivingHand (readingBalance (s.hands false)) with
  | none => rfl
  | some hand =>
    cases hand <;> by_cases even : s.frame.reversals % 2 = 0 <;>
      simp [even,Reading.label,caseFromMirror?,RS.swap,pseudoRSOfRS]

theorem populationReading_reflected {m g p} (s : Population m g p) :
    (populationReading s).map Reading.reflected = survivingHand (readingBalance (s.hands true)) := by
  rw [s.mirror_balance]
  let z := readingBalance (s.hands false)
  change ((survivingHand z).map _).map Reading.reflected = survivingHand (if _ then -z else z)
  by_cases even : s.frame.reversals % 2 = 0
  · rcases lt_trichotomy z 0 with h | h | h
    · simp [even,survivingHand,h,not_lt.mpr h.le,RS.swap]
    · simp [even,survivingHand,h]
    · simp [even,survivingHand,h,not_lt.mpr h.le,RS.swap]
  · simp [even,Option.map_map,Function.comp_def]

private theorem reading_determined_by_label {a b : Option Reading}
    (same : a.bind Reading.label = b.bind Reading.label) : a = b := by
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b => obtain ⟨h,k⟩ := b; cases h <;> cases k <;> cases same
  | some a =>
    obtain ⟨h,k⟩ := a
    cases b with
    | none => cases h <;> cases k <;> cases same
    | some b =>
      obtain ⟨i,j⟩ := b
      cases h <;> cases k <;> cases i <;> cases j <;> first | rfl | cases same

/-- Every consensus reading has exactly the same actual and reflected hands
under signed aggregation, so legacy signed inputs retain both components. -/
theorem populationReading_of_consensus {m g p} (s : Population m g p) {v}
    (accepted : s.consensus? = some v) : populationReading s = v :=
  reading_determined_by_label ((populationReading_label s).trans (s.signedDescriptor_of_consensus accepted))

/-- A nonzero signed result is realized on both geometries by one eligible
mark and its actual pair of strict priority orders. -/
theorem populationReading_witness {m g p} (s : Population m g p) {r}
    (observed : populationReading s = some r) :
    ∃ (t : Trial s.frame) (a b : List Nat), t ∈ s.trials ∧
      ReferenceFrame.orders s.frame.ids t.table false = [a] ∧
      ReferenceFrame.orders s.frame.ids t.table true = [b] ∧ geometric g a b = some r := by
  obtain ⟨hand,survives,eqn⟩ := Option.map_eq_some_iff.mp observed
  obtain ⟨t,a,b,member,ha,hb,actual⟩ := s.surviving_trial survives
  cases out : t.outcome with
  | tied i j neq inside both noStrict => simpa [ha] using noStrict false
  | assigned x y hx hy raw hg =>
    obtain rfl : x = a := by simpa [ha] using hx.symm
    obtain rfl : y = b := by simpa [hb] using hy.symm
    have sameA := Option.some.inj ((t.chemical_letter hx hy hg).1.symm.trans actual)
    have sameB := t.mirror_hand
    cases eqn
    obtain ⟨left,right⟩ := raw
    change left = hand at sameA
    subst hand
    refine ⟨t,x,y,member,hx,hy,?_⟩
    by_cases even : s.frame.reversals % 2 = 0
    · have flip : right = left.swap := by
        simpa [Trial.hand?,out,Outcome.reading?,even] using sameB
      simpa [even,flip] using hg
    · have keep : right = left := by
        simpa [Trial.hand?,out,Outcome.reading?,even] using sameB
      simpa [even,keep] using hg

/-- One completed molecular inference before its signed auxiliary premises are discharged. -/
inductive Step (m : RawMolecule) (g : Geometry) (p : List Nat) where
  | atomic (depth : Nat) (order : List Nat) (reading : Reading)
      (ranked : atomicOrder? m p depth = some order) (observed : geometric g order order = some reading)
  | isotopic (ranking : IsotopePriority.Ranking m p) (reading : Reading)
      (observed : geometric g ranking.order ranking.order = some reading)
  | cursorMass {depth : Nat} (ranking : CursorMass.Ranking m p depth) (reading : Reading)
      (observed : geometric g ranking.order ranking.order = some reading)
  | distinguished {ls rs} (comparison : DiscoveredPriority.Step m p ls rs) (reading : Reading)
      (observed : geometric g comparison.actual.ligands comparison.reflected.ligands = some reading)
  | indistinguishable (pair : SignedPair.Pair m p)
  | cursorTie {depth : Nat} (es : Entries) (why : CursorTie.SinglePair m p depth es)
  | ordinary (frame : MolecularFrame m g p) (result : Ordinary frame)
  | promotion (population : Population m g p)

def Step.inputs {m g p} : Step m g p → Entries
  | .atomic .. | .isotopic .. | .cursorMass .. => []
  | .distinguished (ls := ls) (rs := rs) .. => ls ++ rs
  | .indistinguishable pair => pair.required
  | .cursorTie es _ => es
  | .ordinary f _ => f.inputs
  | .promotion s => s.inputs

def Step.reading? {m g p} : Step m g p → Option Reading
  | .atomic _ _ r .. | .isotopic _ r _ | .cursorMass _ r _ | .distinguished _ r _ => some r
  | .indistinguishable _ | .cursorTie .. => none
  | .ordinary _ o => o.outcome.reading?
  | .promotion s => populationReading s

/-- Three molecular reasons for an empty reading. The ordinary frame retains a tied
incident pair on both geometries; a signed promotion requires zero balance. -/
def Step.refuses {m g p} : Step m g p → Prop
  | .atomic .. | .isotopic .. | .cursorMass .. | .distinguished .. => False
  | .indistinguishable _ | .cursorTie .. => True
  | .ordinary f _ => ∀ rev, ReferenceFrame.orders f.ids (entries f.rows) rev = []
  | .promotion s => readingBalance (s.hands false) = 0

theorem Step.reading?_eq_none_iff {m g p} (s : Step m g p) : s.reading? = none ↔ s.refuses := by
  cases s with
  | atomic | isotopic | cursorMass | distinguished | indistinguishable | cursorTie => simp [Step.reading?,Step.refuses]
  | ordinary f o =>
    simp only [Step.reading?,Step.refuses]
    cases h : o.outcome with
    | tied _ _ _ _ _ noneStrict => exact ⟨fun _ => noneStrict,fun _ => rfl⟩
    | assigned a b left right r read =>
      constructor
      · intro impossible
        cases impossible
      · intro empty
        simpa [left] using empty false
  | promotion s =>
    change populationReading s = none ↔ readingBalance (s.hands false) = 0
    have label := populationReading_label s
    rw [← s.signedDescriptor_none_iff,← label]
    cases h : populationReading s with
    | none => simp
    | some r => obtain ⟨a,b⟩ := r; cases a <;> cases b <;> decide

/-- The actual priority order, and the number of pairs whose priority reverses,
as independently witnessed by the inference that supplied the auxiliary. -/
def Step.orders {m g p} : Step m g p → List Nat → Nat → Prop
  | .atomic _ a .., order, n => order = a ∧ n = 0
  | .isotopic ranking .., order, n => order = ranking.order ∧ n = 0
  | .cursorMass ranking .., order, n => order = ranking.order ∧ n = 0
  | .distinguished s .., order, n => order = s.actual.ligands ∧ n = s.basis.five.toNat
  | .indistinguishable _, _, _ | .cursorTie .., _, _ => False
  | .ordinary f _, order, n =>
      ReferenceFrame.orders f.ids (entries f.rows) false = [order] ∧ n = f.reversals
  | .promotion s, order, n =>
      (∃ t ∈ s.trials, ReferenceFrame.orders s.frame.ids t.table false = [order]) ∧ n = s.frame.reversals

theorem Step.chemical_letter {m g p} (s : Step m g p) {r}
    (observed : s.reading? = some r) :
    ∃ a n, s.orders a n ∧ readback? g a = some r.actual ∧
      r.label = some (if n % 2 = 0 then .chiral r.actual else .pseudoasymmetric (pseudoRSOfRS r.actual)) := by
  cases s with
  | atomic depth a raw ranked read =>
    obtain rfl : raw = r := Option.some.inj observed
    have h := constitutional_casing read
    exact ⟨_,0,⟨rfl,rfl⟩,h.1,h.2.2⟩
  | isotopic ranking raw read | cursorMass ranking raw read =>
    obtain rfl : raw = r := Option.some.inj observed
    have h := constitutional_casing read
    exact ⟨_,0,⟨rfl,rfl⟩,h.1,h.2.2⟩
  | distinguished s raw read =>
    obtain rfl : raw = r := Option.some.inj observed
    obtain ⟨order,label⟩ := s.chemical_letter read
    exact ⟨_,_,⟨rfl,rfl⟩,order,by cases h : s.basis.five <;> simpa [h] using label⟩
  | indistinguishable | cursorTie => cases observed
  | ordinary f o =>
    change o.outcome.reading? = some r at observed
    cases out : o.outcome with
    | tied => simp [out,Outcome.reading?] at observed
    | assigned a b ha hb raw hg =>
      obtain rfl : raw = r := by simpa [out,Outcome.reading?] using observed
      exact ⟨_,_,⟨ha,rfl⟩,f.chemical_letter ha hb hg⟩
  | promotion s =>
    change populationReading s = some r at observed
    obtain ⟨hand,survives,eqn⟩ := Option.map_eq_some_iff.mp observed
    obtain ⟨t,a,b,member,ha,_,actual⟩ := s.surviving_trial survives
    have label := populationReading_label s
    rw [observed,s.signedDescriptor_eq,survives] at label
    cases eqn
    exact ⟨a,s.frame.reversals,⟨⟨t,member,ha⟩,rfl⟩,actual,label⟩

/-- The recursion tree for signed chemical decisions. Every premise is at the exact,
strictly deeper address in the same retained digraph and publication table. -/
inductive Derives (m : RawMolecule) (g : Geometry) (published : Entries) :
    List Nat → Option Reading → Prop where
  | step {p} (s : Step m g p)
      (present : s.inputs ⊆ published)
      (deeper : ∀ x ∈ s.inputs, p <+: x.1 ∧ p.length < x.1.length)
      (children : ∀ x ∈ s.inputs, Derives m g published x.1 x.2) :
      Derives m g published p s.reading?

theorem Derives.localize {m g es p v} (d : Derives m g es p v) {other : Entries}
    (keep : ∀ x ∈ es, (p <+: x.1 ∧ p.length < x.1.length) → x ∈ other) :
    Derives m g other p v := by
  induction d with
  | step s present deeper _ ih =>
    exact .step s (fun x hx => keep x (present hx) (deeper x hx)) deeper
      (fun x hx => ih x hx (fun y hy h => keep y hy ⟨(deeper x hx).1.trans h.1,Nat.lt_trans (deeper x hx).2 h.2⟩))

theorem Derives.chemical_letter {m g es p r} (d : Derives m g es p (some r)) :
    ∃ (s : Step m g p) (a : List Nat) (n : Nat), s.reading? = some r ∧ s.orders a n ∧
      (∀ x ∈ s.inputs, x ∈ es ∧ Derives m g es x.1 x.2) ∧ readback? g a = some r.actual ∧
      r.label = some (if n % 2 = 0 then .chiral r.actual else .pseudoasymmetric (pseudoRSOfRS r.actual)) := by
  generalize h : some r = v at d
  cases d with
  | step s present deeper children =>
    obtain ⟨a,n,o,hand,letter⟩ := s.chemical_letter h.symm
    exact ⟨s,a,n,rfl,o,fun x hx => ⟨present hx,children x hx⟩,hand,letter⟩

structure Certificate (m : RawMolecule) (g : Geometry) (p : List Nat) where
  step : Step m g p
  published : Entries
  consistent : (published.map Prod.fst).Nodup
  below : ∀ x ∈ published, p <+: x.1 ∧ p.length < x.1.length
  bound : step.inputs ⊆ published
  issued : ∀ x ∈ published, Derives m g published x.1 x.2

abbrev Certificate.verdict {m g p} (c : Certificate m g p) := c.step.reading?

theorem Certificate.derived {m g p} (c : Certificate m g p) : Derives m g c.published p c.verdict :=
  .step c.step c.bound (fun x h => c.below x (c.bound h)) (fun x h => c.issued x (c.bound h))

theorem Certificate.lookup_derived {m g p} (c : Certificate m g p) {q v}
    (found : c.published.lookup q = some v) :
    p <+: q ∧ p.length < q.length ∧ Derives m g c.published q v := by
  obtain ⟨l,r,formed,_⟩ := List.lookup_eq_some_iff.mp found
  have member : (q,v) ∈ c.published := by rw [formed]; simp
  exact ⟨(c.below _ member).1,(c.below _ member).2,c.issued _ member⟩

/-- For each sign actually consumed by the root inference, recover its unique
published value and its recursively justified molecular provenance. -/
theorem Certificate.input_derived {m g p} (c : Certificate m g p) {x}
    (used : x ∈ c.step.inputs) :
    c.published.lookup x.1 = some x.2 ∧ Derives m g c.published x.1 x.2 := by
  have mem := c.bound used
  refine ⟨?_,c.issued x mem⟩
  have unique := c.consistent
  generalize c.published = es at unique mem ⊢
  induction es with
  | nil => cases mem
  | cons y ys ih =>
    have u := List.nodup_cons.mp unique
    rcases List.mem_cons.mp mem with rfl | tail
    · simp [List.lookup]
    · have different : x.1 ≠ y.1 := by
        intro same
        exact u.1 (same ▸ List.mem_map_of_mem (f := Prod.fst) tail)
      have no : (x.1 == y.1) = false := by simpa using different
      simpa [List.lookup,no] using ih u.2 tail

private abbrev Child (m : RawMolecule) (g : Geometry) := (q : List Nat) × Certificate m g q
private def Child.entry {m g} (c : Child m g) := (c.1,c.2.verdict)
private def Child.publications {m g} (c : Child m g) := c.entry :: c.2.published

private def finish {m g p} (s : Step m g p) (children : List (Child m g)) :
    Option (Certificate m g p) := do
  let used := children.filter (fun c => s.inputs.contains c.entry)
  let env := (used.flatMap Child.publications).dedup
  if unique : (env.map Prod.fst).Nodup then
    if proper : ∀ x ∈ env, p <+: x.1 ∧ p.length < x.1.length then
      if bound : ∀ x ∈ s.inputs, x ∈ env then
        have issued : ∀ x ∈ env, Derives m g env x.1 x.2 := by
          intro x hx
          obtain ⟨child,inside,entry⟩ := List.mem_flatMap.mp (List.mem_dedup.mp hx)
          have sub : child.2.published ⊆ env := fun y hy =>
            List.mem_dedup.mpr (List.mem_flatMap.mpr ⟨child,inside,List.mem_cons_of_mem _ hy⟩)
          rcases List.mem_cons.mp entry with rfl | deep
          · exact child.2.derived.localize (fun _ h _ => sub h)
          · exact (child.2.issued x deep).localize (fun _ h _ => sub h)
        return ⟨s,env,unique,proper,fun x hx => bound x hx,issued⟩
  none

private def stereoAt? {m g} (p : List Nat) (focus : RawMolecule.CanonicalBranchNode) (depth : Nat)
    (child : (q : List Nat) → Option (Certificate m g q)) : Option (Certificate m g p) := do
  let collect (paths : List (List Nat)) := paths.eraseDups.filterMap fun q =>
    (child q).map fun c => (⟨q,c⟩ : Child m g)
  let single := do
    let f ← SignedPair.frame? m p depth
    let rows := collect (f.leftPaths ++ f.rightPaths)
    let table := rows.map Child.entry
    let project (paths : List (List Nat)) := paths.mapM fun q => do return (q,← table.lookup q)
    let ls ← project f.leftPaths
    let rs ← project f.rightPaths
    if let some s := DiscoveredPriority.check? f ls rs then
      let ⟨r,h⟩ ← (geometric g s.actual.ligands s.reflected.ligands).attach
      return ← finish (.distinguished s r h) rows
    let pair ← f.checkWith? table
    return ← finish (.indistinguishable pair.val) rows
  if let some result := single then return result
  let rows := collect (RingAuxiliaryInventory.promotionPaths m focus)
  let signed := rows.map Child.entry
  let completedFrame := do
    let frame ← molecularFrame? m g p depth (ReferenceDerivation.armFrom signed)
    match ← frame.resolve? with
    | .inl ordinary => finish (.ordinary frame ordinary) rows
    | .inr population => finish (.promotion population.val) rows
  if let some result := completedFrame then return result
  -- Some ligand cursors face their original parent. Test the full two-geometry
  -- tree equality there, together with ten strict checks on the other pairs.
  if let some tied := CursorTie.singlePair? m p depth [] then
    return ← finish (.cursorTie [] tied) []
  let tied ← CursorTie.singlePair? m p depth signed
  finish (.cursorTie signed tied) rows

private def atPath? {m g} (p : List Nat) (depth : Nat)
    (child : (q : List Nat) → Option (Certificate m g q)) : Option (Certificate m g p) := do
  let focus ← occurrence? m p
  guard ((m.atoms[focus.atom]?).any fun a => a.element == .C)
  if let some ⟨order,ranked⟩ := (atomicOrder? m p depth).attach then
    let ⟨r,observed⟩ ← (geometric g order order).attach
    return ⟨.atomic depth order r ranked observed,[],by simp,by simp,by simp [Step.inputs],by simp⟩
  if m.atoms.any (fun a => a.isotope?.isSome) then
    if let some rank := CursorMass.rank? m p depth then
      let ⟨r,observed⟩ ← (geometric g rank.order rank.order).attach
      return ⟨.cursorMass rank r observed,[],by simp,by simp,by simp [Step.inputs],by simp⟩
  if let some result := stereoAt? p focus depth child then return result
  let ranking ← IsotopePriority.rank? m p
  let ⟨r,observed⟩ ← (geometric g ranking.order ranking.order).attach
  return ⟨.isotopic ranking r observed,[],by simp,by simp,by simp [Step.inputs],by simp⟩

private def descendants {m g} (p : List Nat) (child : (q : List Nat) → Option (Certificate m g q))
    (q : List Nat) : Option (Certificate m g q) :=
  if p.length < q.length ∧ p <+: q then child q else none

/-- Derive the entire occurrence tree with signed aggregation at *every* promoted
carbon. The empty outer option distinguishes a missing comparison or calibration
from a derived tie or cancellation in a child's signed entry. -/
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

/-- Store the complete signed recursive result, including a certified absence or
an unresolved occurrence. The proof binds it to the precise address and depth. -/
structure CacheRow (m : RawMolecule) (g : Geometry) (depth : Nat) where
  path : List Nat
  result : Option (Certificate m g path)
  exactResult : result = derive? m g depth (m.atomCount+1) path

abbrev Cache (m : RawMolecule) (g : Geometry) (depth : Nat) :=
  Std.HashMap (List Nat) (CacheRow m g depth)

/-- Reuse the entire dependent certificate when the stored occurrence matches.
Out-of-batch queries use the same chemical evaluator. -/
def Cache.read {m g depth} (rows : Cache m g depth) (p : List Nat) : Option (Certificate m g p) :=
  match rows[p]? with
  | some row => if same : row.path = p then same ▸ row.result else derive? m g depth (m.atomCount+1) p
  | none => derive? m g depth (m.atomCount+1) p

theorem Cache.read_exact {m g depth} (rows : Cache m g depth) (p : List Nat) :
    rows.read p = derive? m g depth (m.atomCount+1) p := by
  unfold Cache.read
  split
  · rename_i row _
    split
    · rename_i same
      subst p
      exact row.exactResult
    · rfl
  · rfl

private def cacheRow {m g depth} (rows : Cache m g depth) (p : List Nat) : CacheRow m g depth :=
  let result := if saturatedWithHalogens m then atPath? p depth (descendants p rows.read) else none
  ⟨p,result,by
    unfold result
    rw [derive?]
    split
    · congr 1
      funext q
      unfold descendants
      split
      · rename_i h
        rw [Cache.read_exact]
        exact (derive_stable m g depth m.atomCount 1 q (by have := h.1; omega)).symm
      · rfl
    · rfl⟩

/-- Compute proper descendants before their ancestors. Each occurrence, including
a cached missing outcome, occupies one slot in the address map. -/
def cache (m : RawMolecule) (g : Geometry) (depth : Nat) (paths : List (List Nat)) : Cache m g depth :=
  (paths.eraseDups.mergeSort fun p q => decide (q.length ≤ p.length)).foldl
    (fun rows p => rows.insert p (cacheRow rows p)) ({} : Cache m g depth)

def cacheAtRoot (m : RawMolecule) (g : Geometry) (depth root : Nat) (extra : List (List Nat) := []) :
    Cache m g depth :=
  let paths := ((occurrence? m [root]).map (RingAuxiliaryInventory.promotionPaths m)).getD []
  cache m g depth ([root] :: (paths ++ extra))

/-- Fresh-root cache lookup agrees with the ordinary atom-count fuel bound. -/
theorem cacheAtRoot_exact (m : RawMolecule) (g : Geometry) (depth root : Nat) (extra : List (List Nat)) :
    (cacheAtRoot m g depth root extra).read [root] = derive? m g depth m.atomCount [root] := by
  rw [Cache.read_exact]
  exact (derive_stable m g depth m.atomCount 1 [root] (by simp)).symm

end TetraStereo.Engine.RingChemicalPriority.RecursiveSigned

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.RecursiveSigned.derive?
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.RecursiveSigned.derive_stable
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.RecursiveSigned.Derives.localize
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.RecursiveSigned.Derives.chemical_letter
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.RecursiveSigned.Certificate.lookup_derived
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.RecursiveSigned.populationReading_label
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.RecursiveSigned.populationReading_reflected
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.RecursiveSigned.populationReading_of_consensus
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.RecursiveSigned.populationReading_witness
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.RecursiveSigned.Step.reading?_eq_none_iff
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.RecursiveSigned.Certificate.input_derived
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.RecursiveSigned.Cache.read_exact
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.RecursiveSigned.cacheAtRoot_exact
