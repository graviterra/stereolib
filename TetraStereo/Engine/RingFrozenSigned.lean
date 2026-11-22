import TetraStereo.Engine.RingCursorStereo

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority.FrozenSigned
open OneCenter LocalizedGenericMarkedRecalculation Recursive ReferenceFrame
open InventoryPriority (Entries)

abbrev Cache := RecursiveSigned.Cache

/-- The actual molecular frame, built and resolved against one snapshot.
Every premise is a strict descendant and has its exact value in that snapshot. -/
structure Frame (m : RawMolecule) (g : Geometry) (depth : Nat) (p : List Nat) where
  snapshot : Entries
  frame : MolecularFrame m g p
  built : molecularFrame? m g p depth (ReferenceDerivation.armFrom snapshot) = some frame
  outcome : Ordinary frame ⊕ {s : Population m g p // s.frame.toMolecularFrame = frame}
  resolved : frame.resolve? = some outcome
  inputs : ∀ x ∈ frame.inputs, snapshot.lookup x.1 = some x.2 ∧ p <+: x.1 ∧ p.length < x.1.length

def Frame.step {m g depth p} (f : Frame m g depth p) : RecursiveSigned.Step m g p :=
  match f.outcome with
  | .inl o => .ordinary f.frame o
  | .inr s => .promotion s.val

theorem Frame.step_inputs {m g depth p} (f : Frame m g depth p) : f.step.inputs = f.frame.inputs := by
  cases h : f.outcome with
  | inl o => simp [Frame.step,h,RecursiveSigned.Step.inputs]
  | inr s =>
    simp only [Frame.step,h,RecursiveSigned.Step.inputs]
    exact congrArg MolecularFrame.inputs s.property

def frame? (m : RawMolecule) (g : Geometry) (depth : Nat) (p : List Nat) (es : Entries) :
    Option (Frame m g depth p) := do
  let ⟨f,built⟩ ← (molecularFrame? m g p depth (ReferenceDerivation.armFrom es)).attach
  let ⟨o,resolved⟩ ← f.resolve?.attach
  if bound : ∀ x ∈ f.inputs, es.lookup x.1 = some x.2 ∧ p <+: x.1 ∧ p.length < x.1.length then
    return ⟨es,f,built,o,resolved,bound⟩
  none

def leftWitness {m g depth base p} (a : @CursorStereo.Assignment m g depth base p) :
    List Nat × Option Reading :=
  (a.pair.a.node.history.reverse,some ⟨a.pair.hand,a.pair.hand.swap⟩)

def rightWitness {m g depth base p} (a : @CursorStereo.Assignment m g depth base p) :
    List Nat × Option Reading :=
  (a.pair.b.node.history.reverse,some ⟨a.pair.hand.swap,a.pair.hand⟩)

/-- All cursors visited by the signed-site traversal at its exact fuel. -/
def visited (m : RawMolecule) : Nat → CanonicalRerootCursor → List CanonicalRerootCursor
  | 0,_ => []
  | fuel+1,c => c :: (c.children m).flatMap (visited m fuel)

def sites {m g depth base p} (a : @CursorStereo.Assignment m g depth base p) :=
  visited m (IsotopePriority.budget m+1) a.pair.left ++ visited m (IsotopePriority.budget m+1) a.pair.right

/-- A noncandidate site uses the molecular exclusion test. Every other
reading, including a derived absence, must exist in the frozen table. -/
def Visible {m g depth} (base : Cache m g depth) (es : Entries) (p : List Nat)
    (c : CanonicalRerootCursor) : Prop :=
  UnitClasses.classAt? m [] ⟨c,[c.node],[],true⟩ = some 0 ∨
    (CursorStereo.read? base p c).isSome = true ∧
      es.lookup c.node.history.reverse = CursorStereo.read? base p c

instance {m g depth} {base : Cache m g depth} {es p c} : Decidable (Visible base es p c) := by
  unfold Visible
  infer_instance

private theorem Visible.weaken {m g depth} {base : Cache m g depth} {es more p c}
    (v : Visible base es p c) (keep : ∀ q w, es.lookup q = some w → more.lookup q = some w) :
    Visible base more p c := by
  rcases v with h | ⟨present,same⟩
  · exact Or.inl h
  · obtain ⟨w,hit⟩ := Option.isSome_iff_exists.mp present
    exact Or.inr ⟨present, (keep _ _ (same.trans hit)).trans hit.symm⟩

/-- A molecular publication in a shared original-root table. Incoming Rule 5
reads require both exact signed witnesses there. Parent frames may use any
earlier kind of publication, including another resolved frame. -/
inductive Published {m g depth} (base : Cache m g depth) (es : Entries) :
    List Nat → Option Reading → Prop where
  | cached {p} (c : RecursiveSigned.Certificate m g p) (hit : base.read p = some c) :
      Published base es p c.verdict
  | incoming {p} (absent : base.read p = none) (a : CursorStereo.Assignment base p) (hit : CursorStereo.assign? base p = some a)
      (left : es.lookup (leftWitness a).1 = some (leftWitness a).2)
      (right : es.lookup (rightWitness a).1 = some (rightWitness a).2)
      (visible : ∀ c ∈ sites a, Visible base es p c) :
      Published base es p (some ⟨a.hand,a.hand⟩)
  | frame {p} (absent : base.read p = none) (f : Frame m g depth p)
      (bound : ∀ x ∈ f.step.inputs, es.lookup x.1 = some x.2)
      (children : ∀ x ∈ f.step.inputs, Published base es x.1 x.2) :
      Published base es p f.step.reading?

private theorem Published.weaken {m g depth} {base : Cache m g depth} {es more : Entries} {p v}
    (pub : Published base es p v)
    (keep : ∀ q w, es.lookup q = some w → more.lookup q = some w) : Published base more p v := by
  induction pub with
  | cached c hit => exact .cached c hit
  | incoming absent a hit left right visible =>
    exact .incoming absent a hit (keep _ _ left) (keep _ _ right) (fun c hc => (visible c hc).weaken keep)
  | frame absent f bound _ ih => exact .frame absent f (fun x hx => keep _ _ (bound x hx)) ih

structure Table {m g depth} (base : Cache m g depth) where
  entries : Entries
  unique : (entries.map Prod.fst).Nodup
  issued : ∀ x ∈ entries, Published base entries x.1 x.2

theorem Table.lookup_published {m g depth base} (t : @Table m g depth base) {p v}
    (hit : t.entries.lookup p = some v) : Published base t.entries p v := by
  obtain ⟨l,r,formed,_⟩ := List.lookup_eq_some_iff.mp hit
  exact t.issued (p,v) (by rw [formed]; simp)

theorem Table.agrees_cached {m g depth base} (t : @Table m g depth base) {p v}
    {c : RecursiveSigned.Certificate m g p}
    (hit : t.entries.lookup p = some v) (cached : base.read p = some c) : c.verdict = v := by
  cases t.lookup_published hit with
  | cached cert got =>
    obtain rfl := Option.some.inj (cached.symm.trans got)
    rfl
  | incoming absent a hit left right visible => simp [absent] at cached
  | frame absent f bound children => simp [absent] at cached

private def Table.insert {m g depth base} (t : @Table m g depth base) (p : List Nat) (v : Option Reading)
    (proof : Published base t.entries p v) : Table base :=
  if fresh : p ∉ t.entries.map Prod.fst then
    let es := (p,v) :: t.entries
    have keep (q w) (hit : t.entries.lookup q = some w) : es.lookup q = some w := by
      have neq : q ≠ p := by
        rintro rfl
        obtain ⟨l,r,formed,_⟩ := List.lookup_eq_some_iff.mp hit
        apply fresh
        rw [formed]
        simp
      have no : (q == p) = false := by simpa using neq
      simpa [es,List.lookup,no] using hit
    ⟨es,List.nodup_cons.mpr ⟨fresh,t.unique⟩,by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | tail
      · exact proof.weaken keep
      · exact (t.issued x tail).weaken keep⟩
  else t

private def frameProof {m g depth base} (t : @Table m g depth base) {p}
    (absent : base.read p = none) (f : Frame m g depth p) (same : f.snapshot = t.entries) : Published base t.entries p f.step.reading? := by
  have hit (x) (hx : x ∈ f.step.inputs) : t.entries.lookup x.1 = some x.2 := by
    rw [← same]
    exact (f.inputs x (f.step_inputs ▸ hx)).1
  exact .frame absent f hit (fun x hx => t.lookup_published (hit x hx))

private def publish {m g depth base} (t : @Table m g depth base) (p : List Nat) : Table base := Id.run do
  match hr : base.read p with
  | some c => return t.insert p c.verdict (.cached c hr)
  | none =>
    if let some ⟨a,hit⟩ := (CursorStereo.assign? base p).attach then
      if both : t.entries.lookup (leftWitness a).1 = some (leftWitness a).2 ∧
          t.entries.lookup (rightWitness a).1 = some (rightWitness a).2 then
        if visible : ∀ c ∈ sites a, Visible base t.entries p c then
          return t.insert p (some ⟨a.hand,a.hand⟩) (.incoming hr a hit both.1 both.2 visible)
    if let some f := frame? m g depth p t.entries then
      if same : f.snapshot = t.entries then
        return t.insert p f.step.reading? (frameProof t hr f same)
    return t

structure Certificate {m g depth} (base : Cache m g depth) (p : List Nat) where
  table : Table base
  frame : Frame m g depth p
  frozen : frame.snapshot = table.entries

theorem Certificate.input_published {m g depth base p} (c : @Certificate m g depth base p) {x}
    (used : x ∈ c.frame.step.inputs) : c.table.entries.lookup x.1 = some x.2 ∧
      p <+: x.1 ∧ p.length < x.1.length ∧ Published base c.table.entries x.1 x.2 := by
  obtain ⟨hit,below,deeper⟩ := c.frame.inputs x (c.frame.step_inputs ▸ used)
  rw [c.frozen] at hit
  exact ⟨hit,below,deeper,c.table.lookup_published hit⟩

theorem Certificate.assignment {m g depth base p} (c : @Certificate m g depth base p) {r}
    (read : c.frame.step.reading? = some r) :
    ∃ a n, c.frame.step.orders a n ∧ readback? g a = some r.actual ∧
      r.label = some (if n % 2 = 0 then .chiral r.actual else .pseudoasymmetric (pseudoRSOfRS r.actual)) :=
  c.frame.step.chemical_letter read

theorem Certificate.refusal {m g depth base p} (c : @Certificate m g depth base p) :
    c.frame.step.reading? = none ↔ c.frame.step.refuses := c.frame.step.reading?_eq_none_iff

/-- Use one molecular cache and a deepest-first table across all branches of
the original root. Missing source computations leave a site unpublished.
A parent succeeds only if its molecular frame really uses available entries. -/
def tableAtRoot {m g depth} (base : Cache m g depth) (root : Nat) : Option (Table base) := do
  let focus ← occurrence? m [root]
  let paths := (RingAuxiliaryInventory.promotionPaths m focus).eraseDups.filter fun q =>
    decide ([root] <+: q ∧ 1 < q.length)
  let ordered := paths.mergeSort fun p q => decide (q.length ≤ p.length)
  let empty : Table base := ⟨[],by simp,by simp⟩
  return ordered.foldl publish empty

def checkWith? {m g depth} (base : Cache m g depth) (root : Nat) : Option (Certificate base [root]) := do
  let t ← tableAtRoot base root
  let f ← frame? m g depth [root] t.entries
  if same : f.snapshot = t.entries then return ⟨t,f,same⟩
  none

def check? (m : RawMolecule) (g : Geometry) (depth root : Nat) :=
  checkWith? (RecursiveSigned.cacheAtRoot m g depth root) root

end TetraStereo.Engine.RingChemicalPriority.FrozenSigned

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.FrozenSigned.Certificate.input_published
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.FrozenSigned.Certificate.assignment
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.FrozenSigned.Certificate.refusal
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.FrozenSigned.check?

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.FrozenSigned.Table.agrees_cached
