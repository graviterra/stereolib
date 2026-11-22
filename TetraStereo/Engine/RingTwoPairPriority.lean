import TetraStereo.Engine.RingTwoPairConstruction

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority
open OneCenter LocalizedGenericMarkedRecalculation Recursive

private def cross? {m p omitted} (e : Experiment m p omitted) (a b : Arm m e.focus omitted) : Option (Cross e a b) := do
  let earlier ← EarlierStereoMatch.check? m p a.ligand b.ligand .five (armEntries a) (armEntries b)
  let ⟨x,hx⟩ ← a.start.attach
  let ⟨y,hy⟩ ← b.start.attach
  let ⟨wins,actual⟩ ← (molecularSeniorLeft? m x y .five a.facts b.facts false).attach
  if reflected : molecularSeniorLeft? m x y .five a.facts b.facts true = some (!wins) then
    return ⟨earlier,x,y,hx,hy,wins,actual,reflected⟩
  none

private def markedOrder? {m p omitted} (e : Experiment m p omitted) (a b : Arm m e.focus omitted) (k : Nat) :
    Option (MarkedOrder e a b) := do
  let ⟨l,hl⟩ ← ((a.observe p e.depth (some k)).bind Prod.snd).attach
  let ⟨r,hr⟩ ← ((b.observe p e.depth (some k)).bind Prod.snd).attach
  if same : l.constitution = r.constitution ∧ l.before = r.before then
    let ⟨o,checked⟩ ← (compare? l r).attach
    if strict : o ≠ .eq then return ⟨k,l,r,hl,hr,same,o,strict,checked⟩
  none

private def row? {m p omitted} (e : Experiment m p omitted) (a b : {a // a ∈ e.arms}) : Option (Row e) := do
  if let some same := markedTie? e none a.val b.val then
    let ks := e.arms.map Arm.ligand
    let trials ← ks.mapM (markedOrder? e a.val b.val)
    if allMarks : trials.map MarkedOrder.mark = ks then
      return ⟨a.val,b.val,a.property,b.property,.within same trials allMarks⟩
    none
  else return ⟨a.val,b.val,a.property,b.property,.cross (← cross? e a.val b.val)⟩

private def matrix? {m p omitted} (e : Experiment m p omitted) : Option (Matrix e) := do
  let rows ← (directedPairs e.arms.attach (fun a => a.val.ligand)).mapM fun (a,b) => row? e a b
  if cover : rows.map Row.address = directedPairs (e.arms.map Arm.ligand) id then
    return ⟨rows,cover⟩
  none

private def partition? {m p omitted} {e : Experiment m p omitted} (mat : Matrix e) : Option (Partition mat) := do
  let ids := e.arms.map Arm.ligand
  let ⟨order,permuted⟩ ← (ids.permutations'.find? mat.partitionOK).attach
  return ⟨order,List.mem_permutations'.mp (List.mem_of_find?_eq_some permuted),List.find?_some (p := mat.partitionOK) permuted⟩

/-- The molecular comparisons and the resulting two-pair partition, prior
to the geometric readback or the choice of an aggregation policy. -/
structure Classified {m p omitted} (e : Experiment m p omitted) where
  constitution : List (List Nat)
  allTied : ∀ a ∈ e.arms, a.start.isSome = true ∧ ligandRows? m p a.ligand e.depth = some constitution
  uniqueFacts : (e.positiveFacts.map Prod.fst).Nodup
  matrix : Matrix e
  partition : Partition matrix

def classify? {m p omitted} (e : Experiment m p omitted) : Option (Classified e) := do
  let first ← e.arms.head?
  let constitution ← ligandRows? m p first.ligand e.depth
  if allTied : ∀ a ∈ e.arms, a.start.isSome = true ∧ ligandRows? m p a.ligand e.depth = some constitution then
    if unique : (e.positiveFacts.map Prod.fst).Nodup then
      let mat ← matrix? e
      return ⟨constitution,allTied,unique,mat,← partition? mat⟩
  none

def Classified.certificate? {m p omitted} {e : Experiment m p omitted}
    (c : Classified e) (g : Geometry) : Option (Certificate e g) := do
  let ts := c.partition.trials
  let t ← ts.head?
  let r ← geometric g t.actual t.reflected
  if agree : ∀ t ∈ ts, geometric g t.actual t.reflected = some r then
    return ⟨c.constitution,c.allTied,c.uniqueFacts,c.matrix,c.partition,ts,c.partition.marks,r,agree⟩
  none

def certify? {m p omitted} (e : Experiment m p omitted) (g : Geometry) : Option (Certificate e g) := do
  (← classify? e).certificate? g

structure Step (m : RawMolecule) (g : Geometry) (p : List Nat) where
  prepared : Prepared m g p
  certificate : Certificate prepared.experiment g

def Step.reading {m g p} (s : Step m g p) := s.certificate.reading
def Step.required {m g p} (s : Step m g p) := signedEntries s.prepared.experiment.positiveFacts
def Step.trials {m g p} (s : Step m g p) := s.certificate.trials

def check? {m g p} (prep : Prepared m g p) : Option (Step m g p) := do
  return ⟨prep,← certify? prep.experiment g⟩

theorem Step.justified {m g p} (s : Step m g p) : Justified m g p s.reading :=
  .pairedPromotion ⟨s.prepared.experiment,s.certificate⟩ s.prepared.children

private theorem exchange_readback (g : Geometry) {actual reflected : List Nat}
    (exchange : swapBlocks? actual = some reflected) :
    readback? g reflected = readback? g actual := by
  unfold swapBlocks? at exchange
  split at exchange
  next a b c d =>
    obtain rfl := Option.some.inj exchange
    rw [LocalizedMarkedTerminalGaugeSwap.readback_swap24 g c b a d,
      LocalizedMarkedTerminalGaugeSwap.readback_swap13 g a b c d]
    cases readback? g [a,b,c,d] with
    | none => rfl
    | some h => cases h <;> rfl
  next => contradiction

theorem Trial.opposite_hands {m p omitted} {e : Experiment m p omitted} {mat : Matrix e} (t : Trial mat)
    (g : Geometry) {r : Reading} (observed : geometric g t.actual t.reflected = some r) :
    r.reflected = r.actual.swap := by
  unfold geometric at observed
  rw [readback_mirror,exchange_readback g t.swap] at observed
  cases h : readback? g t.actual with
  | none => simp [h] at observed
  | some k =>
    have same : (⟨k,k.swap⟩ : Reading) = r := by simpa [h] using observed
    cases same
    rfl

/-- For this two-pair class, the interclass Rule 5 reversal exchanges whole
pairs, while the same marked atom preserves both intraclass orders. Each
successful two-geometry assignment therefore has an uppercase letter. -/
theorem Certificate.uppercase {m g p omitted} {e : Experiment m p omitted} (s : Certificate e g) :
    s.reading.label = some (.chiral s.reading.actual) := by
  have opposite : s.reading.reflected = s.reading.actual.swap := by
    cases eqn : s.trials with
    | nil =>
      have sizes := congrArg List.length s.marks
      simp [eqn,e.four] at sizes
    | cons t ts =>
      exact t.opposite_hands g (s.unanimous t (by simp [eqn]))
  unfold Reading.label
  rw [opposite]
  cases s.reading.actual <;> rfl

theorem Step.uppercase {m g p} (s : Step m g p) :
    s.reading.label = some (.chiral s.reading.actual) := s.certificate.uppercase

/-- Every missing auxiliary used by this promotion has its own molecular proof.
The subproof may depend on positive and negative entries farther down the arms. -/
structure SignedStep (m : RawMolecule) (g : Geometry) (p : List Nat) where
  omitted : List (List Nat)
  experiment : Experiment m p omitted
  certificate : Certificate experiment g
  positive : ∀ a ∈ experiment.arms, ∀ x ∈ a.facts, Justified m g x.1 x.2
  negative : ∀ q ∈ omitted, ∃ es, Negative m q es ∧ es ⊆ required experiment
  unique : ((required experiment).map Prod.fst).Nodup

def SignedStep.reading {m g p} (s : SignedStep m g p) := s.certificate.reading

theorem SignedStep.justified {m g p} (s : SignedStep m g p) : Justified m g p s.reading :=
  .signedPairedPromotion ⟨s.experiment,s.certificate⟩ s.positive s.negative s.unique

theorem SignedStep.uppercase {m g p} (s : SignedStep m g p) :
    s.reading.label = some (.chiral s.reading.actual) := s.certificate.uppercase


end TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority.MarkedOrder.all_completions
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority.certify?
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority.check?
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority.Step.justified
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority.Step.uppercase
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority.SignedStep.justified
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority.SignedStep.uppercase
