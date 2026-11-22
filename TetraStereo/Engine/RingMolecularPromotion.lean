import TetraStereo.Engine.RingHierarchyLinearizations
import TetraStereo.Engine.RingRecursivePriorities
import TetraStereo.Engine.RingDiscoveredPriority
import TetraStereo.OneCenter.LocalizedChemicalRingPromotionAggregation

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority.Promotion
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation Recursive
open DeclarativeCIP.ProductionOccurrenceRules456 (PromotionOutcome promotionAggregate)

/-- Exact candidate addresses that still require positive auxiliary readings. -/
def positivePaths (omitted : List (List Nat)) (paths : Option (List (List Nat))) :=
  match omitted with
  | [] => paths
  | _ :: _ => paths.map (List.filter fun q => !omitted.contains q)

/-- The edge toward the original parent is kept on the original digraph.
We use it only when its constitutional prefix separates it from every other
ligand. Outward edges include terminal ring duplicates. -/
structure Arm (m : RawMolecule) (focus : RawMolecule.CanonicalBranchNode)
    (omitted : List (List Nat) := []) where
  ligand : Nat
  start : Option RawMolecule.CanonicalBranchNode
  bound : match start with
    | none => (canonicalOriginalParent? focus).map (·.atom) = some ligand
    | some n => n ∈ m.canonicalChildren focus ∧ n.atom = ligand
  facts : Facts
  complete : match start with
    | none => facts = []
    | some n => positivePaths omitted (carbonSites m (m.atomCount+1) n) = some (facts.map Prod.fst)

def collect {P : List Nat → Reading → Prop}
    (deriveAt : (p : List Nat) → Option {r // P p r}) :
    (paths : List (List Nat)) → Option {fs : Facts // fs.map Prod.fst = paths ∧ ∀ x ∈ fs, P x.1 x.2}
  | [] => some ⟨[], rfl, by simp⟩
  | p :: ps => do
    let ⟨r,h⟩ ← deriveAt p
    let ⟨rs,paths,valid⟩ ← collect deriveAt ps
    return ⟨(p,r) :: rs, by simp [paths], by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | tail
      · exact h
      · exact valid x tail⟩

def prepareArm? {P : List Nat → Reading → Prop} (m : RawMolecule)
    (focus : RawMolecule.CanonicalBranchNode)
    (deriveAt : (p : List Nat) → Option {r // P p r}) (i : Nat) :
    Option {a : Arm m focus // ∀ x ∈ a.facts, P x.1 x.2} := do
  if parent : (canonicalOriginalParent? focus).map (·.atom) = some i then
    return ⟨⟨i,none,parent,[],rfl⟩,by simp⟩
  let ⟨n,hn⟩ ← ((m.canonicalChildren focus).find? (fun n => n.atom == i)).attach
  let ⟨ps,hp⟩ ← (carbonSites m (m.atomCount+1) n).attach
  let ⟨fs,paths,valid⟩ ← collect deriveAt ps
  return ⟨⟨i,some n,⟨List.mem_of_find?_eq_some hn,by simpa using List.find?_some hn⟩,
    fs,paths.symm ▸ hp⟩,valid⟩

private def handTag : Option Reading → Nat
  | none => 0
  | some ⟨.R,.R⟩ => 1
  | some ⟨.R,.S⟩ => 2
  | some ⟨.S,.R⟩ => 3
  | some ⟨.S,.S⟩ => 4

/-- The promotion applies to every occurrence of the selected atom, including
a duplicate carrying that atom. Auxiliary lookup uses the whole path. -/
def marked (mark : Option Nat) (path : List Nat) : Bool :=
  mark.any fun atom => path.getLast? == some atom

def decorated (m : RawMolecule) (n : RawMolecule.CanonicalBranchNode) (fs : Facts) (mark : Option Nat) :=
  MarkedHierarchy.encode m (fun p => 2 * handTag (fs.lookup p) + (marked mark p).toNat)
    [] (m.atomCount+1) n

/-- Within a sphere, descendants of a constitutionally senior parent precede
descendants of a junior parent (P-92.1.5). At a tie of sibling atomic numbers
we stop refining that whole group's descendants. Their order remains free. -/
structure Site where
  path : List Nat
  atom : Nat
  level : Nat
  ancestry : List Nat
  deriving DecidableEq

def sites (m : RawMolecule) : Nat → RawMolecule.CanonicalBranchNode →
    Nat → List Nat → Bool → Option (List Site)
  | 0,_,_,_,_ => none
  | fuel+1,n,d,rank,fixed => do
    let children ← (m.canonicalChildren n).mapM fun c => do
      let a ← m.atoms[c.atom]?
      return (c,a.element.atomicNumber)
    let rest ← children.mapM fun (c,z) => do
      let solo := fixed && children.countP (fun e => e.2 == z) == 1
      sites m fuel c (d+1) (if fixed then rank ++ [z] else rank) solo
    return ⟨n.history.reverse,n.atom,d,rank⟩ :: rest.flatten

abbrev Group := Nat × List Nat

def groups (ss : List Site) : List Group :=
  ((ss.map fun s => (s.level,s.ancestry)).eraseDups).insertionSort fun (d,u) (e,v) =>
    decide (d < e ∨ (d = e ∧ v ≤ u))

/-- Independent precedence on two addresses. An earlier sphere is senior.
At equal distance, a higher atomic number at the first divergent sibling
fixes precedence for both descendants by the parent ranking rule. -/
def firstSenior (m : RawMolecule) : List Nat → List Nat → Bool
  | a :: as, b :: bs => if a = b then firstSenior m as bs else
      (m.atoms[a]?).any fun x => (m.atoms[b]?).any fun y =>
        x.element.atomicNumber > y.element.atomicNumber
  | _,_ => false

def forced (m : RawMolecule) (a b : Site) : Bool :=
  a.path.length < b.path.length ||
    (a.path.length == b.path.length && firstSenior m a.path b.path)

theorem forced_irrefl (m : RawMolecule) (a : Site) : forced m a a = false := by
  have self (p : List Nat) : firstSenior m p p = false := by induction p <;> simp_all [firstSenior]
  simp [forced,self]

/-- Any completion of the molecular priorities orders the same occurrences
and obeys the sphere rule and previously distinguished parent priorities. -/
def Legal (m : RawMolecule) (ss order : List Site) : Prop :=
  ss.Perm order ∧ order.Pairwise (fun a b => forced m b a ≠ true)

structure Layout (m : RawMolecule) (ss : List Site) where
  blocks : List (List Site)
  complete : blocks.flatten.Perm ss
  separated : blocks.Pairwise (fun l r => ∀ a ∈ l, ∀ b ∈ r, forced m a b = true)

/-- Certify the proposed block boundaries against the actual paths and
elements independently of the ancestry keys which proposed those boundaries. -/
def layout? (m : RawMolecule) (ss : List Site) : Option (Layout m ss) := do
  let blocks := (groups ss).map fun key => ss.filter (fun s => (s.level,s.ancestry) == key)
  if complete : blocks.flatten.Perm ss then
    if separated : blocks.Pairwise (fun l r => ∀ a ∈ l, ∀ b ∈ r, forced m a b = true) then
      return ⟨blocks,complete,separated⟩
  none

def Layout.read {m ss} (layout : Layout m ss) (mark : Nat) :=
  layout.blocks.map (List.map fun s => s.atom == mark)

theorem Layout.every_legal_order {m ss} (layout : Layout m ss) (order : List Site)
    (legal : Legal m ss order) (mark : Nat) :
    ∃ words, List.Forall₂ List.Perm (layout.read mark) words ∧
      words.flatten = order.map (fun s => s.atom == mark) := by
  obtain ⟨parts,perms,whole⟩ := Hierarchy.split_linearization
    (fun a b => forced m a b = true) (by simp [forced_irrefl]) layout.blocks order
    layout.separated (layout.complete.trans legal.1) legal.2
  refine ⟨parts.map (List.map fun s => s.atom == mark),?_,?_⟩
  · exact List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr
      (perms.imp fun _ _ h => h.map _))
  · simp [← whole,List.map_flatten]

private theorem word_shape {a b : PairSpheres.Layers} (h : List.Forall₂ List.Perm a b) :
    (PairSpheres.ranks b).map List.length = a.map List.length := by
  induction h with
  | nil => rfl
  | cons ab _ ih => simpa [PairSpheres.ranks] using And.intro ab.length_eq.symm ih

/-- A strict promotion compares the complete marked-atom words in every
ordering consistent with the molecular sphere and parent precedence rules. -/
theorem strict_in_legal_orders {m xs ys} (a : Layout m xs) (b : Layout m ys) (mark : Nat)
    (win : PairSpheres.seniorLeft? (a.read mark) (b.read mark) = some true)
    (l r : List Site) (left : Legal m xs l) (right : Legal m ys r) :
    r.map (fun s => (s.atom == mark).toNat) < l.map (fun s => (s.atom == mark).toNat) := by
  obtain ⟨ls,lh,leq⟩ := a.every_legal_order l left mark
  obtain ⟨rs,rh,req⟩ := b.every_legal_order r right mark
  have shape : (a.read mark).map List.length = (b.read mark).map List.length := by
    by_contra! different
    simp [PairSpheres.seniorLeft?,different] at win
  have lt := Hierarchy.flatten_strict ((word_shape rh).trans (shape.symm.trans (word_shape lh).symm))
    (PairSpheres.seniorLeft_sound win lh rh)
  simpa only [PairSpheres.ranks,← List.map_flatten,leq,req,List.map_map,Function.comp_def] using lt

structure Observation where
  constitution : List (List Nat)
  before : MarkedHierarchy.Code
  after : MarkedHierarchy.Code
  keys : List Group
  spheres : PairSpheres.Layers

def Arm.observe {m focus omitted} (a : Arm m focus omitted) (path : List Nat) (depth : Nat) (mark : Option Nat) :
    Option (List (List Nat) × Option Observation) := do
  let constitution ← ligandRows? m path a.ligand depth
  let some n := a.start | return (constitution,none)
  let before ← decorated m n a.facts none
  let ss ← sites m (m.atomCount+1) n 0 [] true
  let keys := groups ss
  let layout ← layout? m ss
  return (constitution,some ⟨constitution, before,
    ← (if mark.isNone then some before else decorated m n a.facts mark),keys,
    mark.elim [] layout.read⟩)

/-- An exact tie matches complete trees, including earlier labels and the
promoted bit. A strict Rule 6 decision must hold for every admissible ordering
within every constitutionally ordered block of each sphere. Different earlier trees with the same atomic
prefix require a separate derivation. -/
def compare? (a b : Observation) : Option Ordering := do
  if a.constitution < b.constitution then return .lt
  if b.constitution < a.constitution then return .gt
  guard (a.before == b.before)
  if a.after == b.after then return .eq
  guard (a.keys == b.keys)
  return if ← PairSpheres.seniorLeft? a.spheres b.spheres then .gt else .lt

theorem strict_promotion {a b : Observation} {side : Ordering}
    (prior : a.constitution = b.constitution) (decided : compare? a b = some side)
    (strict : side ≠ .eq) :
    a.before = b.before ∧ ∀ l r, List.Forall₂ List.Perm a.spheres l →
      List.Forall₂ List.Perm b.spheres r →
        ((side = .gt ∧ PairSpheres.ranks r < PairSpheres.ranks l) ∨
         (side = .lt ∧ PairSpheres.ranks l < PairSpheres.ranks r)) := by
  by_cases same : a.before = b.before <;> simp [compare?,prior,same] at decided
  by_cases h : a.after = b.after
  · simp [h] at decided
    exact (strict decided.symm).elim
  · simp [h] at decided
    by_cases keys : a.keys = b.keys <;> simp [keys] at decided
    cases e : PairSpheres.seniorLeft? a.spheres b.spheres with
    | none => simp [e] at decided
    | some s =>
      refine ⟨same,fun l r hl hr => ?_⟩
      have lt := PairSpheres.seniorLeft_sound e hl hr
      cases s <;> simp_all

theorem tie_exact (a b : Observation) : compare? a b = some .eq ↔
    a.constitution = b.constitution ∧ a.before = b.before ∧ a.after = b.after := by
  rcases lt_trichotomy a.constitution b.constitution with h | h | h
  · simp [compare?,h,ne_of_lt h]
  · by_cases ab : a.before = b.before <;> by_cases cd : a.after = b.after <;>
      by_cases keys : a.keys = b.keys <;> cases eq : PairSpheres.seniorLeft? a.spheres b.spheres <;> simp_all [compare?]
    split <;> decide
  · simp [compare?,h,not_lt_of_gt h,ne_of_gt h]

abbrev Table := List (Nat × (Nat × Ordering))

private abbrev ArmRow := List (List Nat) × Option Observation

private def decideArms? (i j : Nat) (a b : ArmRow) : Option Ordering := do
  if i = j then return .eq
  if a.1 < b.1 then return .lt
  if b.1 < a.1 then return .gt
  compare? (← a.2) (← b.2)

/-- Compute every ordered pair, including the comparisons needed to establish
the initial partition. A constitutional tie against the parent edge declines. -/
private def comparisons? (rows : List (Nat × ArmRow)) : Option Table := do
  let table ← rows.mapM fun (i,a) => rows.mapM fun (j,b) => do
    return (i,j,← decideArms? i j a b)
  return table.flatten

private def relation (t : Table) (i j : Nat) : Option Ordering :=
  (t.find? (fun e => e.1 == i && e.2.1 == j)).map (·.2.2)

def population (t : Table) (ligands : List Nat) : List Nat :=
  ligands.filter fun i => ligands.any fun j => i != j && relation t i j == some .eq

/-- Four tied candidates in a 2+2 or four-way partition, or three candidates
in a 3+1 partition. A lone equivalent pair does not enter this procedure. -/
def eligible (t : Table) (ligands : List Nat) : Option (List Nat) := do
  let marks := population t ligands
  guard (marks.length == 3 || marks.length == 4)
  return marks

structure Trial where
  mark : Nat
  table : Table
  order : List Nat
  unique : Bool
  deriving DecidableEq, Repr

private def trial? (ligands : List Nat) (mark : Nat) (t : Table) : Option Trial := do
  let precedes (i j : Nat) := relation t i j = some .gt ∨ relation t i j = some .eq
  let order := ligands.insertionSort precedes
  guard (decide (order.Pairwise precedes))
  return ⟨mark,t,order,decide (order.Pairwise (fun i j => relation t i j = some .gt))⟩

def Trial.outcome (g : Geometry) (t : Trial) : PromotionOutcome :=
  if t.unique then ((readback? g t.order).map PromotionOutcome.descriptor).getD .operationalFailure
  else .unresolved

def result (g : Geometry) (ts : List Trial) := promotionAggregate (ts.map (Trial.outcome g))

private def opposite : PromotionOutcome → PromotionOutcome
  | .descriptor h => .descriptor h.swap
  | .unresolved => .unresolved
  | .operationalFailure => .operationalFailure

private theorem outcome_mirror (g : Geometry) (t : Trial) :
    t.outcome (mirror g) = opposite (t.outcome g) := by
  cases h : readback? g t.order with
  | none => cases u : t.unique <;> simp [Trial.outcome,u,readback_mirror,h,opposite]
  | some r => cases r <;> cases u : t.unique <;> simp [Trial.outcome,u,readback_mirror,h,opposite]

private theorem balance_opposite (os : List PromotionOutcome) :
    DeclarativeCIP.ProductionOccurrenceRules456.promotionBalance (os.map opposite) =
      (DeclarativeCIP.ProductionOccurrenceRules456.promotionBalance os).map Neg.neg := by
  open DeclarativeCIP.ProductionOccurrenceRules456 in
    induction os with
    | nil => rfl
    | cons o os ih =>
      cases o with
      | operationalFailure => rfl
      | unresolved => exact ih
      | descriptor h =>
        cases h <;> simp only [List.map_cons,opposite,RS.swap,promotionBalance,ih]
        all_goals cases promotionBalance os <;> simp
        all_goals omega

/-- With a constitutionally separated partition and fully equal decorated
trees within each group, reflection preserves all marked priority orders.
It reverses every completed raw letter and preserves operational failure. -/
theorem result_mirror (g : Geometry) (ts : List Trial) :
    result (mirror g) ts = (result g ts).map (Option.map RS.swap) := by
  unfold result promotionAggregate
  have hm : ts.map (Trial.outcome (mirror g)) = (ts.map (Trial.outcome g)).map opposite := by
    rw [List.map_map]
    exact List.map_congr_left fun t _ => outcome_mirror g t
  rw [hm,balance_opposite]
  cases DeclarativeCIP.ProductionOccurrenceRules456.promotionBalance (ts.map (Trial.outcome g)) with
  | none => rfl
  | some n =>
    rcases lt_trichotomy n 0 with h | rfl | h
    · have hn : ¬ 0 < n := by omega
      simp [h,hn,RS.swap]
    · rfl
    · have hn : ¬ n < 0 := by omega
      simp [h,hn,RS.swap]

structure Experiment (m : RawMolecule) (path : List Nat) (omitted : List (List Nat) := []) where
  depth : Nat
  domain : saturatedWithHalogens m = true
  focus : RawMolecule.CanonicalBranchNode
  reached : occurrence? m path = some focus
  center : (m.atoms[focus.atom]?).any (fun a => a.element == .C) = true
  arms : List (Arm m focus omitted)
  incident : arms.map (·.ligand) = (occurrenceLigandCursors m focus).map (·.node.atom)
  four : arms.length = 4
  distinct : (arms.map (·.ligand)).Nodup

def Experiment.table? {m path} (e : Experiment m path) (mark : Option Nat) : Option Table := do
  let rows ← e.arms.mapM fun a => do return (a.ligand,← a.observe path e.depth mark)
  comparisons? rows

def Experiment.trials? {m path} (e : Experiment m path) : Option (List Trial) := do
  let ligands := e.arms.map (·.ligand)
  let before ← e.table? none
  let marks ← eligible before ligands
  marks.mapM fun mark => do trial? ligands mark (← e.table? (some mark))

/-- Every promoted order accounts for exactly the four incident ligands.
A completed nonunique order carries an actual equality between distinct
ligands; a strict order contains every directed strict comparison it uses. -/
def Trial.Valid (ligands : List Nat) (t : Trial) : Prop :=
  t.order.Perm ligands ∧
  t.order.Pairwise (fun i j => relation t.table i j = some .gt ∨ relation t.table i j = some .eq) ∧
  (t.unique = true ↔ t.order.Pairwise (fun i j => relation t.table i j = some .gt))

private theorem trial_spec {ligands i tab t} (ok : trial? ligands i tab = some t) :
    t.mark = i ∧ t.table = tab ∧ t.Valid ligands := by
  let le (i j : Nat) := relation tab i j = some .gt ∨ relation tab i j = some .eq
  let sorted := ligands.insertionSort le
  by_cases h : sorted.Pairwise le
  · have ht : (⟨i,tab,sorted,decide (sorted.Pairwise (fun i j => relation tab i j = some .gt))⟩ : Trial) = t := by
      change (guard (decide (sorted.Pairwise le)) >>= _) = some t at ok
      simpa [h] using ok
    subst t
    exact ⟨rfl,rfl,List.perm_insertionSort _ _,h,by simp⟩
  · have invalid : trial? ligands i tab = none := by
      unfold trial?
      change (guard (decide (sorted.Pairwise le)) >>= _) = none
      simp [h]
    simp [invalid] at ok

private theorem traverse_exact {α β : Type} (f : α → Option β) {xs : List α} {ys : List β}
    (ok : xs.mapM f = some ys) : List.Forall₂ (fun x y => f x = some y) xs ys := by
  induction xs generalizing ys with
  | nil =>
    simp at ok
    subst ys
    exact .nil
  | cons x xs ih =>
    cases hx : f x with
    | none => simp [List.mapM_cons,hx] at ok
    | some y =>
      cases ht : xs.mapM f with
      | none => simp [List.mapM_cons,hx,ht] at ok
      | some tail =>
        simp [List.mapM_cons,hx,ht] at ok
        exact ok ▸ List.Forall₂.cons hx (ih ht)

theorem Experiment.all_promotions {m p} (e : Experiment m p) {ts}
    (ok : e.trials? = some ts) :
    ∃ before, e.table? none = some before ∧
    List.Forall₂ (fun mark t => t.mark = mark ∧ e.table? (some mark) = some t.table ∧
      t.Valid (e.arms.map (·.ligand))) (population before (e.arms.map (·.ligand))) ts := by
  unfold Experiment.trials? at ok
  cases b : e.table? none with
  | none => simp [b] at ok
  | some before =>
    refine ⟨before,rfl,?_⟩
    let ligands := e.arms.map (·.ligand)
    let marks := population before ligands
    let f (mark : Nat) := (e.table? (some mark)).bind (trial? ligands mark)
    by_cases gate : marks.length = 3 ∨ marks.length = 4
    · have checked : marks.mapM f = some ts := by
        simpa [eligible,b,ligands,marks,f,gate,guard] using ok
      apply (traverse_exact f checked).imp
      intro mark t trial
      cases tab : e.table? (some mark) with
      | none => simp [f,tab] at trial
      | some value =>
        have h := trial_spec (by simpa [f,tab] using trial : trial? ligands mark value = some t)
        exact ⟨h.1,congrArg some h.2.1.symm,h.2.2⟩
    · have bad : eligible before ligands = none := by
        simpa [eligible,marks] using (show ¬ (marks.length = 3 ∨ marks.length = 4) from gate)
      change (e.table? none >>= fun t => eligible t ligands >>= fun ms => ms.mapM f) = some ts at ok
      simp [b,bad] at ok

/-- Directed comparison in the actual unmarked table. -/
def tableOrdering (t : Table) (i j : Nat) : Option Ordering := relation t i j

/-- Identify exactly the two equivalent carriers before reading class ranks. -/
def collapsePair (a b i : Nat) := if i = b then a else i

def classOrder (a b : Nat) (ranks : List Nat) (i j : Nat) : Ordering :=
  compare (ranks.idxOf (collapsePair a b j)) (ranks.idxOf (collapsePair a b i))

/-- This is the tag used by the actual unmarked molecular encoder. It
distinguishes absence and each of the four actual/reflected letter pairs. -/
def readingTag (fs : Facts) (p : List Nat) :=
  2 * handTag (fs.lookup p) + (marked none p).toNat

private def decodeHandTag : Nat → Option Reading
  | 1 => some ⟨.R,.R⟩
  | 2 => some ⟨.R,.S⟩
  | 3 => some ⟨.S,.R⟩
  | 4 => some ⟨.S,.S⟩
  | _ => none

private theorem decodeHandTag_exact (x : Option Reading) : decodeHandTag (handTag x) = x := by
  cases x with
  | none => rfl
  | some r =>
    rcases r with ⟨a,b⟩
    cases a <;> cases b <;> rfl

private theorem matched_readings {m : RawMolecule} {l r : Facts} {a b o}
    (left : MarkedHierarchy.observe? m (readingTag l) [] a = some o)
    (right : MarkedHierarchy.observe? m (readingTag r) [] b = some o) :
    l.lookup a.history.reverse = r.lookup b.history.reverse := by
  have tag_at {fs : Facts} {n : RawMolecule.CanonicalBranchNode}
      (h : MarkedHierarchy.observe? m (readingTag fs) [] n = some o) :
      readingTag fs n.history.reverse = o.unitClass := by
    have observed := congrArg (Option.map MarkedHierarchy.Observation.unitClass) h
    cases atom : m.atoms[n.atom]? <;> simp [MarkedHierarchy.observe?,atom] at observed
    exact observed
  have equal := (tag_at left).trans (tag_at right).symm
  change 2 * handTag (l.lookup a.history.reverse) = 2 * handTag (r.lookup b.history.reverse) at equal
  have tags : handTag (l.lookup a.history.reverse) = handTag (r.lookup b.history.reverse) := by omega
  simpa only [decodeHandTag_exact] using congrArg decodeHandTag tags

/-- One common child matching preserves the earlier observations and both
geometry readings at every node of the complete actual outward trees. -/
def SameDecorations (m : RawMolecule) (l r : Facts) :
    Nat → RawMolecule.CanonicalBranchNode → RawMolecule.CanonicalBranchNode → Prop
  | 0,_,_ => False
  | d+1,a,b => ∃ o, MarkedHierarchy.observe? m (readingTag l) [] a = some o ∧
      MarkedHierarchy.observe? m (readingTag r) [] b = some o ∧
      l.lookup a.history.reverse = r.lookup b.history.reverse ∧
      ∃ ordered, ordered.Perm (m.canonicalChildren b) ∧
        List.Forall₂ (SameDecorations m l r d) (m.canonicalChildren a) ordered

private theorem sameDecorations_of_iso {m l r d a b}
    (h : MarkedHierarchy.Isomorphic m m (readingTag l) (readingTag r) [] [] d a b) :
    SameDecorations m l r d a b := by
  induction d generalizing a b with
  | zero => contradiction
  | succ k ih =>
    obtain ⟨o,left,right,nodes,perm,children⟩ := h
    exact ⟨o,left,right,matched_readings left right,nodes,perm,
      children.imp fun _ _ same => ih same⟩

/-- Every one of the sixteen comparisons agrees with a strict total order
on three classes of the four actual carriers. Both elements of the unique
two-member class have complete outward decorated trees. -/
structure BareSinglePair (m : RawMolecule) (p : List Nat) where
  experiment : Experiment m p
  table : Table
  unmarked : experiment.table? none = some table
  left : Arm m experiment.focus
  right : Arm m experiment.focus
  leftMem : left ∈ experiment.arms
  rightMem : right ∈ experiment.arms
  distinct : left.ligand ≠ right.ligand
  populationPair : population table (experiment.arms.map (·.ligand)) = [left.ligand,right.ligand]
  classes : List Nat
  three : classes.length = 3
  representatives : classes.Perm
    (((experiment.arms.map (·.ligand)).map (collapsePair left.ligand right.ligand)).dedup)
  allPairs : ∀ i ∈ experiment.arms.map (·.ligand),
    ∀ j ∈ experiment.arms.map (·.ligand),
    tableOrdering table i j = some (classOrder left.ligand right.ligand classes i j)
  leftNode : RawMolecule.CanonicalBranchNode
  rightNode : RawMolecule.CanonicalBranchNode
  leftAt : left.start = some leftNode
  rightAt : right.start = some rightNode
  code : MarkedHierarchy.Code
  leftCode : decorated m leftNode left.facts none = some code
  rightCode : decorated m rightNode right.facts none = some code

/-- The attached equality transports any independently proved child facts
from the exact input experiment into the resulting certificate. -/
def bareAbsenceFor? {m p} (e : Experiment m p) :
    Option {c : BareSinglePair m p // c.experiment = e} := do
  let ligands := e.arms.map (·.ligand)
  let ⟨table,unmarked⟩ ← (e.table? none).attach
  let [i,j] := population table ligands | none
  let ⟨l,hl⟩ ← (e.arms.find? fun a => a.ligand == i).attach
  let ⟨r,hr⟩ ← (e.arms.find? fun a => a.ligand == j).attach
  if distinct : l.ligand ≠ r.ligand then
    if pair : population table ligands = [l.ligand,r.ligand] then
      let keys := (ligands.map (collapsePair l.ligand r.ligand)).dedup
      let senior (u v : Nat) := tableOrdering table u v = some .gt
      let cs := keys.insertionSort senior
      if agreement : ∀ u ∈ ligands, ∀ v ∈ ligands,
          tableOrdering table u v = some (classOrder l.ligand r.ligand cs u v) then
        if three : cs.length = 3 then
          let ⟨ln,la⟩ ← l.start.attach
          let ⟨rn,ra⟩ ← r.start.attach
          let ⟨c,lc⟩ ← (decorated m ln l.facts none).attach
          if rc : decorated m rn r.facts none = some c then
            return ⟨⟨e,table,unmarked,l,r,List.mem_of_find?_eq_some hl,
              List.mem_of_find?_eq_some hr,distinct,pair,cs,three,
              List.perm_insertionSort _ _,agreement,ln,rn,la,ra,c,lc,rc⟩,rfl⟩
  none

def bareAbsence? {m p} (e : Experiment m p) : Option (BareSinglePair m p) :=
  (bareAbsenceFor? e).map Subtype.val

theorem BareSinglePair.same_decorations {m p} (c : BareSinglePair m p) :
    SameDecorations m c.left.facts c.right.facts (m.atomCount+1) c.leftNode c.rightNode :=
  sameDecorations_of_iso (MarkedHierarchy.isomorphic_of_code c.leftCode c.rightCode)

/-- An independent reader can use the exact pair of geometry readings and
the entire earlier observation. Its combination of children must be invariant
under permutation. It then takes equal values on the two outward ligands. -/
theorem SameDecorations.observer_eq {α : Type} {m l r d a b}
    (same : SameDecorations m l r d a b)
    (readL readR : Nat → RawMolecule.CanonicalBranchNode → α)
    (combine : MarkedHierarchy.Observation → Option Reading → List α → α)
    (leftStep : ∀ n c o, MarkedHierarchy.observe? m (readingTag l) [] c = some o →
      readL (n+1) c = combine o (l.lookup c.history.reverse) ((m.canonicalChildren c).map (readL n)))
    (rightStep : ∀ n c o, MarkedHierarchy.observe? m (readingTag r) [] c = some o →
      readR (n+1) c = combine o (r.lookup c.history.reverse) ((m.canonicalChildren c).map (readR n)))
    (symmetric : ∀ o h {xs ys : List α}, xs.Perm ys → combine o h xs = combine o h ys) :
    readL d a = readR d b := by
  induction d generalizing a b with
  | zero => contradiction
  | succ n ih =>
    obtain ⟨o,lo,ro,hands,ordered,perm,children⟩ := same
    rw [leftStep n a o lo,rightStep n b o ro,hands]
    apply symmetric
    have matched : List.Forall₂ (fun u v => readL n u = readR n v)
        (m.canonicalChildren a) ordered := children.imp fun _ _ h => ih h
    have aligned : (m.canonicalChildren a).map (readL n) = ordered.map (readR n) := by
      have eqs : List.Forall₂ (· = ·) ((m.canonicalChildren a).map (readL n))
          (ordered.map (readR n)) :=
        List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr matched)
      simpa only [List.forall₂_eq_eq_eq] using eqs
    rw [aligned]
    exact perm.map (readR n)

/-- The two selected ligands and the diagonal are exactly the equal entries
of the molecular table. All other distinct carriers have different ranks. -/
theorem BareSinglePair.tie_iff {m p} (c : BareSinglePair m p) {i j : Nat}
    (hi : i ∈ c.experiment.arms.map (·.ligand)) (hj : j ∈ c.experiment.arms.map (·.ligand)) :
    tableOrdering c.table i j = some .eq ↔
      i = j ∨ (i = c.left.ligand ∧ j = c.right.ligand) ∨ (i = c.right.ligand ∧ j = c.left.ligand) := by
  have member : collapsePair c.left.ligand c.right.ligand j ∈ c.classes :=
    c.representatives.mem_iff.mpr (List.mem_dedup.mpr (List.mem_map_of_mem hj))
  rw [c.allPairs i hi j hj,Option.some.injEq,classOrder,Nat.compare_eq_eq,List.idxOf_inj member]
  unfold collapsePair
  split_ifs <;> grind

theorem BareSinglePair.tied_both_ways {m p} (c : BareSinglePair m p) :
    tableOrdering c.table c.left.ligand c.right.ligand = some .eq ∧
    tableOrdering c.table c.right.ligand c.left.ligand = some .eq := by
  have l := List.mem_map_of_mem (f := fun a : Arm m c.experiment.focus => a.ligand) c.leftMem
  have r := List.mem_map_of_mem (f := fun a : Arm m c.experiment.focus => a.ligand) c.rightMem
  constructor
  · simpa [classOrder,collapsePair,c.distinct] using c.allPairs _ l _ r
  · simpa [classOrder,collapsePair,c.distinct] using c.allPairs _ r _ l

private theorem pair_compared {α : Type} {R : α → α → Prop} {a b : α} (ne : a ≠ b)
    {xs : List α} (pw : xs.Pairwise R) (ha : a ∈ xs) (hb : b ∈ xs) : R a b ∨ R b a := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    obtain ⟨head,tail⟩ := List.pairwise_cons.mp pw
    rcases List.mem_cons.mp ha with ax | ax
    · subst x
      rcases List.mem_cons.mp hb with bx | bx
      · exact (ne bx.symm).elim
      · exact Or.inl (head _ bx)
    · rcases List.mem_cons.mp hb with bx | bx
      · subst x
        exact Or.inr (head _ ax)
      · exact ih tail ax bx

theorem BareSinglePair.no_strict_permutation {m p} (c : BareSinglePair m p)
    (order : List Nat) (perm : order.Perm (c.experiment.arms.map (·.ligand))) :
    ¬ order.Pairwise (fun i j => tableOrdering c.table i j = some .gt) := by
  intro strict
  have l := List.mem_map_of_mem (f := fun a : Arm m c.experiment.focus => a.ligand) c.leftMem
  have r := List.mem_map_of_mem (f := fun a : Arm m c.experiment.focus => a.ligand) c.rightMem
  obtain ab | ba := pair_compared c.distinct strict (perm.mem_iff.mpr l) (perm.mem_iff.mpr r)
  · simp [c.tied_both_ways.1] at ab
  · simp [c.tied_both_ways.2] at ba

theorem BareSinglePair.promotion_inapplicable {m p} (c : BareSinglePair m p) :
    c.experiment.trials? = none := by
  simp [Experiment.trials?,c.unmarked,eligible,c.populationPair,guard]

/-- Every signed occurrence used below a single-pair absence. -/
def BareSinglePair.required {m p} (c : BareSinglePair m p) : InventoryPriority.Entries :=
  c.experiment.arms.flatMap fun a => a.facts.map fun x => (x.1,some x.2)

/-- The parent relation and the signed occurrence inventory are fixed across
all promotions. The selected atom marks every copy of its original index. -/
def promotionObservation? (m : RawMolecule) (p : List Nat) (facts : Facts) (mark : Option Nat)
    (c : CanonicalRerootCursor) : Option (IsotopePriority.FullObservation × Option Reading × Bool) := do
  let observation ← IsotopePriority.fullObservation? m p c
  let address := c.node.history.reverse
  return (observation,facts.lookup address,mark.any (· == c.node.atom))

def Experiment.positiveFacts {m p omitted} (e : Experiment m p omitted) := e.arms.flatMap (·.facts)

/-- A single correspondence matches the full constitution, duplicate
origins, actual and reflected auxiliary hands, and the promoted-atom bit.
Both matched arms lead out from the same addressed focus. -/
structure MarkedTie {m p omitted} (e : Experiment m p omitted) (mark : Option Nat) (a b : Arm m e.focus omitted) where
  left : RawMolecule.CanonicalBranchNode
  right : RawMolecule.CanonicalBranchNode
  leftAt : a.start = some left
  rightAt : b.start = some right
  incident : (⟨left,some e.focus⟩ : CanonicalRerootCursor) ∈ occurrenceLigandCursors m e.focus ∧
    (⟨right,some e.focus⟩ : CanonicalRerootCursor) ∈ occurrenceLigandCursors m e.focus
  matched : IsotopePriority.TreesMatch m (promotionObservation? m p e.positiveFacts mark)
    (IsotopePriority.budget m+1) ⟨left,some e.focus⟩ ⟨right,some e.focus⟩

def markedTie? {m p omitted} (e : Experiment m p omitted) (mark : Option Nat) (a b : Arm m e.focus omitted) :
    Option (MarkedTie e mark a b) := do
  let ⟨x,hx⟩ ← a.start.attach
  let ⟨y,hy⟩ ← b.start.attach
  let cx : CanonicalRerootCursor := ⟨x,some e.focus⟩
  let cy : CanonicalRerootCursor := ⟨y,some e.focus⟩
  if incident : cx ∈ occurrenceLigandCursors m e.focus ∧ cy ∈ occurrenceLigandCursors m e.focus then
    if same : IsotopePriority.treesMatch m (promotionObservation? m p e.positiveFacts mark)
        (IsotopePriority.budget m+1) cx cy = true then
      return ⟨x,y,hx,hy,incident,IsotopePriority.treesMatch_sound same⟩
  none

/-- A distinct pair in the unmarked table must exhibit either a strict
Rule 1a prefix difference or full unmarked tree equivalence. -/
def baselineOK {m p} (e : Experiment m p) (table : Table) (a b : Arm m e.focus) : Bool :=
  if a.ligand = b.ligand then tableOrdering table a.ligand b.ligand == some .eq else
  ((ligandRows? m p a.ligand e.depth).any fun x => (ligandRows? m p b.ligand e.depth).any fun y =>
    if x < y then tableOrdering table a.ligand b.ligand == some .lt else
    if y < x then tableOrdering table a.ligand b.ligand == some .gt else
      tableOrdering table a.ligand b.ligand == some .eq && (markedTie? e none a b).isSome)

structure PersistentPair {m p} (e : Experiment m p) (t : Trial) where
  left : Arm m e.focus
  right : Arm m e.focus
  leftMem : left ∈ e.arms
  rightMem : right ∈ e.arms
  distinct : left.ligand ≠ right.ligand
  forward : tableOrdering t.table left.ligand right.ligand = some .eq
  backward : tableOrdering t.table right.ligand left.ligand = some .eq
  same : MarkedTie e (some t.mark) left right

private def persistent? {m p} (e : Experiment m p) (t : Trial) : Option (PersistentPair e t) :=
  e.arms.attach.findSome? fun a => e.arms.attach.findSome? fun b => do
    if different : a.val.ligand ≠ b.val.ligand then
      if tied : tableOrdering t.table a.val.ligand b.val.ligand = some .eq ∧
          tableOrdering t.table b.val.ligand a.val.ligand = some .eq then
        return ⟨a.val,b.val,a.property,b.property,different,tied.1,tied.2,
          ← markedTie? e (some t.mark) a.val b.val⟩
    none

theorem PersistentPair.no_strict_permutation {m p} {e : Experiment m p} {t}
    (pair : PersistentPair e t) (order : List Nat) (perm : order.Perm (e.arms.map (·.ligand))) :
    ¬ order.Pairwise (fun i j => tableOrdering t.table i j = some .gt) := by
  intro strict
  have l := List.mem_map_of_mem (f := fun a : Arm m e.focus => a.ligand) pair.leftMem
  have r := List.mem_map_of_mem (f := fun a : Arm m e.focus => a.ligand) pair.rightMem
  obtain ab | ba := pair_compared pair.distinct strict (perm.mem_iff.mpr l) (perm.mem_iff.mpr r)
  · simp [pair.forward] at ab
  · simp [pair.backward] at ba

structure StructuralRefusal (m : RawMolecule) (p : List Nat) where
  experiment : Experiment m p
  uniqueFacts : (experiment.positiveFacts.map Prod.fst).Nodup
  table : Table
  unmarked : experiment.table? none = some table
  completeBaseline : ∀ a ∈ experiment.arms, ∀ b ∈ experiment.arms, baselineOK experiment table a b = true
  trials : List Trial
  allTrials : experiment.trials? = some trials
  nonempty : trials ≠ []
  nonunique : ∀ t ∈ trials, t.unique = false
  survives : ∀ t ∈ trials, Nonempty (PersistentPair experiment t)

def structuralRefusal? {m p} (e : Experiment m p) (ts : List Trial) (done : e.trials? = some ts) :
    Option {c : StructuralRefusal m p // c.experiment = e} := do
  if trials : ts ≠ [] ∧ ∀ t ∈ ts, t.unique = false then
    if unique : (e.positiveFacts.map Prod.fst).Nodup then
      let ⟨table,found⟩ ← (e.table? none).attach
      if baseline : ∀ a ∈ e.arms, ∀ b ∈ e.arms, baselineOK e table a b = true then
        if pairs : ∀ t ∈ ts, (persistent? e t).isSome = true then
          return ⟨⟨e,unique,table,found,baseline,ts,done,trials.1,trials.2,
            fun t ht => ⟨(persistent? e t).get (pairs t ht)⟩⟩,rfl⟩
  none

def StructuralRefusal.required {m p} (c : StructuralRefusal m p) : InventoryPriority.Entries :=
  c.experiment.positiveFacts.map fun x => (x.1,some x.2)

theorem StructuralRefusal.outcomes {m p} (c : StructuralRefusal m p) (g : Geometry) :
    ∀ t ∈ c.trials, t.outcome g = .unresolved := by
  intro t ht
  simp [Trial.outcome,c.nonunique t ht]

/-- A finite derivation discharges every absence used in the two matched
ligands. The child's observations must agree with the enclosing inventory
at the same paths. Positive readings receive their geometry proofs when
this structural derivation is used. -/
inductive Negative (m : RawMolecule) : List Nat → InventoryPriority.Entries → Prop where
  | single {p} (c : BareSinglePair m p) : Negative m p c.required
  | promotionTie {p} (c : StructuralRefusal m p) : Negative m p c.required
  | branch {p} (c : SignedPair.Pair m p)
      (sub : (q : List Nat) → (q,none) ∈ c.required → InventoryPriority.Entries)
      (descendants : ∀ q h, Negative m q (sub q h))
      (compatible : ∀ q h, sub q h ⊆ c.required) : Negative m p c.required

theorem Negative.signed {m p} (c : SignedPair.Pair m p)
    (children : ∀ q, (q,none) ∈ c.required → ∃ es, Negative m q es ∧ es ⊆ c.required) :
    Negative m p c.required :=
  .branch c (fun q h => (children q h).choose)
    (fun q h => (children q h).choose_spec.1) (fun q h => (children q h).choose_spec.2)

theorem Negative.descend {m p es q} (h : Negative m p es) (atPath : (q,none) ∈ es) :
    ∃ sub, Negative m q sub ∧ sub ⊆ es := by
  cases h with
  | single c => simp [BareSinglePair.required] at atPath
  | promotionTie c => simp [StructuralRefusal.required] at atPath
  | branch c sub children compatible => exact ⟨_,children q atPath,compatible q atPath⟩

namespace TwoPairPriority

def signedEntries (fs : Facts) : InventoryPriority.Entries := fs.map fun x => (x.1,some x.2)

/-- Preserve signed absences on this arm at their full outward addresses.
The independent earlier-rule checker verifies exact candidate coverage. -/
def armEntries {m focus omitted} (a : Arm m focus omitted) : InventoryPriority.Entries :=
  signedEntries a.facts ++ (omitted.filter fun q => a.start.any (fun n => n.history.reverse <+: q)).map (·,none)

def required {m p omitted} (e : Experiment m p omitted) : InventoryPriority.Entries :=
  signedEntries e.positiveFacts ++ omitted.map (·,none)

structure Cross {m p omitted} (e : Experiment m p omitted) (a b : Arm m e.focus omitted) where
  earlier : EarlierStereoMatch.Decision m p a.ligand b.ligand .five (armEntries a) (armEntries b)
  left : RawMolecule.CanonicalBranchNode
  right : RawMolecule.CanonicalBranchNode
  leftAt : a.start = some left
  rightAt : b.start = some right
  wins : Bool
  actual : molecularSeniorLeft? m left right .five a.facts b.facts false = some wins
  reflected : molecularSeniorLeft? m left right .five a.facts b.facts true = some (!wins)

/-- A promoted preference within a fully equivalent pair. It uses the same
marked atom on both complete arms, with the preceding observations fixed. -/
structure MarkedOrder {m p omitted} (e : Experiment m p omitted) (a b : Arm m e.focus omitted) where
  mark : Nat
  left : Observation
  right : Observation
  leftAt : (a.observe p e.depth (some mark)).bind Prod.snd = some left
  rightAt : (b.observe p e.depth (some mark)).bind Prod.snd = some right
  same : left.constitution = right.constitution ∧ left.before = right.before
  ordering : Ordering
  different : ordering ≠ .eq
  checked : compare? left right = some ordering

theorem MarkedOrder.all_completions {m p omitted} {e : Experiment m p omitted} {a b} (r : MarkedOrder e a b)
    (l v) (hl : List.Forall₂ List.Perm r.left.spheres l) (hr : List.Forall₂ List.Perm r.right.spheres v) :
    (r.ordering = .gt ∧ PairSpheres.ranks v < PairSpheres.ranks l) ∨
    (r.ordering = .lt ∧ PairSpheres.ranks l < PairSpheres.ranks v) :=
  (strict_promotion r.same.1 r.checked r.different).2 l v hl hr

inductive PairBasis {m p omitted} (e : Experiment m p omitted) (a b : Arm m e.focus omitted) where
  | within (tied : MarkedTie e none a b) (trials : List (MarkedOrder e a b))
      (allMarks : trials.map MarkedOrder.mark = e.arms.map Arm.ligand)
  | cross (decision : Cross e a b)

structure Row {m p omitted} (e : Experiment m p omitted) where
  left : Arm m e.focus omitted
  right : Arm m e.focus omitted
  leftMem : left ∈ e.arms
  rightMem : right ∈ e.arms
  directed : PairBasis e left right

def Row.address {m p omitted} {e : Experiment m p omitted} (r : Row e) := (r.left.ligand,r.right.ligand)

def Row.unmarked {m p omitted} {e : Experiment m p omitted} (r : Row e) : Ordering :=
  match r.directed with
  | .within .. => .eq
  | .cross c => if c.wins then .gt else .lt

def Row.ordering? {m p omitted} {e : Experiment m p omitted} (r : Row e) (mark : Nat) (rev : Bool) :
    Option Ordering :=
  match r.directed with
  | .within _ ts _ => (ts.find? (fun t => t.mark == mark)).map MarkedOrder.ordering
  | .cross c => some (if (if rev then !c.wins else c.wins) then .gt else .lt)

def directedPairs {α : Type} (xs : List α) (key : α → Nat) : List (α × α) :=
  xs.flatMap fun a => (xs.filter (fun b => key a != key b)).map (a,·)

structure Matrix {m p omitted} (e : Experiment m p omitted) where
  rows : List (Row e)
  covered : rows.map Row.address = directedPairs (e.arms.map Arm.ligand) id

def Matrix.row? {m p omitted} {e : Experiment m p omitted} (mat : Matrix e) (i j : Nat) :=
  mat.rows.find? fun r => r.address == (i,j)

def Matrix.partitionOK {m p omitted} {e : Experiment m p omitted} (mat : Matrix e) (order : List Nat) : Bool :=
  match order with
  | [a,b,c,d] =>
    let high := [a,b]
    let low := [c,d]
    let same (xs : List Nat) := (directedPairs xs id).all fun (i,j) =>
      ((mat.row? i j).map Row.unmarked) == some .eq
    same high && same low && high.all fun i => low.all fun j =>
      ((mat.row? i j).map Row.unmarked) == some .gt && ((mat.row? j i).map Row.unmarked) == some .lt
  | _ => false

/-- Both initial class memberships and both directions of the between-class
order are checked on all directed molecular comparisons. -/
structure Partition {m p omitted} {e : Experiment m p omitted} (mat : Matrix e) where
  order : List Nat
  incident : order.Perm (e.arms.map Arm.ligand)
  classes : mat.partitionOK order = true

def Matrix.strict {m p omitted} {e : Experiment m p omitted} (mat : Matrix e) (k : Nat) (rev : Bool)
    (i j : Nat) : Bool :=
  ((mat.row? i j).bind (·.ordering? k rev)) == some .gt &&
    ((mat.row? j i).bind (·.ordering? k rev)) == some .lt

def Matrix.orders {m p omitted} {e : Experiment m p omitted} (mat : Matrix e) (k : Nat) (rev : Bool) :=
  (e.arms.map Arm.ligand).permutations'.filter fun order =>
    decide (order.Pairwise (fun i j => mat.strict k rev i j = true))

/-- Moving the two senior ligands below the two junior ligands preserves
the order internal to each pair. -/
def swapBlocks? : List Nat → Option (List Nat)
  | [a,b,c,d] => some [c,d,a,b]
  | _ => none

structure Trial {m p omitted} {e : Experiment m p omitted} (mat : Matrix e) where
  mark : Nat
  actual : List Nat
  reflected : List Nat
  actualUnique : mat.orders mark false = [actual]
  reflectedUnique : mat.orders mark true = [reflected]
  swap : swapBlocks? actual = some reflected

/-- All four independently selected atoms must give the same original
and reflected hand, with a unique strict order on each side. -/
structure Certificate {m p omitted} (e : Experiment m p omitted) (g : Geometry) where
  constitution : List (List Nat)
  allTied : ∀ a ∈ e.arms, a.start.isSome = true ∧ ligandRows? m p a.ligand e.depth = some constitution
  uniqueFacts : (e.positiveFacts.map Prod.fst).Nodup
  matrix : Matrix e
  partition : Partition matrix
  trials : List (Trial matrix)
  marks : trials.map Trial.mark = e.arms.map Arm.ligand
  reading : Reading
  unanimous : ∀ t ∈ trials, geometric g t.actual t.reflected = some reading

/-- The complete chemical and physical two-pair criterion before attaching
the recursive molecular proofs of its addressed auxiliary readings. -/
structure Basis (m : RawMolecule) (g : Geometry) (p : List Nat) (omitted : List (List Nat) := []) where
  experiment : Experiment m p omitted
  certificate : Certificate experiment g

end TwoPairPriority

/-- Chemical derivations may alternate between ordinary stereochemical rules
and Rule 6 at several addressed sites. Every child proof uses the original
molecular digraph and the same geometry. -/
inductive Justified (m : RawMolecule) (g : Geometry) : List Nat → Reading → Prop where
  | ordinary {p r} : Supported m g p r → Justified m g p r
  | stereo {p d f ls rs r} : (step? m g p d f ls rs).map Subtype.val = some r →
      (∀ x ∈ ls, Justified m g x.1 x.2) → (∀ x ∈ rs, Justified m g x.1 x.2) → Justified m g p r
  | promotion {p r ts} (e : Experiment m p) :
      (∀ a ∈ e.arms, ∀ x ∈ a.facts, Justified m g x.1 x.2) →
      e.trials? = some ts → result g ts = some (some r.actual) →
      result (mirror g) ts = some (some r.reflected) → Justified m g p r
  | inventory {p d f ls rs r} (step : InventoryPriority.Step m p d f ls rs)
      (missing : List (Sigma (fun q => BareSinglePair m q)))
      (coverage : (missing.map Sigma.fst).Perm
        ((ls ++ rs).filterMap (fun x => if x.2.isNone then some x.1 else none)))
      (positive : ∀ q v, (q,some v) ∈ ls ++ rs → Justified m g q v)
      (children : ∀ c ∈ missing, ∀ a ∈ c.2.experiment.arms, ∀ x ∈ a.facts, Justified m g x.1 x.2)
      (consistency : ∀ c ∈ missing, ∀ a ∈ c.2.experiment.arms, ∀ x ∈ a.facts,
        (x.1,some x.2) ∈ ls ++ rs)
      (read : geometric g (f.order step.orders.1) (f.order step.orders.2) = some r) :
      Justified m g p r
  | signedInventory {p d f ls rs r} (step : InventoryPriority.Step m p d f ls rs)
      (positive : ∀ q v, (q,some v) ∈ ls ++ rs → Justified m g q v)
      (negative : ∀ q, (q,none) ∈ ls ++ rs →
        ∃ es, Negative m q es ∧ es ⊆ ls ++ rs)
      (read : geometric g (f.order step.orders.1) (f.order step.orders.2) = some r) :
      Justified m g p r

  | discovered {p ls rs r} (s : DiscoveredPriority.Step m p ls rs)
      (positive : ∀ q v, (q,some v) ∈ ls ++ rs → Justified m g q v)
      (negative : ∀ q, (q,none) ∈ ls ++ rs → ∃ es, Negative m q es ∧ es ⊆ ls ++ rs)
      (read : geometric g s.actual.ligands s.reflected.ligands = some r) : Justified m g p r

  | pairedPromotion {p} (basis : TwoPairPriority.Basis m g p)
      (children : ∀ a ∈ basis.experiment.arms, ∀ x ∈ a.facts, Justified m g x.1 x.2) :
      Justified m g p basis.certificate.reading

  | signedPairedPromotion {p omitted} (basis : TwoPairPriority.Basis m g p omitted)
      (children : ∀ a ∈ basis.experiment.arms, ∀ x ∈ a.facts, Justified m g x.1 x.2)
      (negative : ∀ q ∈ omitted, ∃ es, Negative m q es ∧ es ⊆ TwoPairPriority.required basis.experiment)
      (unique : ((TwoPairPriority.required basis.experiment).map Prod.fst).Nodup) :
      Justified m g p basis.certificate.reading

/-- Each nested negative inherits independent geometry proofs for every
positive reading used anywhere below it, with the same occurrence addresses. -/
theorem supported_negative_child {m : RawMolecule} {g : Geometry} {p es q}
    (negative : Negative m p es)
    (positive : ∀ z v, (z,some v) ∈ es → Justified m g z v)
    (child : (q,none) ∈ es) :
    ∃ sub, Negative m q sub ∧ sub ⊆ es ∧
      ∀ z v, (z,some v) ∈ sub → Justified m g z v := by
  obtain ⟨sub,valid,within⟩ := negative.descend child
  exact ⟨sub,valid,within,fun z v member => positive z v (within member)⟩


structure Checked (m : RawMolecule) (g : Geometry) (path : List Nat) where
  experiment : Experiment m path
  children : ∀ a ∈ experiment.arms, ∀ x ∈ a.facts, Justified m g x.1 x.2
  trials : List Trial
  allTrials : experiment.trials? = some trials
  actual : Option RS
  reflected : Option RS
  actualResult : result g trials = some actual
  reflectedResult : result (mirror g) trials = some reflected

def Checked.label {m g path} (c : Checked m g path) := caseFromMirror? c.actual c.reflected

theorem Checked.uppercase_or_refusal {m g root} (c : Checked m g root) :
    c.label = c.actual.map (.chiral ·) := by
  have h := result_mirror g c.trials
  rw [c.actualResult,c.reflectedResult] at h
  have reflected := Option.some.inj h
  unfold Checked.label
  rw [reflected]
  cases c.actual with
  | none => rfl
  | some a => cases a <;> rfl

/-- The complete unmarked experiment and the molecular derivations of every
positive auxiliary below the focus, before the Rule 6 eligibility test. -/
structure PreparedWith (m : RawMolecule) (path : List Nat) (P : List Nat → Reading → Prop) where
  experiment : Experiment m path
  children : ∀ a ∈ experiment.arms, ∀ x ∈ a.facts, P x.1 x.2

def prepareWith? {P : List Nat → Reading → Prop} (m : RawMolecule) (path : List Nat) (depth : Nat)
    (deriveAt : (p : List Nat) → Option {r // P p r}) : Option (PreparedWith m path P) := do
  if dom : saturatedWithHalogens m = true then
    let ⟨focus,found⟩ ← (occurrence? m path).attach
    if carbon : (m.atoms[focus.atom]?).any (fun a => a.element == .C) = true then
      let ligands := (occurrenceLigandCursors m focus).map (·.node.atom)
      let certified ← ligands.mapM (prepareArm? m focus deriveAt)
      let arms := certified.map Subtype.val
      if inc : arms.map (·.ligand) = ligands then
        if four : arms.length = 4 then
          if distinct : (arms.map (·.ligand)).Nodup then
            let e : Experiment m path := ⟨depth,dom,focus,found,carbon,arms,inc,four,distinct⟩
            return ⟨e,by
              intro a ha
              obtain ⟨c,_,rfl⟩ := List.mem_map.mp ha
              exact c.property⟩
  none

abbrev Prepared (m : RawMolecule) (g : Geometry) (path : List Nat) :=
  PreparedWith m path (Justified m g)

def prepareAt? (m : RawMolecule) (g : Geometry) (path : List Nat) (depth : Nat)
    (deriveAt : (q : List Nat) → Option {r // Justified m g q r}) : Option (Prepared m g path) :=
  prepareWith? m path depth deriveAt

def checkAt? (m : RawMolecule) (g : Geometry) (path : List Nat) (depth : Nat)
    (deriveAt : (p : List Nat) → Option {r // Justified m g p r}) : Option (Checked m g path) := do
  let prepared ← prepareAt? m g path depth deriveAt
  let e := prepared.experiment
  let ⟨ts,ht⟩ ← e.trials?.attach
  let ⟨r,hr⟩ ← (result g ts).attach
  let ⟨s,hs⟩ ← (result (mirror g) ts).attach
  return ⟨e,prepared.children,ts,ht,r,s,hr,hs⟩

/-- Specialization of the structural certificate to recursively justified
children on the supplied geometry. -/
structure SinglePairAbsence (m : RawMolecule) (g : Geometry) (p : List Nat) extends BareSinglePair m p where
  children : ∀ a ∈ experiment.arms, ∀ x ∈ a.facts, Justified m g x.1 x.2

def singlePairAbsenceAt? (m : RawMolecule) (g : Geometry) (p : List Nat) (depth : Nat)
    (deriveAt : (q : List Nat) → Option {r // Justified m g q r}) : Option (SinglePairAbsence m g p) := do
  let prepared ← prepareAt? m g p depth deriveAt
  let ⟨bare,same⟩ ← bareAbsenceFor? prepared.experiment
  let justified (e : Experiment m p) := ∀ a ∈ e.arms, ∀ x ∈ a.facts, Justified m g x.1 x.2
  return ⟨bare,Eq.mpr (congrArg justified same) prepared.children⟩

theorem SinglePairAbsence.same_decorations {m g p} (c : SinglePairAbsence m g p) :
    SameDecorations m c.left.facts c.right.facts (m.atomCount+1) c.leftNode c.rightNode :=
  c.toBareSinglePair.same_decorations

theorem SinglePairAbsence.tied_both_ways {m g p} (c : SinglePairAbsence m g p) :
    tableOrdering c.table c.left.ligand c.right.ligand = some .eq ∧
    tableOrdering c.table c.right.ligand c.left.ligand = some .eq := c.toBareSinglePair.tied_both_ways

theorem SinglePairAbsence.no_strict_permutation {m g p} (c : SinglePairAbsence m g p)
    (order : List Nat) (perm : order.Perm (c.experiment.arms.map (·.ligand))) :
    ¬ order.Pairwise (fun i j => tableOrdering c.table i j = some .gt) :=
  c.toBareSinglePair.no_strict_permutation order perm

theorem SinglePairAbsence.promotion_inapplicable {m g p} (c : SinglePairAbsence m g p) :
    c.experiment.trials? = none := c.toBareSinglePair.promotion_inapplicable

/-- These positive readings remain available even though the local focus
has no strict order. Each still has its original molecular derivation. -/
def SinglePairAbsence.positiveFacts {m g p} (c : SinglePairAbsence m g p) : Facts :=
  c.experiment.arms.flatMap (·.facts)

theorem SinglePairAbsence.all_children {m g p} (c : SinglePairAbsence m g p)
    {x} (h : x ∈ c.positiveFacts) : Justified m g x.1 x.2 := by
  obtain ⟨a,ha,hx⟩ := List.mem_flatMap.mp h
  exact c.children a ha x hx

theorem SinglePairAbsence.outward_coverage {m g p} (c : SinglePairAbsence m g p)
    (a : Arm m c.experiment.focus) (_member : a ∈ c.experiment.arms) {n}
    (start : a.start = some n) : carbonSites m (m.atomCount+1) n = some (a.facts.map Prod.fst) := by
  cases a with
  | mk ligand origin bound facts complete =>
    cases origin with
    | none => cases start
    | some node =>
      cases start
      exact complete

def Checked.reading? {m g path} (c : Checked m g path) : Option {r // Justified m g path r} := do
  let ⟨a,ha⟩ ← c.actual.attach
  let ⟨b,hb⟩ ← c.reflected.attach
  return ⟨⟨a,b⟩,.promotion c.experiment c.children c.allTrials (ha ▸ c.actualResult) (hb ▸ c.reflectedResult)⟩

private def stereoAt? {m g} (path : List Nat) (depth : Nat) (f : Recursive.Frame)
    (deriveAt : (q : List Nat) → Option {r // Justified m g q r}) :
    Option {r // Justified m g path r} := do
  let ln ← occurrence? m (path ++ [f.left])
  let rn ← occurrence? m (path ++ [f.right])
  let ⟨ls,_,lh⟩ ← collect deriveAt (← carbonSites m (m.atomCount+1) ln)
  let ⟨rs,_,rh⟩ ← collect deriveAt (← carbonSites m (m.atomCount+1) rn)
  let ⟨r,checked⟩ ← ((step? m g path depth f ls rs).map Subtype.val).attach
  return ⟨r,.stereo checked lh rh⟩

/-- One finite recursion for auxiliary stereochemistry, including a further
promotion at a child. Only the local, unmarked child derivation is exported. -/
def deriveAt (m : RawMolecule) (g : Geometry) (hint : List Nat → Option Recursive.Frame)
    (radius : List Nat → Nat) : Nat → (p : List Nat) → Option {r // Justified m g p r}
  | 0,_ => none
  | fuel+1,p => do
    let d := radius p
    if let some ⟨order,supported⟩ := constitutionalOrder? m p d then
      let ⟨r,h⟩ ← (geometric g order order).attach
      return ⟨r,.ordinary (supported g r h)⟩
    let child := deriveAt m g hint radius fuel
    if let some f := hint p then
      if let some r := stereoAt? p d f child then return r
    (← checkAt? m g p d child).reading?

def analyze? (m : RawMolecule) (g : Geometry) (root depth fuel : Nat)
    (hint : List Nat → Option Recursive.Frame) (radius : List Nat → Nat) :=
  checkAt? m g [root] depth (deriveAt m g hint radius fuel)

end TetraStereo.Engine.RingChemicalPriority.Promotion
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.strict_promotion
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.tie_exact
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.analyze?
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.Checked.uppercase_or_refusal
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.Experiment.all_promotions
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.Layout.every_legal_order
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.singlePairAbsenceAt?
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.SinglePairAbsence.same_decorations
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.SameDecorations.observer_eq
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.SinglePairAbsence.tied_both_ways
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.SinglePairAbsence.no_strict_permutation
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.SinglePairAbsence.promotion_inapplicable
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.SinglePairAbsence.all_children
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.SinglePairAbsence.outward_coverage
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.prepareWith?
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.bareAbsence?
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.BareSinglePair.tie_iff
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.supported_negative_child
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.structuralRefusal?
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.PersistentPair.no_strict_permutation
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.StructuralRefusal.outcomes
