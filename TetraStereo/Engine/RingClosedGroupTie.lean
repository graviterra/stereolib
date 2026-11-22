import TetraStereo.Engine.RingClosedPairCasing

set_option autoImplicit false

namespace TetraStereo.Engine.RingClosedGroupTie
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site Arm)
open RingNestedActivePair (Reader Labels Frame)
open RingActivePairReport (Matrix Score Slot)
open RingClosedPairGroup (Group children projected upperAt FIFO seeded)
open RingActiveDistanceSchedule

/-- Both arms have a complete mixed first group. Their root lowercase
publications agree, and their outer constitutional comparison tied. -/
structure Certificate (i : Input) (f a b : Site i) (read : Reader i) where
  trace : List CIPRuleDecision
  earlier : RingRetainedChemicalTrace.compareAt? i f a b = some trace
  tie : cipTraceOutcome trace = .eq
  left : Group i ⟨a,some f⟩ read
  right : Group i ⟨b,some f⟩ read
  same : left.p = right.p

def edge? (i : Input) (f a b : Site i) (read : Reader i) : Option (Certificate i f a b read) := do
  let ⟨t,ht⟩ ← (RingRetainedChemicalTrace.compareAt? i f a b).attach
  if tie : cipTraceOutcome t = .eq then
    let l ← RingClosedPairGroup.group? i ⟨a,some f⟩ read
    let r ← RingClosedPairGroup.group? i ⟨b,some f⟩ read
    if eqn : l.p = r.p then return ⟨t,ht,tie,l,r,eqn⟩ else none
  else none

theorem Certificate.both_references {i f a b read} (c : Certificate i f a b read) (rev : Bool)
    {lr ls rr rs} (h₁ : FIFO i (seeded c.left rev .R) [⟨a,some f⟩] lr)
    (h₂ : FIFO i (seeded c.left rev .S) [⟨a,some f⟩] ls)
    (h₃ : FIFO i (seeded c.right rev .R) [⟨b,some f⟩] rr)
    (h₄ : FIFO i (seeded c.right rev .S) [⟨b,some f⟩] rs) :
    max (RingClosedPairGroup.word read rev .R lr) (RingClosedPairGroup.word read rev .S ls) =
      max (RingClosedPairGroup.word read rev .R rr) (RingClosedPairGroup.word read rev .S rs) := by
  simp only [RingClosedPairGroup.word,RingClosedPairGroup.accepted c.left h₁,
    RingClosedPairGroup.accepted c.left h₂,RingClosedPairGroup.accepted c.right h₃,
    RingClosedPairGroup.accepted c.right h₄]

def ordinal {i : Input} (read : Reader i) (rev : Bool) (q : Arm i) :=
  RingNestedActivePair.lower (((read q.occurrence).join).map fun p => if rev then p.2 else p.1)

private theorem silent_zero {i read q} (h : RingClosedPairGroup.silent i read q = true) (rev : Bool) :
    ordinal read rev q = 0 := by
  have found := beq_iff_eq.mp (Bool.and_eq_true_iff.mp h).2
  simp [ordinal,found,RingNestedActivePair.lower]

/-- All remaining ordinals vanish: both chiral children and all terminal
descendants. Even an arbitrary permutation of each whole sphere gives the
same Rule 4c word, so each source-permitted parent grouping gives this word. -/
theorem lower_word {i q read} (g : Group i q read) (rev : Bool) {row ends : List (Arm i)}
    (first : row.Perm (children i q)) (last : ends.Perm (children i g.pos ++ children i g.neg)) :
    [[ordinal read rev q],row.map (ordinal read rev),ends.map (ordinal read rev)] =
      [[RingNestedActivePair.lower (some (.pseudoasymmetric g.p))],[0,0,0],[0,0,0,0,0,0]] := by
  have root : ordinal read rev q = RingNestedActivePair.lower (some (.pseudoasymmetric g.p)) := by
    cases rev <;> simp [ordinal,g.rootRead,RingClosedPairGroup.lower]
  have kids := first.trans g.allChildren
  have one : row.map (ordinal read rev) = List.replicate 3 0 := by
    apply List.eq_replicate_iff.mpr
    refine ⟨by simpa using kids.length_eq,?_⟩
    intro x hx
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    have p := kids.mem_iff.mp hv
    simp only [List.mem_cons,List.not_mem_nil,or_false] at p
    rcases p with rfl | rfl | rfl
    · cases rev <;> simp [ordinal,g.posRead,RingClosedPairGroup.chiral,RingNestedActivePair.lower]
    · cases rev <;> simp [ordinal,g.negRead,RingClosedPairGroup.chiral,RingNestedActivePair.lower]
    · exact silent_zero g.leafSilent rev
  have all (v) (h : v ∈ [g.pos,g.neg]) := Bool.and_eq_true_iff.mp (List.all_eq_true.mp g.closed v h)
  have pos := all g.pos (by simp)
  have neg := all g.neg (by simp)
  have sizeP := beq_iff_eq.mp pos.1
  have sizeN := beq_iff_eq.mp neg.1
  have two : ends.map (ordinal read rev) = List.replicate 6 0 := by
    apply List.eq_replicate_iff.mpr
    refine ⟨by simpa [sizeP,sizeN] using last.length_eq,?_⟩
    intro x hx
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    have mem := List.mem_append.mp (last.mem_iff.mp hv)
    exact silent_zero (mem.elim (List.all_eq_true.mp pos.2 v) (List.all_eq_true.mp neg.2 v)) rev
  simp [root,one,two]

theorem Certificate.rule4c {i f a b read} (c : Certificate i f a b read) (rev : Bool)
    {l₁ l₂ r₁ r₂ : List (Arm i)} (la : l₁.Perm (children i ⟨a,some f⟩))
    (lb : l₂.Perm (children i c.left.pos ++ children i c.left.neg))
    (ra : r₁.Perm (children i ⟨b,some f⟩))
    (rb : r₂.Perm (children i c.right.pos ++ children i c.right.neg)) :
    [[ordinal read rev ⟨a,some f⟩],l₁.map (ordinal read rev),l₂.map (ordinal read rev)] =
    [[ordinal read rev ⟨b,some f⟩],r₁.map (ordinal read rev),r₂.map (ordinal read rev)] := by
  rw [lower_word c.left rev la lb,lower_word c.right rev ra rb,c.same]

/-- The actual ordered *descriptors*, including the opposite publication,
are recovered from the two pairing bits because the two possible hands
have different bits for either fixed reference. -/
theorem fixed_list {i q read} (g : Group i q read) {seed rev walk}
    (h : FIFO i (seeded g rev seed) [q] walk) :
    walk.filterMap (upperAt read rev) = [seed,seed.swap] := by
  let encode (hand : RS) := (hand == seed).toNat
  have injective : Function.Injective encode := by
    cases seed <;> intro a b <;> cases a <;> cases b <;> decide
  apply List.map_injective_iff.mpr injective
  exact (RingClosedPairGroup.accepted g h).trans (by cases seed <;> rfl)

def fixedSign {i : Input} (read : Reader i) (rev : Bool) (seed : RS) (a b : List (Arm i)) : Option Int :=
  RingSeededPairs.listSign? seed (a.map (upperAt read rev)) (b.map (upperAt read rev))

theorem fixed_zero {i x y read} (l : Group i x read) (r : Group i y read) {seed rev a b}
    (lh : FIFO i (seeded l rev seed) [x] a) (rh : FIFO i (seeded r rev seed) [y] b) :
    fixedSign read rev seed a b = some 0 := by
  simp only [fixedSign,RingSeededPairs.listSign?,List.filterMap_map,Function.id_comp,
    fixed_list l lh,fixed_list r rh]
  cases seed <;> rfl

/-- Rule 5 performs two separate fixed-seed comparisons after the full Rule
4c tie. Their combined magnitude is exactly zero for all four legal walks. -/
theorem Certificate.rule5 {i f a b read} (c : Certificate i f a b read) (rev : Bool)
    {lr ls rr rs} (h₁ : FIFO i (seeded c.left rev .R) [⟨a,some f⟩] lr)
    (h₂ : FIFO i (seeded c.left rev .S) [⟨a,some f⟩] ls)
    (h₃ : FIFO i (seeded c.right rev .R) [⟨b,some f⟩] rr)
    (h₄ : FIFO i (seeded c.right rev .S) [⟨b,some f⟩] rs) :
    fixedSign read rev .R lr rr = some 0 ∧ fixedSign read rev .S ls rs = some 0 ∧
      (do
        let direct ← fixedSign read rev .R lr rr
        let inverse ← fixedSign read rev .S ls rs
        return CentresRing.PairList.combine direct inverse) = some 0 := by
  rw [fixed_zero c.left c.right h₁ h₃,fixed_zero c.left c.right h₂ h₄]
  exact ⟨rfl,rfl,rfl⟩

/-- The inexpensive guard only examines the two current endpoint publications.
A candidate must still pass the complete group and constitutional witnesses. -/
def equalLower {i : Input} (read : Reader i) (a b : Site i) : Bool :=
  match read a,read b with
  | some (some (.pseudoasymmetric x,_)),some (some (.pseudoasymmetric y,_)) => x == y
  | _,_ => false

theorem Certificate.candidate {i f a b read} (c : Certificate i f a b read) : equalLower read a b = true := by
  have l := c.left.rootRead
  have r := c.right.rootRead
  change read a = _ at l
  change read b = _ at r
  simp [equalLower,l,r,RingClosedPairGroup.lower,c.same]

/-- Give an independently verified zero its exact value. Every candidate
failing that check is handed to the previous reader. -/
def score? (i : Input) (f a b : Site i) (read : Reader i) : Option Score :=
  if equalLower read a b then
    match edge? i f a b read with
    | some _ => some (0,0)
    | none => RingClosedPairGroup.score? i f a b read
  else RingClosedPairGroup.score? i f a b read

theorem issued {i f a b read v} (hit : score? i f a b read = some v) :
    RingClosedPairGroup.score? i f a b read = some v ∨
    (Nonempty (Certificate i f a b read) ∧ v = (0,0)) := by
  cases gate : equalLower read a b with
  | false => exact Or.inl (by simpa [score?,gate] using hit)
  | true =>
    cases found : edge? i f a b read with
    | none => exact Or.inl (by simpa [score?,gate,found] using hit)
    | some c =>
      exact Or.inr ⟨⟨c⟩,(Option.some.inj (by simpa [score?,gate,found] using hit) : (0,0) = v).symm⟩

theorem previous_on_miss {i f a b read} (miss : edge? i f a b read = none) :
    score? i f a b read = RingClosedPairGroup.score? i f a b read := by
  cases gate : equalLower read a b <;> simp [score?,gate,miss]

def source {i f} (fr : Frame i f) (read : Reader i) (a b : Slot) :=
  score? i f (fr.arm a).occurrence (fr.arm b).occurrence read

structure Refusal (i : Input) (f : Site i) (read : Reader i) where
  frame : Frame i f
  matrix : Matrix (source frame read)
  ordinary : RingOrdinaryPairRefusal.Certificate matrix

def refusal? (i : Input) (f : Site i) (read : Reader i) : Option (Refusal i f read) := do
  let fr ← RingNestedActivePair.frame? i f
  let m ← RingActivePairReport.matrix? (source fr read)
  return ⟨fr,m,← RingOrdinaryPairRefusal.find? m⟩

theorem Refusal.physical {i f read} (r : Refusal i f read) (rev : Bool) :
    ¬Nonempty (RingActivePairReport.Ranking r.matrix rev) ∧
    (RingChemicalPriority.ReferenceFrame.marks RingOrdinaryPairRefusal.ids
      (RingOrdinaryPairRefusal.table r.matrix rev)).length ∉ [3,4] :=
  ⟨r.ordinary.no_ranking rev,r.ordinary.no_promotion rev⟩

theorem Refusal.tied_source {i f read} (r : Refusal i f read) :
    source r.frame read r.ordinary.a r.ordinary.b = some (0,0) ∧
    source r.frame read r.ordinary.b r.ordinary.a = some (0,0) := r.ordinary.tied_source

def publish? (i : Input) (q : Site i) (s : View i) : Option (Option Labels) :=
  (RingClosedPairAssignment.publish? i q s).orElse fun _ =>
    (refusal? i q (RingNestedActivePair.masked q s)).map (fun _ => none)

private theorem publish_congr (i : Input) (q : Site i) {a b : View i}
    (agree : ∀ t, RingNestedActivePair.Eligible q t → a t = b t) :
    publish? i q a = publish? i q b := by
  have old : RingClosedPairAssignment.publish? i q a = RingClosedPairAssignment.publish? i q b := by
    unfold RingClosedPairAssignment.publish?
    rw [RingNestedActivePair.publish_congr i q agree,RingNestedActivePair.masked_congr q agree]
  unfold publish?
  rw [old,RingNestedActivePair.masked_congr q agree]

private def onRoot (i : Input) (root : i.certified.Atom) : Rule i := fun q s =>
  if q.val.root = root then publish? i q s else none

def atRoot (i : Input) (root : i.certified.Atom) := evaluate (onRoot i root)
def publicationTable (i : Input) (root : i.certified.Atom) : Table i :=
  table (onRoot i root) (height i+1)

theorem table_readback (i : Input) (root : i.certified.Atom) :
    snapshot (publicationTable i root) = atRoot i root := snapshot_table ..

theorem atRoot_eq {i : Input} {root : i.certified.Atom} {q : Site i} (on : q.val.root = root) :
    atRoot i root q = publish? i q (atRoot i root) := by
  change evaluate (onRoot i root) q = _
  rw [evaluate_eq]
  simp only [onRoot,on,if_true]
  apply publish_congr
  intro t vis
  simp [frozen,vis.1,vis.2.1,vis.2.2,distance,atRoot]

/-- A certified absence is either an already justified publication or an
issued ordinary refusal whose two geometries have no strict four-ligand ranking. -/
theorem atRoot_absence_iff {i : Input} {root : i.certified.Atom} {q : Site i} (on : q.val.root = root) :
    atRoot i root q = some none ↔
      RingClosedPairAssignment.publish? i q (atRoot i root) = some none ∨
      (RingClosedPairAssignment.publish? i q (atRoot i root) = none ∧
        (refusal? i q (RingNestedActivePair.masked q (atRoot i root))).isSome = true) := by
  conv_lhs => rw [atRoot_eq on]
  cases old : RingClosedPairAssignment.publish? i q (atRoot i root) with
  | some v => simp [publish?,old]
  | none =>
    cases h : refusal? i q (RingNestedActivePair.masked q (atRoot i root)) <;> simp [publish?,old,h]

inductive Derivation (i : Input) : Site i → Option Labels → Prop where
  | existing {q v} (s : View i) (issued : RingClosedPairAssignment.publish? i q s = some v)
      (deeper : ∀ t w, Visible q t → s t = some w → Derivation i t w) : Derivation i q v
  | refusal {q} (s : View i) (r : Refusal i q (RingNestedActivePair.masked q s))
      (issued : refusal? i q (RingNestedActivePair.masked q s) = some r)
      (deeper : ∀ t w, Visible q t → s t = some w → Derivation i t w) : Derivation i q none

theorem derivation {i : Input} {root : i.certified.Atom} (q : Site i)
    (on : q.val.root = root) {v} (found : atRoot i root q = some v) : Derivation i q v := by
  suffices done : ∀ n (q : Site i), height i - distance q = n → q.val.root = root →
      ∀ v, atRoot i root q = some v → Derivation i q v from done _ q rfl on _ found
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro q eqn on v hit
    have deeper (t : Site i) (w) (vis : Visible q t) (seen : atRoot i root t = some w) : Derivation i t w := by
      have upper := distance_bound t
      have lt := vis.2.1
      exact ih _ (by omega) t rfl (vis.1.trans on) w seen
    rw [atRoot_eq on] at hit
    cases old : RingClosedPairAssignment.publish? i q (atRoot i root) with
    | some val =>
      have eqv : val = v := Option.some.inj (by simpa [publish?,old] using hit)
      exact eqv ▸ Derivation.existing _ old deeper
    | none =>
      obtain ⟨r,found,eqn⟩ := Option.map_eq_some_iff.mp
        (by simpa [publish?,old] using hit :
         (refusal? i q (RingNestedActivePair.masked q (atRoot i root))).map (fun _ => none) = some v)
      exact eqn ▸ Derivation.refusal _ r found deeper

theorem atRoot_lower_iff {i : Input} {root : i.certified.Atom} {q : Site i}
    (on : q.val.root = root) {v : Labels} (hit : atRoot i root q = some (some v)) :
    RingJointObservations.isLower (some v.1) = true ↔
      RingClosedPairAssignment.IssuedOdd (f := q) (atRoot i root) v := by
  have cell := (atRoot_eq on).symm.trans hit
  cases old : RingClosedPairAssignment.publish? i q (atRoot i root) with
  | some val =>
    have eqv : val = some v := Option.some.inj (by simpa [publish?,old] using cell)
    exact RingClosedPairAssignment.publication_lower_iff (eqv ▸ old)
  | none =>
    cases miss : refusal? i q (RingNestedActivePair.masked q (atRoot i root)) <;>
      simp [publish?,old,miss] at cell

end TetraStereo.Engine.RingClosedGroupTie

assert_kernel_only TetraStereo.Engine.RingClosedGroupTie.Certificate.both_references
assert_kernel_only TetraStereo.Engine.RingClosedGroupTie.Certificate.rule4c
assert_kernel_only TetraStereo.Engine.RingClosedGroupTie.fixed_list
assert_kernel_only TetraStereo.Engine.RingClosedGroupTie.Certificate.rule5
assert_kernel_only TetraStereo.Engine.RingClosedGroupTie.issued
assert_kernel_only TetraStereo.Engine.RingClosedGroupTie.Refusal.physical
assert_kernel_only TetraStereo.Engine.RingClosedGroupTie.Refusal.tied_source
assert_kernel_only TetraStereo.Engine.RingClosedGroupTie.derivation
assert_kernel_only TetraStereo.Engine.RingClosedGroupTie.atRoot_lower_iff
assert_kernel_only TetraStereo.Engine.RingClosedGroupTie.atRoot_absence_iff
assert_kernel_only TetraStereo.Engine.RingClosedGroupTie.previous_on_miss
