import TetraStereo.Engine.RingNestedActivePair
import TetraStereo.Engine.RingPairAlternatives
import TetraStereo.OneCenter.LocalizedRule4bPopulationInvariance

set_option autoImplicit false

namespace TetraStereo.Engine.RingClosedPairGroup
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site Arm)
open RingNestedActivePair (Reader Labels)
open RingActivePairReport (Score)

def children (i : Input) (q : Arm i) := i.certified.executableLocalizedRerootChildren q
def projected (i : Input) (q : Arm i) :=
  (children i q).filter fun x => !(children i x).isEmpty

def silent (i : Input) (read : Reader i) (q : Arm i) : Bool :=
  (children i q).isEmpty && read q.occurrence == some none

def chiral (h : RS) : Labels := (.chiral h,.chiral h.swap)
def lower (p : PseudoRS) : Labels := (.pseudoasymmetric p,.pseudoasymmetric p)

structure Group (i : Input) (q : Arm i) (read : Reader i) where
  pos : Arm i
  neg : Arm i
  leaf : Arm i
  p : PseudoRS
  rootRead : read q.occurrence = some (some (lower p))
  posRead : read pos.occurrence = some (some (chiral .R))
  negRead : read neg.occurrence = some (some (chiral .S))
  allChildren : (children i q).Perm [pos,neg,leaf]
  live : (projected i q).Perm [pos,neg]
  real : [q,pos,neg].all (fun a => a.occurrence.val.node.provenance == .realAtom) = true
  leafSilent : silent i read leaf = true
  closed : [pos,neg].all (fun a => (children i a).length == 3 && (children i a).all (silent i read)) = true
  noLaterPos : projected i pos = []
  noLaterNeg : projected i neg = []
  z : Nat
  leafZ : Nat
  numbers : RingActivePairs.z? i pos = some z ∧ RingActivePairs.z? i neg = some z ∧
    RingActivePairs.z? i leaf = some leafZ ∧ leafZ < z
  earlier : List CIPRuleDecision
  earlierRead : RingRetainedChemicalTrace.compareAt? i q.occurrence pos.occurrence neg.occurrence = some earlier
  oneClass : cipTraceOutcome earlier = .eq

private def groupAt? (i : Input) (q : Arm i) (read : Reader i) (pos neg leaf : Arm i) :
    Option (Group i q read) := do
  let some (some (.pseudoasymmetric p,_)) := read q.occurrence | none
  let z ← RingActivePairs.z? i pos
  let leafZ ← RingActivePairs.z? i leaf
  let ⟨t,ht⟩ ← (RingRetainedChemicalTrace.compareAt? i q.occurrence pos.occurrence neg.occurrence).attach
  if h : read q.occurrence = some (some (lower p)) ∧
      read pos.occurrence = some (some (chiral .R)) ∧ read neg.occurrence = some (some (chiral .S)) ∧
      (children i q).Perm [pos,neg,leaf] ∧ (projected i q).Perm [pos,neg] ∧
      [q,pos,neg].all (fun a => a.occurrence.val.node.provenance == .realAtom) = true ∧
      silent i read leaf = true ∧
      [pos,neg].all (fun a => (children i a).length == 3 && (children i a).all (silent i read)) = true ∧
      projected i pos = [] ∧ projected i neg = [] ∧
      (RingActivePairs.z? i pos = some z ∧ RingActivePairs.z? i neg = some z ∧
        RingActivePairs.z? i leaf = some leafZ ∧ leafZ < z) ∧ cipTraceOutcome t = .eq then
    let ⟨hr,hp,hn,allC,hc,real,absent,closed,pp,pn,zs,tie⟩ := h
    return ⟨pos,neg,leaf,p,hr,hp,hn,allC,hc,real,absent,closed,pp,pn,z,leafZ,zs,t,ht,tie⟩
  else none

def group? (i : Input) (q : Arm i) (read : Reader i) : Option (Group i q read) :=
  let cs := children i q
  match cs with
  | [_,_,_] => cs.permutations'.findSome? fun xs => match xs with
    | [pos,neg,leaf] => groupAt? i q read pos neg leaf
    | _ => none
  | _ => none

/-- The entire accepted FIFO projection consists of the branch root followed by
the prior-equivalent nonterminal siblings, in the order allowed by this seed.
Each sibling has only terminal children. -/
def bit {i : Input} (read : Reader i) (rev : Bool) (seed : RS) (q : Arm i) : Nat :=
  let l := ((read q.occurrence).join).map fun p => if rev then p.2 else p.1
  ((RingNestedActivePair.upper l) == some seed).toNat

structure FilteredWalk {i q read} (g : Group i q read) (rev : Bool) (seed : RS)
    (walk : List (Arm i)) : Prop where
  exhausted : ∃ row, walk = q :: row ∧ row.Perm (projected i q) ∧
    row.Pairwise (fun a b => bit read rev seed b ≤ bit read rev seed a)

/-- Every seeded priority order of the actual two children yields the identical
accepted pairing word. The branch root's lowercase descriptor is ignored. -/
theorem pairing {i q read} (g : Group i q read) {rev seed walk}
    (h : FilteredWalk g rev seed walk) :
    (walk.drop 1).map (bit read rev seed) = [1,0] := by
  obtain ⟨row,rfl,perm,sorted⟩ := h.exhausted
  change row.map (bit read rev seed) = [1,0]
  have pp := (perm.trans g.live).map (bit read rev seed)
  have ranked : (row.map (bit read rev seed)).Pairwise (· ≥ ·) := List.pairwise_map.mpr sorted
  have multiset : (row.map (bit read rev seed)).Perm [1,0] := by
    cases rev <;> cases seed <;> simp [bit,g.posRead,g.negRead,chiral,RingNestedActivePair.upper,RS.swap] at pp <;>
      first | exact pp | exact pp.trans (List.Perm.swap ..)
  exact List.Perm.eq_of_pairwise (fun _ _ _ _ ab ba => le_antisymm ba ab) ranked (by decide) multiset

/-- A source walk exists for each seed and each geometry, since the only two
nonterminal children have opposite hands, are constitutionally tied and carry
the same unit class. The distinct lower-priority leaf is outside their group. -/
theorem walk_exists {i q read} (g : Group i q read) (rev : Bool) (seed : RS) :
    ∃ walk, FilteredWalk g rev seed walk := by
  have direct := g.live.symm
  have swap : [g.neg,g.pos].Perm (projected i q) := (List.Perm.swap ..).trans direct
  cases rev <;> cases seed
  · exact ⟨_,⟨_,rfl,direct,by simp [bit,g.posRead,g.negRead,chiral,RS.swap,RingNestedActivePair.upper]; decide⟩⟩
  · exact ⟨_,⟨_,rfl,swap,by simp [bit,g.posRead,g.negRead,chiral,RS.swap,RingNestedActivePair.upper]; decide⟩⟩
  · exact ⟨_,⟨_,rfl,swap,by simp [bit,g.posRead,g.negRead,chiral,RS.swap,RingNestedActivePair.upper]; decide⟩⟩
  · exact ⟨_,⟨_,rfl,direct,by simp [bit,g.posRead,g.negRead,chiral,RS.swap,RingNestedActivePair.upper]; decide⟩⟩



inductive FIFO (i : Input) (order : Arm i → List (Arm i) → Prop) :
    List (Arm i) → List (Arm i) → Prop where
  | stop : FIFO i order [] []
  | step {a rest row out} (p : row.Perm (projected i a)) (allowed : order a row)
      (next : FIFO i order (rest ++ row) out) : FIFO i order (a :: rest) (a :: out)

private theorem FIFO.closed {i order qs out} (seen : FIFO i order qs out)
    (ends : ∀ q ∈ qs, projected i q = []) : out = qs := by
  induction qs generalizing out with
  | nil => cases seen; rfl
  | cons a rest ih =>
    cases seen with
    | step perm _ next =>
      have empty := List.Perm.eq_nil ((ends a List.mem_cons_self) ▸ perm)
      subst_vars
      exact congrArg (List.cons a) (ih (by simpa only [List.append_nil] using next)
        (fun q h => ends q (List.mem_cons_of_mem _ h)))

def seeded {i q read} (_ : Group i q read) (rev : Bool) (seed : RS) (a : Arm i) (row : List (Arm i)) :=
  a = q → row.Pairwise (fun x y => bit read rev seed y ≤ bit read rev seed x)

/-- The restricted witness follows from an ordinary full FIFO walk, since
the two source siblings generate no further enqueued nodes. -/
theorem of_fifo {i q read} (g : Group i q read) {rev seed walk}
    (seen : FIFO i (seeded g rev seed) [q] walk) : FilteredWalk g rev seed walk := by
  cases seen with
  | @step _ _ row tail perm allowed next =>
    have ends : ∀ a ∈ row, projected i a = [] := by
      intro a h
      have p := (perm.trans g.live).mem_iff.mp h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at p
      rcases p with rfl | rfl
      · exact g.noLaterPos
      · exact g.noLaterNeg
    have closed := FIFO.closed (by simpa only [List.nil_append] using next : FIFO i _ row tail) ends
    exact ⟨row,congrArg (List.cons q) closed,perm,allowed rfl⟩

private theorem FIFO.of_closed {i : Input} {order : Arm i → List (Arm i) → Prop}
    (qs : List (Arm i)) (ends : ∀ a ∈ qs, projected i a = []) (ok : ∀ a ∈ qs, order a []) :
    FIFO i order qs qs := by
  induction qs with
  | nil => exact .stop
  | cons a rest ih =>
    apply FIFO.step (row := []) (by rw [ends a List.mem_cons_self]) (ok a List.mem_cons_self)
    simpa only [List.append_nil] using ih (fun b h => ends b (List.mem_cons_of_mem _ h))
      (fun b h => ok b (List.mem_cons_of_mem _ h))

theorem fifo_exists {i q read} (g : Group i q read) (rev : Bool) (seed : RS) :
    ∃ walk, FIFO i (seeded g rev seed) [q] walk := by
  obtain ⟨_,⟨row,rfl,perm,allowed⟩⟩ := walk_exists g rev seed
  refine ⟨q::row,.step perm (fun _ => allowed) ?_⟩
  apply FIFO.of_closed
  · intro a h
    have p := (perm.trans g.live).mem_iff.mp h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at p
    rcases p with rfl | rfl
    · exact g.noLaterPos
    · exact g.noLaterNeg
  · exact fun _ _ _ => .nil

/-- The Rule 4a observations from all three complete layers: one pseudo unit;
two chiral units above the terminal child; then all six terminal grandchildren.
This is invariant under any ordering of the two chiral children. -/
def unitAt {i} (read : Reader i) (rev : Bool) (q : Arm i) :=
  RingNestedActivePair.unit (((read q.occurrence).join).map (fun p => if rev then p.2 else p.1))

private theorem silent_unit {i read a} (quiet : silent i read a = true) (rev : Bool) :
    unitAt read rev a = 0 := by
  have got := beq_iff_eq.mp (Bool.and_eq_true_iff.mp quiet).2
  simp [unitAt,got,RingNestedActivePair.unit]

theorem fourA {i q read} (g : Group i q read) (rev : Bool) :
    unitAt read rev q = 1 ∧ unitAt read rev g.pos = 2 ∧ unitAt read rev g.neg = 2 ∧
    unitAt read rev g.leaf = 0 ∧ ∀ a ∈ [g.pos,g.neg], (children i a).length = 3 ∧
      ∀ b ∈ children i a, unitAt read rev b = 0 := by
  refine ⟨?_,?_,?_,silent_unit g.leafSilent rev,?_⟩
  · cases rev <;> simp [unitAt,g.rootRead,lower,RingNestedActivePair.unit]
  · cases rev <;> simp [unitAt,g.posRead,chiral,RingNestedActivePair.unit]
  · cases rev <;> simp [unitAt,g.negRead,chiral,RingNestedActivePair.unit]
  · intro a ha
    have closed := Bool.and_eq_true_iff.mp (List.all_eq_true.mp g.closed a ha)
    exact ⟨beq_iff_eq.mp closed.1,fun b hb => silent_unit (List.all_eq_true.mp closed.2 b hb) rev⟩

/-- The complete Rule 4a word is fixed even if the earlier-tied two
children exchange places or their silent terminal descendants are permuted. -/
theorem fourA_word {i q read} (g : Group i q read) (rev : Bool) {row ends : List (Arm i)}
    (atGroup : row.Perm (projected i q))
    (atEnds : ends.Perm (children i g.pos ++ children i g.neg)) :
    [[unitAt read rev q],(row ++ [g.leaf]).map (unitAt read rev),ends.map (unitAt read rev)] =
      [[1],[2,2,0],[0,0,0,0,0,0]] := by
  obtain ⟨hq,hp,hn,hl,all⟩ := fourA g rev
  have two := atGroup.trans g.live
  have pos := all g.pos (by simp)
  have neg := all g.neg (by simp)
  have r : row.map (unitAt read rev) = List.replicate 2 2 := by
    apply List.eq_replicate_iff.mpr
    refine ⟨by simpa using two.length_eq,?_⟩
    intro x hx
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    have p := two.mem_iff.mp ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at p
    rcases p with rfl | rfl
    · exact hp
    · exact hn
  have e : ends.map (unitAt read rev) = List.replicate 6 0 := by
    apply List.eq_replicate_iff.mpr
    refine ⟨by simpa [pos.1,neg.1] using atEnds.length_eq,?_⟩
    intro x hx
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    exact (List.mem_append.mp (atEnds.mem_iff.mp ha)).elim (pos.2 a) (neg.2 a)
  simp [hq,r,e,hl]

def score (a b : PseudoRS) : Int := RingNestedActivePair.lowerScore
  [RingNestedActivePair.lower (some (.pseudoasymmetric a))]
  [RingNestedActivePair.lower (some (.pseudoasymmetric b))]

structure Certificate (i : Input) (f a b : Site i) (read : Reader i) where
  prior : List CIPRuleDecision
  comparison : RingRetainedChemicalTrace.compareAt? i f a b = some prior
  tied : cipTraceOutcome prior = .eq
  left : Group i ⟨a,some f⟩ read
  right : Group i ⟨b,some f⟩ read
  strict : left.p ≠ right.p

def Certificate.score {i f a b read} (c : Certificate i f a b read) : Score :=
  (RingClosedPairGroup.score c.left.p c.right.p,RingClosedPairGroup.score c.left.p c.right.p)

def edge? (i : Input) (f a b : Site i) (read : Reader i) : Option (Certificate i f a b read) := do
  let ⟨t,ht⟩ ← (RingRetainedChemicalTrace.compareAt? i f a b).attach
  if tied : cipTraceOutcome t = .eq then
    let l ← group? i ⟨a,some f⟩ read
    let r ← group? i ⟨b,some f⟩ read
    if ne : l.p ≠ r.p then return ⟨t,ht,tied,l,r,ne⟩ else none
  else none

theorem Certificate.first_difference {i f a b read} (c : Certificate i f a b read) (x y : List Nat) :
    RingNestedActivePair.lowerScore (RingNestedActivePair.lower (some (.pseudoasymmetric c.left.p)) :: x)
      (RingNestedActivePair.lower (some (.pseudoasymmetric c.right.p)) :: y) = c.score.1 ∧
      (c.score = (1,1) ∨ c.score = (-1,-1)) := by
  have ne := c.strict
  cases hl : c.left.p <;> cases hr : c.right.p <;>
    simp_all [Certificate.score,RingClosedPairGroup.score,RingNestedActivePair.lowerScore,RingNestedActivePair.lower]


def upperAt {i : Input} (read : Reader i) (rev : Bool) (q : Arm i) :=
  RingNestedActivePair.upper (((read q.occurrence).join).map fun p => if rev then p.2 else p.1)

/-- The first occupied, previously equivalent, nonterminal group selects
both reference hands under the formal source population rule. -/
theorem references {i q read} (g : Group i q read) (rev : Bool) :
    localizedRule4bReferencesFromPopulation ((projected i q).filterMap (upperAt read rev)) = [.R,.S] := by
  have perm := localizedRule4bReferencesFromPopulation_perm (g.live.filterMap (upperAt read rev))
  rw [perm]
  cases rev <;> simp [upperAt,g.posRead,g.negRead,chiral,RS.swap,RingNestedActivePair.upper] <;> rfl

/-- In this tied earlier-priority group the legal seeded comparison agrees
with the independent P-92 judgment on a like and unlike publication. -/
theorem seeded_source (a b seed : RS) :
    BlueBookP92.rule4bPairDecision (if a = seed then .like else .unlike)
      (if b = seed then .like else .unlike) = compare (a == seed).toNat (b == seed).toNat := by
  cases a <;> cases b <;> cases seed <;> rfl

private theorem keep_chiral {i : Input} (read : Reader i) (rev : Bool) (seed : RS)
    (row : List (Arm i)) (allChiral : ∀ a ∈ row, (upperAt read rev a).isSome = true) :
    (row.filterMap (upperAt read rev)).map (fun h => (h == seed).toNat) =
      row.map (bit read rev seed) := by
  induction row with
  | nil => rfl
  | cons a rest ih =>
    obtain ⟨hand,found⟩ := Option.isSome_iff_exists.mp (allChiral a List.mem_cons_self)
    have head : bit read rev seed a = (hand == seed).toNat := by
      change ((upperAt read rev a) == some seed).toNat = _
      rw [found]
      rfl
    simp only [List.filterMap_cons,found,List.map_cons,head]
    exact congrArg (List.cons _) (ih fun b hb => allChiral b (List.mem_cons_of_mem _ hb))

/-- Filter complete source walks with the actual PairList acceptance rule:
lowercase and missing observations disappear, and both uppercase children
survive with their true reference-dependent pairing bits. -/
theorem accepted {i q read} (g : Group i q read) {rev seed walk}
    (seen : FIFO i (seeded g rev seed) [q] walk) :
    (walk.filterMap (upperAt read rev)).map (fun h => (h == seed).toNat) = [1,0] := by
  have proof := of_fifo g seen
  have bits := pairing g proof
  obtain ⟨row,rfl,perm,_⟩ := proof.exhausted
  have head : upperAt read rev q = none := by
    cases rev <;> simp [upperAt,g.rootRead,lower,RingNestedActivePair.upper]
  simp only [List.filterMap_cons,head]
  rw [keep_chiral]
  · exact bits
  · intro x hx
    have p := (perm.trans g.live).mem_iff.mp hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at p
    rcases p with rfl | rfl <;> cases rev <;>
      simp [upperAt,g.posRead,g.negRead,chiral,RingNestedActivePair.upper]

def word {i : Input} (read : Reader i) (rev : Bool) (seed : RS) (walk : List (Arm i)) :
    RingChemicalPriority.PairSpheres.Word := [(walk.filterMap (upperAt read rev)).map (fun h => (h == seed).toNat)]

/-- Both ligands choose their best reference independently. Each of their two
actual filtered walks has the same complete accepted word, so the formal
dual-reference decision is equality for every allowed choice of all four walks. -/
theorem Certificate.dual_reference {i f a b read} (c : Certificate i f a b read) (rev : Bool)
    {lr ls rr rs} (h₁ : FIFO i (seeded c.left rev .R) [⟨a,some f⟩] lr)
    (h₂ : FIFO i (seeded c.left rev .S) [⟨a,some f⟩] ls)
    (h₃ : FIFO i (seeded c.right rev .R) [⟨b,some f⟩] rr)
    (h₄ : FIFO i (seeded c.right rev .S) [⟨b,some f⟩] rs) :
    max (word read rev .R lr) (word read rev .S ls) =
      max (word read rev .R rr) (word read rev .S rs) := by
  let bounds := RingChemicalPriority.PairSpheres.Interval.exact [[1,0]]
  have bound {k seed walk} (g : Group i k read) (seen : FIFO i (seeded g rev seed) [k] walk) :
      bounds.Allows (word read rev seed walk) := by
    simp [word,accepted g seen,bounds,RingChemicalPriority.PairSpheres.Interval.exact,
      RingChemicalPriority.PairSpheres.Interval.Allows]
  have left := RingChemicalPriority.PairSpheres.Interval.best_allows (bound c.left h₁) (bound c.left h₂)
  have right := RingChemicalPriority.PairSpheres.Interval.best_allows (bound c.right h₃) (bound c.right h₄)
  exact RingChemicalPriority.PairSpheres.Interval.decision left right (result := .eq) (by decide +kernel)

theorem Certificate.rule4c {i f a b read} (c : Certificate i f a b read) :
    Rule4c5SourceDecision.sourceRule4cPairDecision (.pseudoasymmetric c.left.p) (.pseudoasymmetric c.right.p) =
      some (if 0 < c.score.1 then .gt else .lt) := by
  rw [RingNestedActivePair.lower_pair]
  have ne := c.strict
  cases hl : c.left.p <;> cases hr : c.right.p <;>
    simp_all [Certificate.score,RingClosedPairGroup.score,RingNestedActivePair.lowerScore,RingNestedActivePair.lower] <;> decide

/-- This edge can augment the existing strict or physically resolved edges.
Every successful evaluation records which of the two proofs supplied its score. -/
def score? (i : Input) (f a b : Site i) (read : Reader i) : Option Score :=
  ((RingNestedActivePair.edge? i f a b read).map Subtype.val).orElse fun _ => (edge? i f a b read).map Certificate.score

theorem issued {i f a b read v} (hit : score? i f a b read = some v) :
    RingNestedActivePair.Edge i f a b read v ∨ ∃ c : Certificate i f a b read, c.score = v := by
  cases h : RingNestedActivePair.edge? i f a b read with
  | some e => exact Or.inl ((Option.some.inj (by simpa [score?,h] using hit) : e.val = v) ▸ e.property)
  | none =>
    have got : (edge? i f a b read).map Certificate.score = some v := by simpa [score?,h] using hit
    obtain ⟨c,_,eqn⟩ := Option.map_eq_some_iff.mp got
    exact Or.inr ⟨c,eqn⟩

end TetraStereo.Engine.RingClosedPairGroup
assert_kernel_only TetraStereo.Engine.RingClosedPairGroup.pairing
assert_kernel_only TetraStereo.Engine.RingClosedPairGroup.walk_exists
assert_kernel_only TetraStereo.Engine.RingClosedPairGroup.fourA
assert_kernel_only TetraStereo.Engine.RingClosedPairGroup.Certificate.first_difference
assert_kernel_only TetraStereo.Engine.RingClosedPairGroup.issued
assert_kernel_only TetraStereo.Engine.RingClosedPairGroup.of_fifo
assert_kernel_only TetraStereo.Engine.RingClosedPairGroup.fifo_exists
assert_kernel_only TetraStereo.Engine.RingClosedPairGroup.Certificate.dual_reference
assert_kernel_only TetraStereo.Engine.RingClosedPairGroup.Certificate.rule4c
assert_kernel_only TetraStereo.Engine.RingClosedPairGroup.accepted
assert_kernel_only TetraStereo.Engine.RingClosedPairGroup.references
assert_kernel_only TetraStereo.Engine.RingClosedPairGroup.seeded_source
assert_kernel_only TetraStereo.Engine.RingClosedPairGroup.fourA_word
