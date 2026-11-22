import TetraStereo.Engine.RingSeededPairs
import TetraStereo.Engine.RingRetainedAuxiliary

set_option autoImplicit false

namespace TetraStereo.Engine.RingActivePairs

open OneCenter CertifiedLocalizedCIPInput RingRetainedConstitution
open LocalizedChemicalRing (Input)
open RingSeededPairs (Spheres Decision)

abbrev Site (i : Input) := i.certified.LocalizedCIPOccurrence (i.certified.certified.input.molecule.atomCount + 1)
abbrev Arm (i : Input) := Cursor i.certified (i.certified.certified.input.molecule.atomCount + 1)

/-- Tetrahedral auxiliary batches exclude the original configuration and publish only after
a distance is complete. A site on another original digraph cannot supply a publication. -/
def active? (i : Input) (focus q : Site i) : Option (Option RS) :=
  if q.val.root ≠ focus.val.root then none
  else if focus.val.address.length < q.val.address.length ∧ q.val.node.current? ≠ some focus.val.root then
    RingRetainedAuxiliary.publication? i q
  else some none

theorem active_positive (i : Input) (focus q : Site i) (hand : RS) :
    active? i focus q = some (some hand) ↔ q.val.root = focus.val.root ∧
    focus.val.address.length < q.val.address.length ∧ q.val.node.current? ≠ some focus.val.root ∧
      RingRetainedAuxiliary.publication? i q = some (some hand) := by
  unfold active?
  split_ifs <;> simp_all

/-- Full-carrier children of a retained direction. The two descriptor queue walkers in
Rule4b and Rule5New enqueue outward nonterminal nodes in the reference sorter's order. -/
def next (i : Input) (q : Arm i) : List (Arm i) :=
  (i.certified.executableLocalizedRerootChildren q).filter fun child =>
    !(i.certified.executableLocalizedRerootChildren child).isEmpty

/-- Return no profile if fuel expires before the queue is empty. One breadth layer is
retained per distance, preserving multiplicity and the original address of each visit. -/
def levels? (i : Input) : Nat → List (Arm i) → Option (List (List (Arm i)))
  | _,[] => some []
  | 0,_ :: _ => none
  | n+1,q :: qs => do
    let layer := q :: qs
    return layer :: (← levels? i n (layer.flatMap (next i)))

def observations? (i : Input) (focus : Site i) (levels : List (List (Arm i))) : Option Spheres :=
  levels.mapM (fun layer => layer.mapM (fun q => active? i focus q.occurrence))

private theorem mapM_perm {α β : Type} {f : α → Option β} {xs ys : List α}
    (perm : xs.Perm ys) {values} (read : ys.mapM f = some values) :
    ∃ actual, xs.mapM f = some actual ∧ actual.Perm values := by
  induction perm generalizing values with
  | nil => exact ⟨[],rfl,by simpa using read⟩
  | @cons x xs ys _ ih =>
    rw [List.mapM_cons] at read ⊢
    cases hx : f x <;> cases hy : ys.mapM f <;> simp [hx,hy] at read
    subst values
    obtain ⟨v,hv,perm⟩ := ih hy
    exact ⟨_,by simp [hv],.cons _ perm⟩
  | swap x y xs =>
    simp only [List.mapM_cons] at read ⊢
    cases hx : f x <;> cases hy : f y <;> cases tail : xs.mapM f <;> simp [hx,hy,tail] at read ⊢
    subst values
    exact List.Perm.swap ..
  | trans p q ih jh =>
    obtain ⟨mid,r,eq⟩ := jh read
    obtain ⟨out,s,eq'⟩ := ih r
    exact ⟨out,s,eq'.trans eq⟩

/-- Every independent reordering of a molecular sphere reads exactly the same publications
up to permutation. Missing molecular evidence is never treated as an unlabeled atom. -/
theorem observations_perm {i : Input} {focus : Site i} {xs ys : List (List (Arm i))}
    (orders : List.Forall₂ List.Perm xs ys) {s : Spheres} (read : observations? i focus ys = some s) :
    ∃ t, observations? i focus xs = some t ∧ List.Forall₂ List.Perm t s := by
  unfold observations? at read ⊢
  induction orders generalizing s with
  | nil => obtain rfl : [] = s := Option.some.inj read; exact ⟨[],rfl,.nil⟩
  | cons perm tail ih =>
    rw [List.mapM_cons] at read ⊢
    rename_i x y xs ys
    cases h : y.mapM (fun q => active? i focus q.occurrence) <;>
      cases r : ys.mapM (fun layer => layer.mapM (fun q => active? i focus q.occurrence)) <;> simp [h,r] at read
    subst s
    obtain ⟨a,ha,pa⟩ := mapM_perm perm h
    obtain ⟨b,hb,pb⟩ := ih r
    exact ⟨a :: b,by simp [ha,hb],.cons pa pb⟩

structure ArmProfile (i : Input) (focus q : Site i) where
  levels : List (List (Arm i))
  walked : levels? i (2*(i.certified.certified.input.molecule.atomCount+2)+2) [⟨q,some focus⟩] = some levels
  spheres : Spheres
  bound : observations? i focus levels = some spheres

def arm? (i : Input) (focus q : Site i) : Option (ArmProfile i focus q) := do
  let ⟨levels,walked⟩ ← (levels? i (2*(i.certified.certified.input.molecule.atomCount+2)+2) [⟨q,some focus⟩]).attach
  let ⟨s,read⟩ ← (observations? i focus levels).attach
  return ⟨levels,walked,s,read⟩

structure Certificate (i : Input) (focus l r : Site i) where
  prior : List CIPRuleDecision
  incident : compareAt? i.certified focus l r = some prior
  tied : cipTraceOutcome prior = .eq
  left : ArmProfile i focus l
  right : ArmProfile i focus r
  outcome : Decision
  decided : RingSeededPairs.evaluate? left.spheres right.spheres = some outcome

def compare? (i : Input) (focus l r : Site i) : Option (Certificate i focus l r) := do
  let ⟨t,ht⟩ ← (compareAt? i.certified focus l r).attach
  if tied : cipTraceOutcome t = .eq then
    let a ← arm? i focus l
    let b ← arm? i focus r
    let ⟨o,h⟩ ← (RingSeededPairs.evaluate? a.spheres b.spheres).attach
    return ⟨t,ht,tied,a,b,o,h⟩
  else none

theorem ArmProfile.visit {i f q} (a : ArmProfile i f q) {ls}
    (order : List.Forall₂ List.Perm ls a.levels) :
    ∃ s, observations? i f ls = some s ∧ RingSeededPairs.Visits a.spheres s.flatten := by
  obtain ⟨s,read,perms⟩ := observations_perm order a.bound
  exact ⟨s,read,s,perms,rfl⟩

/-- The integer atomic number of the actual molecule record at the endpoint. -/
def endpointZ? (i : Input) (q : Arm i) : Option Nat := do
  let atom ← q.occurrence.val.node.current?
  let record ← i.molecule.atoms[atom.val]?
  guard (record.element.atomicNumber > 0)
  return record.element.atomicNumber

/-- Both a real node and a terminal ring duplicate have the atomic number of the
addressed atom on this single-bond domain. A duplicate is never a publication source.
Centres 1.0 Node.newTerminalChild uses the atom numerator and denominator one for a
ring closure; Labeller.labelAux skips such nodes. -/
def z? (i : Input) (q : Arm i) : Option Nat :=
  match q.occurrence.val.node.provenance with
  | .realAtom => endpointZ? i q
  | .ringDuplicate _ => if (i.certified.executableLocalizedRerootChildren q).isEmpty then endpointZ? i q else none
  | _ => none

/-- The closure has separate constitutional and stereochemical observations. Its
original distance remains in the addressed constitutional trace. Its shallow priority
uses the endpoint atomic number and its frozen tetrahedral publication is absent. -/
theorem ring_closure_observations (i : Input) (focus : Site i) (q : Arm i) {origin : Nat}
    (closure : q.occurrence.val.node.provenance = .ringDuplicate origin)
    (terminal : i.certified.executableLocalizedRerootChildren q = [])
    (scope : q.occurrence.val.root = focus.val.root) :
    z? i q = endpointZ? i q ∧ active? i focus q.occurrence = some none := by
  have absent : RingRetainedAuxiliary.publication? i q.occurrence = some none :=
    (RingRetainedAuxiliary.absence_iff ..).mpr (fun _ h => by have real := h.1; rw [closure] at real; contradiction)
  exact ⟨by simp [z?,closure,terminal],by simp [active?,scope,absent]⟩

abbrev Edge (i : Input) := Arm i × Nat

def strictEdges (i : Input) (edges : List (Edge i)) :=
  edges.Pairwise fun a b => b.2 < a.2

instance {i es} : Decidable (strictEdges i es) := by unfold strictEdges; infer_instance

def children? (i : Input) (q : Arm i) : Option (List (Edge i)) := do
  let edges ← (i.certified.executableLocalizedRerootChildren q).mapM fun a => (z? i a).map (a,·)
  let sorted := edges.mergeSort fun a b => a.2 ≥ b.2
  if strictEdges i sorted then return sorted else none

theorem only_order {i : Input} {q : Arm i} {edges xs : List (Edge i)}
    (got : children? i q = some edges) (perm : xs.Perm edges) (sorted : strictEdges i xs) : xs = edges := by
  have strict : strictEdges i edges := by
    unfold children? at got
    cases h : (i.certified.executableLocalizedRerootChildren q).mapM (fun a => (z? i a).map (a,·)) <;> simp [h] at got
    exact got.2 ▸ got.1
  exact List.Perm.eq_of_pairwise (fun _ _ _ _ a b => False.elim (Nat.lt_asymm a b)) sorted strict perm

/-- The sorted molecular queue records the Rule 4a unit observation and the number of
outward children at each aligned node. The Rule 4b/5 queue visits its first node and
subsequently visits only nonterminal descendants. -/
structure NodeRead where
  address : List Nat
  atomicNumber : Nat
  children : Nat
  hand : Option RS
  deriving Repr, DecidableEq

def NodeRead.signature (v : NodeRead) := (v.atomicNumber,v.children,v.hand.isSome)

def orderedLevels? (i : Input) (focus : Site i) :
    Nat → List (Arm i) → Option (List (List NodeRead))
  | _,[] => some []
  | 0,_ :: _ => none
  | n+1,a :: rest => do
    let frame ← (a :: rest).mapM fun q => do
      let edges ← children? i q
      let z ← z? i q
      let hand ← active? i focus q.occurrence
      return (NodeRead.mk q.occurrence.val.address z edges.length hand,edges.map Prod.fst)
    return frame.map Prod.fst :: (← orderedLevels? i focus n (frame.flatMap Prod.snd))

def descriptorWalk : List (List NodeRead) → List (Option RS)
  | [] => []
  | root :: rest => root.map (·.hand) ++ rest.flatMap fun layer =>
    (layer.filter (fun v => 0 < v.children)).map (·.hand)

def swapWalk (xs : List (Option RS)) := xs.map (Option.map RS.swap)

structure OrderedPair (i : Input) (focus l r : Site i) where
  prior : List CIPRuleDecision
  edges : compareAt? i.certified focus l r = some prior
  tied : cipTraceOutcome prior = .eq
  left : List (List NodeRead)
  right : List (List NodeRead)
  leftRead : orderedLevels? i focus (2*(i.certified.certified.input.molecule.atomCount+2)+2) [⟨l,some focus⟩] = some left
  rightRead : orderedLevels? i focus (2*(i.certified.certified.input.molecule.atomCount+2)+2) [⟨r,some focus⟩] = some right
  earlier : left.map (List.map NodeRead.signature) = right.map (List.map NodeRead.signature)

def orderedPair? (i : Input) (focus l r : Site i) : Option (OrderedPair i focus l r) := do
  let ⟨prior,edges⟩ ← (compareAt? i.certified focus l r).attach
  if tied : cipTraceOutcome prior = .eq then
    let n := 2*(i.certified.certified.input.molecule.atomCount+2)+2
    let ⟨left,hl⟩ ← (orderedLevels? i focus n [⟨l,some focus⟩]).attach
    let ⟨right,hr⟩ ← (orderedLevels? i focus n [⟨r,some focus⟩]).attach
    if earlier : left.map (List.map NodeRead.signature) = right.map (List.map NodeRead.signature) then
      return ⟨prior,edges,tied,left,right,hl,hr,earlier⟩
    else none
  else none

def OrderedPair.decision? {i f l r} (p : OrderedPair i f l r) (mirror : Bool) : Option Decision :=
  let view := fun v => if mirror then swapWalk (descriptorWalk v) else descriptorWalk v
  let a := view p.left
  let b := view p.right
  RingSeededPairs.fromVisits? a b a b a b

def score (d : Decision) := d.rule5.getD d.rule4b

/-- The actual score and its reflected score. A strict constitutional edge consumes no
auxiliary. A tied edge visits both original branches in molecular sibling order. -/
def rootScore? (i : Input) (c : i.certified.TetrahedralCenter) (a b : Fin 4) : Option (Int × Int) := do
  if a = b then return (0,0)
  let prior ← i.certified.compareRuleMajorConstitutionAt? c a b
  match prior.outcome with
  | .lt => return (-1,-1)
  | .gt => return (1,1)
  | .eq =>
    let sites := (i.certified.localizedOccurrences (i.certified.certified.input.molecule.atomCount+1)).attach
    let focus ← sites.find? fun q => q.val.root == c.val && q.val.address.isEmpty
    let branch := fun (slot : Fin 4) => sites.find? fun q =>
      q.val.root == c.val && q.val.address.length == 1 && q.val.node.current? == some (i.certified.canonicalLigandAtom c slot)
    let l ← branch a
    let r ← branch b
    let p ← orderedPair? i focus l r
    return (score (← p.decision? false),score (← p.decision? true))

end TetraStereo.Engine.RingActivePairs

assert_kernel_only TetraStereo.Engine.RingActivePairs.active_positive
assert_kernel_only TetraStereo.Engine.RingActivePairs.ArmProfile.visit
assert_kernel_only TetraStereo.Engine.RingActivePairs.compare?

assert_kernel_only TetraStereo.Engine.RingActivePairs.only_order
assert_kernel_only TetraStereo.Engine.RingActivePairs.rootScore?

assert_kernel_only TetraStereo.Engine.RingActivePairs.ring_closure_observations
