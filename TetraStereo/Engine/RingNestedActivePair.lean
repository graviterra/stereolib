import TetraStereo.Engine.RingActivePairReport
import TetraStereo.Engine.RingRetainedSiblingOrder
import TetraStereo.Engine.RingRetainedSilentPair
import TetraStereo.Engine.RingRetainedTerminalClass
import TetraStereo.Engine.RingRetainedProtiumClass
import TetraStereo.Engine.RingOrdinaryPairRefusal

set_option autoImplicit false

namespace TetraStereo.Engine.RingNestedActivePair
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActivePairs (Site Arm)
open RingActivePairReport (Slot Score Matrix Ranking)
open LocalizedChemicalRingPhysicalSense (inputGeometry)

/-- Both projections of one tetrahedral publication. An inner absence certifies that the
site contributes no label, while an outer absence leaves the computation open. -/
abbrev Labels := LocalizedAuxiliaryLabel × LocalizedAuxiliaryLabel
abbrev Reader (i : Input) := Site i → Option (Option Labels)

def Eligible {i : Input} (focus q : Site i) := q.val.root = focus.val.root ∧
  focus.val.address.length < q.val.address.length ∧ q.val.node.current? ≠ some focus.val.root

instance {i : Input} {f q : Site i} : Decidable (Eligible f q) := by unfold Eligible; infer_instance

def masked {i : Input} (focus : Site i) (read : Reader i) : Reader i := fun q =>
  if q.val.root ≠ focus.val.root then none else if Eligible focus q then read q else some none

/-- The positive and absent readings in the frozen state share one original root and are
strictly deeper in its original publication schedule. -/
theorem masked_congr {i : Input} (f : Site i) {a b : Reader i}
    (agree : ∀ q, Eligible f q → a q = b q) : masked f a = masked f b := by
  funext q
  by_cases ok : Eligible f q <;> simp [masked,ok,agree q]

/-- Breadth-first traversal with the same source-qualified sibling sorter used by the
fresh-root pair evaluator. Queue exhaustion is checked before the depth boundary. -/
def orderedLevelsWith? {α : Type} (i : Input) (visit : Arm i → Nat → Nat → Option α) :
    Nat → List (Arm i) → Option (List (List α))
  | _,[] => some []
  | 0,_ :: _ => none
  | n+1,a :: rest => do
    let layer ← (a :: rest).mapM fun q => do
      let edges ← RingActivePairs.children? i q
      let z ← RingActivePairs.z? i q
      let value ← visit q z edges.length
      return (value,edges.map Prod.fst)
    return layer.map Prod.fst :: (← orderedLevelsWith? i visit n (layer.flatMap Prod.snd))

/-- Project the existing uppercase-only fixed-root reader through the generic BFS walker. -/
def rootVisit (i : Input) (focus : Site i) (q : Arm i) (z degree : Nat) : Option RingActivePairs.NodeRead := do
  let h ← RingActivePairs.active? i focus q.occurrence
  return ⟨q.occurrence.val.address,z,degree,h⟩
theorem ordered_specializes (i : Input) (f : Site i) : ∀ n qs,
    orderedLevelsWith? i (rootVisit i f) n qs = RingActivePairs.orderedLevels? i f n qs
  | 0,[] | _+1,[] | 0,_::_ => rfl
  | n+1,q::qs => by
    simp only [orderedLevelsWith?,RingActivePairs.orderedLevels?,rootVisit,bind_assoc,pure_bind,
      ordered_specializes i f n]

structure Visit where
  address : List Nat
  z : Nat
  children : Nat
  publication : Option Labels
  deriving DecidableEq, Repr

def consistent : Labels → Bool
  | (.chiral x,.chiral y) => y == x.swap
  | (.pseudoasymmetric x,.pseudoasymmetric y) => x == y
  | _ => false

def visit {i : Input} (read : Reader i) (q : Arm i) (z children : Nat) : Option Visit := do
  let labels ← read q.occurrence
  if labels.all consistent = true ∧ (children ≠ 0 ∨ labels.isNone = true) then
    return ⟨q.occurrence.val.address,z,children,labels⟩
  else none

def Visit.label (v : Visit) (rev : Bool) := v.publication.map fun p => if rev then p.2 else p.1

def unit : Option LocalizedAuxiliaryLabel → Nat
  | none => 0 | some (.pseudoasymmetric _) => 1 | some (.chiral _) => 2

def upper : Option LocalizedAuxiliaryLabel → Option RS
  | some (.chiral h) => some h | _ => none

/-- The tetrahedral Rule 4c source has r above s. Bond stereo is absent from the public
single-bond profile. The other publication types have ordinal zero at this stage. -/
def lower : Option LocalizedAuxiliaryLabel → Nat
  | some (.pseudoasymmetric .r) => 2 | some (.pseudoasymmetric .s) => 1 | _ => 0

def topology (v : Visit) := (v.z,v.children)
def unitWord (vs : List (List Visit)) (rev : Bool) : List Nat :=
  (vs.map (List.map (fun v => unit (v.label rev)))).flatten

def signature (v : Visit) := (v.z,v.children,unit (v.label false),unit (v.label true))

def descriptors : List (List Visit) → List Visit
  | [] => []
  | top :: tail => top ++ tail.flatMap (fun layer => layer.filter (fun v => 0 < v.children))

/-- First strict stage-4c node comparison in the two fully aligned BFS profiles. -/
def lowerScore : List Nat → List Nat → Int
  | x :: xs,y :: ys => if x = y then lowerScore xs ys else if y < x then 1 else -1
  | _,_ => 0

/-- The first strict Rule 4a unit comparison precedes all descriptor comparisons.
On a complete unit tie, Rule 4b compares uppercase like/unlike words. Following a tie, Rule 4c consumes the
full ordered lower-case observations. Following a further tie, Rule 5 uses two fixed seeds.
Both geometries obtain their own scores from the corresponding published labels. -/
def decide? (a b : List (List Visit)) (rev : Bool) : Option Int := do
  guard (a.map (List.map topology) == b.map (List.map topology))
  let fourA := lowerScore (unitWord a rev) (unitWord b rev)
  if fourA ≠ 0 then return fourA
  let word (xs : List (List Visit)) := (descriptors xs).map (fun v => upper (v.label rev))
  let x := word a
  let y := word b
  let first ← RingSeededPairs.localSign? x y
  if first ≠ 0 then return first
  let stage4c := lowerScore (a.flatten.map (fun v => lower (v.label rev))) (b.flatten.map (fun v => lower (v.label rev)))
  if stage4c ≠ 0 then return stage4c
  let r ← RingSeededPairs.listSign? .R x y
  let s ← RingSeededPairs.listSign? .S x y
  return CentresRing.PairList.combine r s

/-- Ordinal zero is a frozen absence of a publication. In particular a masked shallower
occurrence may be absent while its atom is stereogenic elsewhere. -/
def sourceClass : Option LocalizedAuxiliaryLabel → Rule4bSparseSource.SourceRule4aClass
  | none => .unavailable
  | some (.pseudoasymmetric _) => .pseudoasymmetricDeferred
  | some (.chiral _) => .chiral

/-- The preceding-rule gate agrees with the independent three-class source judgment,
including the publication-unavailable class. -/
theorem unit_pair (a b : Option LocalizedAuxiliaryLabel) :
    Rule4bSparseSource.sourceRule4aGateDecision (sourceClass a) (sourceClass b) =
      compare (unit a) (unit b) := by
  rcases a with _ | (_ | _) <;> rcases b with _ | (_ | _) <;> rfl

theorem unit_p92 {a b : Option LocalizedAuxiliaryLabel} (ha : a.isSome) (hb : b.isSome) :
    BlueBookP92.rule4aDecision (Rule4bSparseSource.sourceRule4aClassToP92 (sourceClass a))
      (Rule4bSparseSource.sourceRule4aClassToP92 (sourceClass b)) = compare (unit a) (unit b) := by
  rcases a with _ | (_ | _) <;> rcases b with _ | (_ | _) <;> simp_all <;> rfl

theorem lowerScore_self (a : List Nat) : lowerScore a a = 0 := by
  induction a with
  | nil => rfl
  | cons x xs ih => simpa [lowerScore] using ih

theorem signature_projection {a b : List (List Visit)}
    (h : a.map (List.map signature) = b.map (List.map signature)) (rev : Bool) :
    a.map (List.map topology) = b.map (List.map topology) ∧ unitWord a rev = unitWord b rev := by
  constructor
  · have eqn := congrArg (List.map (List.map (fun (v : Nat × Nat × Nat × Nat) => (v.1,v.2.1)))) h
    simpa [List.map_map,Function.comp_def,signature,topology] using eqn
  · cases rev
    · have eqn := congrArg (fun x => (x.map (List.map (fun (v : Nat × Nat × Nat × Nat) => v.2.2.1))).flatten) h
      simpa [unitWord,List.map_map,Function.comp_def,signature] using eqn
    · have eqn := congrArg (fun x => (x.map (List.map (fun (v : Nat × Nat × Nat × Nat) => v.2.2.2))).flatten) h
      simpa [unitWord,List.map_map,Function.comp_def,signature] using eqn

theorem decide_rule4a {a b : List (List Visit)} {rev : Bool} {v : Int}
    (shape : a.map (List.map topology) = b.map (List.map topology))
    (score : lowerScore (unitWord a rev) (unitWord b rev) = v) (strict : v ≠ 0) :
    decide? a b rev = some v := by
  simp [decide?,shape,score,strict]

/-- For the two applicable tetrahedral symbols, the numeric stage has exactly the
ordering specified by the independent P-92.1.3.4(c) source judgment. -/
theorem lower_pair (a b : PseudoRS) :
    Rule4c5SourceDecision.sourceRule4cPairDecision (.pseudoasymmetric a) (.pseudoasymmetric b) =
      some (compare (lower (some (.pseudoasymmetric a))) (lower (some (.pseudoasymmetric b)))) := by
  cases a <;> cases b <;> rfl

theorem lower_first_difference (pre : List Nat) (a b : Nat) (xs ys : List Nat) (ne : a ≠ b) :
    lowerScore (pre ++ a::xs) (pre ++ b::ys) = (if b < a then 1 else -1) := by
  induction pre with
  | nil => simp [lowerScore,ne]
  | cons z zs ih => simpa [lowerScore] using ih

/-- A strict source judgment after an exactly equal prefix of active unit readings
determines the full molecular edge score ahead of all descriptor rules. -/
theorem decide_rule4a_first {a b : List (List Visit)} {rev : Bool}
    (shape : a.map (List.map topology) = b.map (List.map topology))
    (pre leftTail rightTail : List Nat) (x y : Option LocalizedAuxiliaryLabel)
    (hx : unitWord a rev = pre ++ unit x :: leftTail)
    (hy : unitWord b rev = pre ++ unit y :: rightTail)
    (different : Rule4bSparseSource.sourceRule4aGateDecision (sourceClass x) (sourceClass y) ≠ .eq) :
    decide? a b rev = some (if Rule4bSparseSource.sourceRule4aGateDecision (sourceClass x) (sourceClass y) = .gt then 1 else -1) := by
  apply decide_rule4a shape
  · rw [hx,hy]
    have ne : unit x ≠ unit y := by
      intro equ
      apply different
      exact (unit_pair x y).trans (Nat.compare_eq_eq.mpr equ)
    rw [lower_first_difference _ _ _ _ _ ne]
    simp only [unit_pair,Nat.compare_eq_gt]
  · split <;> decide

/-- A prior uppercase Rule 4b tie followed by a strict lowercase comparison fixes the
score before either Rule 5 seed is consulted. -/
theorem decide_rule4c {a b : List (List Visit)} {rev : Bool} {v : Int}
    (shape : a.map (List.map signature) = b.map (List.map signature))
    (tied : RingSeededPairs.localSign? ((descriptors a).map (fun w => upper (w.label rev)))
      ((descriptors b).map (fun w => upper (w.label rev))) = some 0)
    (low : lowerScore (a.flatten.map (fun w => lower (w.label rev)))
      (b.flatten.map (fun w => lower (w.label rev))) = v) (strict : v ≠ 0) :
    decide? a b rev = some v := by
  obtain ⟨top,units⟩ := signature_projection shape rev
  simp only [List.map_flatten] at low
  simp [decide?,top,units,lowerScore_self,tied,low,strict]

/-- Shallow comparisons inspect the two unit classes and the two lowercase ordinals.
Uppercase hands are read later in the constitutionally ordered descriptor queue. -/
def shallowReading {i : Input} (read : Reader i) (q : Arm i) :=
  (read q.occurrence).map fun labels =>
    (unit (labels.map Prod.fst),unit (labels.map Prod.snd),
      lower (labels.map Prod.fst),lower (labels.map Prod.snd))

private def number (i : Input) (q : Arm i) := (RingActivePairs.z? i q).getD 0

/-- A full constitutional order can differ from a shallow sort at equal atomic numbers.
Such exchanges preserve the shallow observations exactly when each tied block is constant. -/
def ShallowOrder (i : Input) (read : Reader i) (xs : List (Arm i)) : Prop :=
  xs.Pairwise fun a b => number i b < number i a ∨
    (number i a = number i b ∧ shallowReading read a = shallowReading read b)

instance {i read xs} : Decidable (ShallowOrder i read xs) := by unfold ShallowOrder; infer_instance

/-- Every shallow sort allowed by atomic priority gives the same actual/reflected
unit and lowercase words, including when it exchanges constitutionally distinct arms. -/
theorem shallow_invariant {i : Input} {read : Reader i} {xs ys : List (Arm i)}
    (cert : ShallowOrder i read xs) (perm : xs.Perm ys)
    (legal : ys.Pairwise fun a b => (RingActivePairs.z? i b).getD 0 ≤ (RingActivePairs.z? i a).getD 0) :
    xs.map (shallowReading read) = ys.map (shallowReading read) := by
  let row (a : Arm i) := (number i a,shallowReading read a)
  have x : (xs.map row).Pairwise (fun a b => b.1 < a.1 ∨ a = b) := by
    apply List.pairwise_map.mpr
    exact cert.imp fun h => h.elim Or.inl (fun ⟨hz,hr⟩ => Or.inr (Prod.ext hz hr))
  have y : (ys.map row).Pairwise (fun a b => b.1 ≤ a.1) := List.pairwise_map.mpr legal
  have same : (xs.map row).Pairwise (fun a b => a.1 = b.1 → a = b) :=
    x.imp fun h eqn => h.elim (fun lt => False.elim (Nat.ne_of_lt lt eqn.symm)) id
  have transported := ((perm.map row).pairwise_iff
    (R := fun a b => a.1 = b.1 → a = b) (fun h eqn => (h eqn.symm).symm)).mp same
  have sorted : (ys.map row).Pairwise (fun a b => b.1 < a.1 ∨ a = b) :=
    (List.pairwise_and_iff.mpr ⟨y,transported⟩).imp fun ⟨le,sameKey⟩ =>
      (Nat.lt_or_eq_of_le le).imp id (fun eqn => sameKey eqn.symm)
  have eqn := List.Perm.eq_of_pairwise (fun _ _ _ _ h k =>
    h.elim (fun lt => k.elim (fun gt => False.elim (Nat.lt_asymm lt gt))
      (fun eqn => eqn.symm)) id) x sorted (perm.map row)
  simpa [row,List.map_map,Function.comp_def] using congrArg (List.map Prod.snd) eqn

private def retainedChildren? (i : Input) (read : Reader i) (q : Arm i) :
    Option {xs : List (Arm i) // RingRetainedSiblingOrder.Order i q xs ∧ ShallowOrder i read xs} := do
  let ⟨xs,source⟩ ← RingRetainedSiblingOrder.chemicalChildren? i q
  if h : ShallowOrder i read xs then return ⟨xs,source,h⟩ else none

/-- The molecular queue uses all children of the original cursor in a certified earlier-rule
order. The immediate observations are invariant under each remaining shallow-sort choice. -/
def retainedLevels? (i : Input) (read : Reader i) :
    Nat → List (Arm i) → Option (List (List Visit))
  | _,[] => some []
  | 0,_ :: _ => none
  | n+1,q :: qs => do
    let data ← (q :: qs).mapM fun a => do
      let children ← retainedChildren? i read a
      let z ← RingActivePairs.z? i a
      let v ← visit read a z children.val.length
      return (v,children.val)
    return data.map Prod.fst :: (← retainedLevels? i read n (data.flatMap Prod.snd))

structure Pair (i : Input) (focus a b : Site i) (read : Reader i) where
  trace : List CIPRuleDecision
  prior : RingRetainedChemicalTrace.compareAt? i focus a b = some trace
  tied : cipTraceOutcome trace = .eq
  left : List (List Visit)
  right : List (List Visit)
  leftRead : retainedLevels? i read (2*(i.certified.certified.input.molecule.atomCount+2)+2) [⟨a,some focus⟩] = some left
  rightRead : retainedLevels? i read (2*(i.certified.certified.input.molecule.atomCount+2)+2) [⟨b,some focus⟩] = some right
  scores : Score
  actual : decide? left right false = some scores.1
  reflected : decide? left right true = some scores.2

/-- A strict constitutional edge retains its sign on both geometries. A tied edge is
revisited as two actual original-carrier arms entered from this same occurrence. -/
inductive Edge (i : Input) (f a b : Site i) (read : Reader i) : Score → Prop where
  | below {t} (prior : RingRetainedChemicalTrace.compareAt? i f a b = some t) (strict : cipTraceOutcome t = .lt) : Edge i f a b read (-1,-1)
  | above {t} (prior : RingRetainedChemicalTrace.compareAt? i f a b = some t) (strict : cipTraceOutcome t = .gt) : Edge i f a b read (1,1)
  | stereo (p : Pair i f a b read) : Edge i f a b read p.scores

def edge? (i : Input) (f a b : Site i) (read : Reader i) : Option {s : Score // Edge i f a b read s} := do
  let ⟨t,ht⟩ ← (RingRetainedChemicalTrace.compareAt? i f a b).attach
  match h : cipTraceOutcome t with
  | .lt => return ⟨(-1,-1),.below ht h⟩
  | .gt => return ⟨(1,1),.above ht h⟩
  | .eq =>
    let n := 2*(i.certified.certified.input.molecule.atomCount+2)+2
    let ⟨xs,hx⟩ ← (retainedLevels? i read n [⟨a,some f⟩]).attach
    let ⟨ys,hy⟩ ← (retainedLevels? i read n [⟨b,some f⟩]).attach
    let ⟨v,hv⟩ ← (decide? xs ys false).attach
    let ⟨w,hw⟩ ← (decide? xs ys true).attach
    return ⟨(v,w),.stereo ⟨t,ht,h,xs,ys,hx,hy,(v,w),hv,hw⟩⟩

structure Frame (i : Input) (f : Site i) where
  center : i.certified.TetrahedralCenter
  recognized : i.certified.localizedOccurrenceDescriptorCenter? f = some center
  four : (RingRetainedAuxiliary.frame i.certified f).length = 4
  ids : List Nat
  actualAtoms : (RingRetainedAuxiliary.frame i.certified f).mapM (fun q => q.occurrence.val.node.current?.map Fin.val) = some ids
  physical : ids.Perm (RingRetainedAuxiliary.canonical i.certified center)

def frame? (i : Input) (f : Site i) : Option (Frame i f) := do
  let ⟨c,hc⟩ ← (i.certified.localizedOccurrenceDescriptorCenter? f).attach
  let fs := RingRetainedAuxiliary.frame i.certified f
  if four : fs.length = 4 then
    let ⟨ids,hi⟩ ← (fs.mapM (fun (q : Arm i) => q.occurrence.val.node.current?.map Fin.val)).attach
    if p : ids.Perm (RingRetainedAuxiliary.canonical i.certified c) then return ⟨c,hc,four,ids,hi,p⟩
  none

def Frame.arm {i f} (fr : Frame i f) (k : Slot) : Arm i :=
  (RingRetainedAuxiliary.frame i.certified f).get (Fin.cast fr.four.symm k)

def Frame.atoms {i f} (fr : Frame i f) (slots : List Slot) : List Nat :=
  slots.map fun k => fr.ids.get (Fin.cast (by simpa [RingRetainedAuxiliary.canonical] using fr.physical.length_eq.symm) k)

def Frame.score? {i f} (fr : Frame i f) (read : Reader i) (a b : Slot) : Option Score :=
  (edge? i f (fr.arm a).occurrence (fr.arm b).occurrence read).map Subtype.val

structure Assignment (i : Input) (f : Site i) (read : Reader i) where
  frame : Frame i f
  matrix : Matrix (frame.score? read)
  actual : Ranking matrix false
  reflected : Ranking matrix true
  hand : RS
  mirrorHand : RS
  physical : readback? (inputGeometry i.certified) (frame.atoms actual.slots) = some hand
  mirrorPhysical : readback? (mirror (inputGeometry i.certified)) (frame.atoms reflected.slots) = some mirrorHand

def assign? (i : Input) (f : Site i) (read : Reader i) : Option (Assignment i f read) := do
  let fr ← frame? i f
  let m ← RingActivePairReport.matrix? (fr.score? read)
  let a ← RingActivePairReport.rank? m false
  let b ← RingActivePairReport.rank? m true
  let ⟨h,hh⟩ ← (readback? (inputGeometry i.certified) (fr.atoms a.slots)).attach
  let ⟨k,hk⟩ ← (readback? (mirror (inputGeometry i.certified)) (fr.atoms b.slots)).attach
  return ⟨fr,m,a,b,h,k,hh,hk⟩

/-- Casing obtained from the two ranked physical configurations. The imperative insertion
sort may separately test the number of magnitude-two comparisons it encounters. -/
def label (h k : RS) : LocalizedAuxiliaryLabel := if h = k then .pseudoasymmetric (pseudoRSOfRS h) else .chiral h

def Assignment.labels {i f read} (a : Assignment i f read) : Labels := (label a.hand a.mirrorHand,label a.mirrorHand a.hand)

theorem Assignment.edge {i f read} (o : Assignment i f read) (a b : Slot) (ne : a ≠ b) :
    Edge i f (o.frame.arm a).occurrence (o.frame.arm b).occurrence read (o.matrix.get a b) := by
  obtain ⟨v,_,eqv⟩ := Option.map_eq_some_iff.mp (o.matrix.found a b ne)
  exact eqv ▸ v.property

theorem Assignment.casing {i f read} (a : Assignment i f read) :
    caseFromMirror? (some a.hand) (some a.mirrorHand) = some a.labels.1 ∧
      caseFromMirror? (some a.mirrorHand) (some a.hand) = some a.labels.2 ∧ consistent a.labels = true := by
  cases h : a.hand <;> cases k : a.mirrorHand <;> simp [Assignment.labels,label,caseFromMirror?,consistent,h,k,RS.swap,pseudoRSOfRS]

/-- Molecular certificates for absence at a recognized center. The matrix
case retains the exact signed molecular edges and their active publication reader. -/
inductive Refusal (i : Input) (f : Site i) (read : Reader i) where
  | silent (certificate : RingRetainedSilentPair.Certificate i f)
  | terminals (certificate : RingRetainedTerminalClass.Certificate i f)
  | hydrogen (certificate : RingRetainedProtiumClass.Certificate i f)
  | ordinary (frame : Frame i f) (matrix : Matrix (frame.score? read))
      (certificate : RingOrdinaryPairRefusal.Certificate matrix)

inductive Later (i : Input) (f : Site i) (read : Reader i) where
  | ranked (a : Assignment i f read) (found : assign? i f read = some a)
  | refused (reason : Refusal i f read)

def Later.value {i f read} : Later i f read → Option Labels
  | .ranked a _ => some a.labels
  | .refused _ => none

private def matrixRefusal? (i : Input) (f : Site i) (read : Reader i) : Option (Refusal i f read) := do
  let frame ← frame? i f
  let matrix ← RingActivePairReport.matrix? (frame.score? read)
  return .ordinary frame matrix (← RingOrdinaryPairRefusal.find? matrix)

/-- Positive rows use all directed molecular scores. A failed ranking is retried using
equivalence of terminal ligands, a silent exchange, or a complete single-pair matrix. -/
def later? (i : Input) (f : Site i) (read : Reader i) : Option (Later i f read) :=
  match found : assign? i f read with
  | some a => some (.ranked a found)
  | none => do
    if let some t := RingRetainedTerminalClass.find? i f then return .refused (.terminals t)
    if let some t := RingRetainedProtiumClass.find? i f then return .refused (.hydrogen t)
    if let some p := RingRetainedSilentPair.find? i f then return .refused (.silent p)
    return .refused (← matrixRefusal? i f read)

def publish? (i : Input) (f : Site i) (read : Reader i) : Option (Option Labels) :=
  match RingRetainedAuxiliary.publication? i f with
  | some none => some none
  | some (some s) => some (some (.chiral s,.chiral s.swap))
  | none => (later? i f (masked f read)).map Later.value

theorem publish_congr (i : Input) (f : Site i) {a b : Reader i} (agree : ∀ q, Eligible f q → a q = b q) :
    publish? i f a = publish? i f b := by
  cases h : RingRetainedAuxiliary.publication? i f with
  | some v => cases v <;> simp [publish?,h]
  | none =>
    simp only [publish?,h]
    exact congrArg (fun r : Reader i => (later? i f r).map Later.value) (masked_congr f agree)

theorem publication_source {i f read v} (found : publish? i f read = some (some v)) :
    (∃ s, RingRetainedAuxiliary.read? i f = some s ∧ v = (.chiral s,.chiral s.swap)) ∨
      ∃ a : Assignment i f (masked f read), assign? i f (masked f read) = some a ∧ v = a.labels := by
  cases h : RingRetainedAuxiliary.publication? i f with
  | none =>
    right
    obtain ⟨result,_,out⟩ := Option.map_eq_some_iff.mp (by simpa only [publish?,h] using found)
    cases result with
    | ranked a issued => exact ⟨a,issued,(Option.some.inj out).symm⟩
    | refused w => contradiction
  | some p => cases p with
    | none => simp [publish?,h] at found
    | some s => exact Or.inl ⟨s,RingRetainedAuxiliary.publication_iff.mp h,by simpa [publish?,h,eq_comm] using found⟩

def Absent (i : Input) (f : Site i) (read : Reader i) : Prop :=
  (∀ c, ¬i.certified.RealTetrahedralCenterNode f.val.node c) ∨
    (RingRetainedAuxiliary.publication? i f = none ∧ ∃ w, later? i f (masked f read) = some (.refused w))

theorem absence_source {i f read} : publish? i f read = some none ↔ Absent i f read := by
  unfold Absent
  rw [← RingRetainedAuxiliary.absence_iff i f]
  cases h : RingRetainedAuxiliary.publication? i f with
  | none =>
    cases t : later? i f (masked f read) with
    | none => simp [publish?,h,t]
    | some row => cases row <;> simp [publish?,h,t,Later.value]
  | some p => cases p <;> simp [publish?,h]

theorem later_missing {i f read} (miss : later? i f read = none) : assign? i f read = none := by
  unfold later? at miss
  split at miss
  · contradiction
  · assumption

private theorem eachMap {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (got : xs.mapM f = some ys) : List.Forall₂ (fun x y => f x = some y) xs ys := by
  induction xs generalizing ys with
  | nil => obtain rfl : [] = ys := Option.some.inj got; exact .nil
  | cons x xs ih =>
    rw [List.mapM_cons] at got
    cases h : f x <;> cases t : xs.mapM f <;> simp [h,t] at got
    subst ys
    exact .cons h (ih t)

/-- Bind the coordinate atom of each sorted direction to the very occurrence whose key
was used by the ranker. This includes the old parent when a direction is inward. -/
theorem Frame.point_at {i f} (fr : Frame i f) (k : Slot) :
    (fr.arm k).occurrence.val.node.current?.map Fin.val = some (fr.atoms [k]).head! := by
  have h := (List.forall₂_iff_get.mp (eachMap fr.actualAtoms)).2 k.val
    (by rw [fr.four]; exact k.isLt) (by rw [fr.physical.length_eq]; simp [RingRetainedAuxiliary.canonical])
  exact h

/-- Declarative evidence for a visited node, including frozen absences. The child order is
certified by the atomic or retained constitutional comparison at that occurrence. -/
structure NodeSource (i : Input) (read : Reader i) (q : Arm i) (data : Visit × List (Arm i)) : Prop where
  address : data.1.address = q.occurrence.val.address
  number : RingActivePairs.z? i q = some data.1.z
  state : read q.occurrence = some data.1.publication
  physical : data.1.publication.all consistent = true
  degree : data.1.children = data.2.length
  leaf : data.1.children = 0 → data.1.publication = none
  order : RingRetainedSiblingOrder.Order i q data.2
  shallow : ShallowOrder i read data.2

/-- Paths identify the witness. The comparison itself uses only the molecular fields. -/
def Visit.withoutAddress (v : Visit) : Visit := {v with address := []}

theorem NodeSource.equal_leaves {i read a b x y} (l : NodeSource i read a x)
    (r : NodeSource i read b y) (same : RingRetainedSiblingOrder.SameLeaves i a b) :
    x.2 = [] ∧ y.2 = [] ∧ x.1.withoutAddress = y.1.withoutAddress := by
  have lx : x.2 = [] := List.Perm.eq_nil (same.1 ▸ l.order.complete)
  have ly : y.2 = [] := List.Perm.eq_nil (same.2.1 ▸ r.order.complete)
  have dx : x.1.children = 0 := by simpa only [lx,List.length_nil] using l.degree
  have dy : y.1.children = 0 := by simpa only [ly,List.length_nil] using r.degree
  have z := Option.some.inj (l.number.symm.trans (same.2.2.trans r.number))
  exact ⟨lx,ly,by simp only [Visit.withoutAddress,dx,dy,l.leaf dx,r.leaf dy,z]⟩

private def forgetPaths (ls : List (List Visit)) := ls.map (List.map Visit.withoutAddress)

private theorem forget_descriptors (ls : List (List Visit)) :
    descriptors (forgetPaths ls) = (descriptors ls).map Visit.withoutAddress := by
  cases ls with
  | nil => rfl
  | cons layer layers =>
    simp [descriptors,forgetPaths,List.flatMap_map,List.map_flatMap,List.filter_map,Function.comp_def,Visit.withoutAddress]

/-- Molecular comparisons are unaffected by exchanging the addresses of identical
terminal visits in an arbitrary layer. Their two descendant queues are empty. -/
theorem decide_forget_paths (a b : List (List Visit)) (rev : Bool) :
    decide? (forgetPaths a) (forgetPaths b) rev = decide? a b rev := by
  simp only [decide?,forget_descriptors]
  simp [unitWord,forgetPaths,topology,List.map_map,Function.comp_def,Visit.withoutAddress,Visit.label]
  rfl

theorem decide_of_same_visits {a b x y : List (List Visit)}
    (left : a.map (List.map Visit.withoutAddress) = x.map (List.map Visit.withoutAddress))
    (right : b.map (List.map Visit.withoutAddress) = y.map (List.map Visit.withoutAddress))
    (rev : Bool) : decide? a b rev = decide? x y rev := by
  rw [← decide_forget_paths a b rev, ← decide_forget_paths x y rev]
  exact congrArg₂ (fun l r => decide? l r rev) left right

inductive Walk (i : Input) (read : Reader i) : List (Arm i) → List (List Visit) → Prop where
  | empty : Walk i read [] []
  | layer {q qs data tail} (visits : List.Forall₂ (NodeSource i read) (q::qs) data)
      (below : Walk i read (data.flatMap Prod.snd) tail) : Walk i read (q::qs) (data.map Prod.fst :: tail)

theorem ordered_source (i : Input) (read : Reader i) : ∀ n qs out,
    orderedLevelsWith? i (visit read) n qs = some out → Walk i read qs out
  | 0,[],_,h | _+1,[],_,h => by obtain rfl := Option.some.inj h; exact .empty
  | 0,_::_,_,h => by contradiction
  | n+1,q::qs,out,h => by
    let one (a : Arm i) : Option (Visit × List (Arm i)) := do
      let es ← RingActivePairs.children? i a
      let z ← RingActivePairs.z? i a
      let v ← visit read a z es.length
      return (v,es.map Prod.fst)
    change ((q::qs).mapM one >>= fun data => orderedLevelsWith? i (visit read) n (data.flatMap Prod.snd) >>=
      fun tail => some (data.map Prod.fst :: tail)) = some out at h
    obtain ⟨data,values,tail⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rest,restSource,eqn⟩ := Option.bind_eq_some_iff.mp tail
    obtain rfl := Option.some.inj eqn
    apply Walk.layer _ (ordered_source i read n _ _ restSource)
    apply (eachMap values).imp
    intro x y hy
    dsimp [one] at hy
    obtain ⟨es,he,k⟩ := Option.bind_eq_some_iff.mp hy
    obtain ⟨z,hz,k⟩ := Option.bind_eq_some_iff.mp k
    obtain ⟨v,hv,k⟩ := Option.bind_eq_some_iff.mp k
    obtain rfl := Option.some.inj k
    unfold visit at hv
    cases hread : read x.occurrence with
    | none => simp [hread] at hv
    | some labels =>
      rw [hread] at hv
      change (if labels.all consistent = true ∧ (es.length ≠ 0 ∨ labels.isNone = true) then some (Visit.mk x.occurrence.val.address z es.length labels) else none) = some v at hv
      by_cases ok : labels.all consistent = true ∧ (es.length ≠ 0 ∨ labels.isNone = true)
      · obtain rfl : Visit.mk x.occurrence.val.address z es.length labels = v := by simpa only [if_pos ok,Option.some.injEq] using hv
        have atomic := RingActivePairs.children_source he
        exact ⟨rfl,hz,hread,ok.1,(List.length_map ..).symm,(fun zero => Option.isNone_iff_eq_none.mp (ok.2.resolve_left (not_not_intro zero))),.atomic atomic,atomic.descending.imp Or.inl⟩
      · simp only [if_neg ok,reduceCtorEq] at hv

theorem retained_source (i : Input) (read : Reader i) : ∀ n qs out,
    retainedLevels? i read n qs = some out → Walk i read qs out
  | 0,[],_,h | _+1,[],_,h => by obtain rfl := Option.some.inj h; exact .empty
  | 0,_::_,_,h => by contradiction
  | n+1,q::qs,out,h => by
    let one (a : Arm i) : Option (Visit × List (Arm i)) := do
      let children ← retainedChildren? i read a
      let z ← RingActivePairs.z? i a
      let v ← visit read a z children.val.length
      return (v,children.val)
    change ((q::qs).mapM one >>= fun data => retainedLevels? i read n (data.flatMap Prod.snd) >>=
      fun tail => some (data.map Prod.fst :: tail)) = some out at h
    obtain ⟨data,values,tail⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rest,restSource,eqn⟩ := Option.bind_eq_some_iff.mp tail
    obtain rfl := Option.some.inj eqn
    apply Walk.layer _ (retained_source i read n _ _ restSource)
    apply (eachMap values).imp
    intro x y hy
    dsimp [one] at hy
    obtain ⟨cs,_,k⟩ := Option.bind_eq_some_iff.mp hy
    obtain ⟨z,hz,k⟩ := Option.bind_eq_some_iff.mp k
    obtain ⟨v,hv,k⟩ := Option.bind_eq_some_iff.mp k
    obtain rfl := Option.some.inj k
    unfold visit at hv
    obtain ⟨labels,hread,rest⟩ := Option.bind_eq_some_iff.mp hv
    split at rest
    next ok =>
      obtain rfl := Option.some.inj rest
      exact ⟨rfl,hz,hread,ok.1,rfl,(fun zero => Option.isNone_iff_eq_none.mp (ok.2.resolve_left (not_not_intro zero))),cs.property.1,cs.property.2⟩
    next => contradiction

theorem Pair.source_walks {i f a b read} (p : Pair i f a b read) :
    Walk i read [⟨a,some f⟩] p.left ∧ Walk i read [⟨b,some f⟩] p.right :=
  ⟨retained_source i read _ _ _ p.leftRead,retained_source i read _ _ _ p.rightRead⟩

end TetraStereo.Engine.RingNestedActivePair

assert_kernel_only TetraStereo.Engine.RingNestedActivePair.masked_congr
assert_kernel_only TetraStereo.Engine.RingNestedActivePair.Assignment.edge
assert_kernel_only TetraStereo.Engine.RingNestedActivePair.Assignment.casing
assert_kernel_only TetraStereo.Engine.RingNestedActivePair.publish_congr
assert_kernel_only TetraStereo.Engine.RingNestedActivePair.publication_source
assert_kernel_only TetraStereo.Engine.RingNestedActivePair.absence_source

assert_kernel_only TetraStereo.Engine.RingNestedActivePair.ordered_specializes
assert_kernel_only TetraStereo.Engine.RingNestedActivePair.decide_rule4a_first
assert_kernel_only TetraStereo.Engine.RingNestedActivePair.unit_pair
assert_kernel_only TetraStereo.Engine.RingNestedActivePair.unit_p92
assert_kernel_only TetraStereo.Engine.RingNestedActivePair.signature_projection
assert_kernel_only TetraStereo.Engine.RingNestedActivePair.decide_rule4a
assert_kernel_only TetraStereo.Engine.RingNestedActivePair.lower_pair
assert_kernel_only TetraStereo.Engine.RingNestedActivePair.lower_first_difference
assert_kernel_only TetraStereo.Engine.RingNestedActivePair.decide_rule4c
assert_kernel_only TetraStereo.Engine.RingNestedActivePair.Frame.point_at
assert_kernel_only TetraStereo.Engine.RingNestedActivePair.ordered_source
assert_kernel_only TetraStereo.Engine.RingNestedActivePair.Pair.source_walks

assert_kernel_only TetraStereo.Engine.RingNestedActivePair.shallow_invariant
assert_kernel_only TetraStereo.Engine.RingNestedActivePair.retained_source

assert_kernel_only TetraStereo.Engine.RingNestedActivePair.NodeSource.equal_leaves
assert_kernel_only TetraStereo.Engine.RingNestedActivePair.decide_of_same_visits
