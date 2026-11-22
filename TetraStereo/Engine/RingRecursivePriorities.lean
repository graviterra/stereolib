import TetraStereo.Engine.RingEnantiomorphicArms
import TetraStereo.Engine.RingPairAlternatives
import TetraStereo.Engine.RingReferenceBlocks
import TetraStereo.Engine.RingIsotopePriority

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority.Recursive
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation

/-- The witness proposes a local frame and a correspondence between the two
tied arms. Descriptors and auxiliary orders are computed from the molecule. -/
inductive Stage where | fourB | fourC | five
  deriving DecidableEq, Repr
structure Frame where
  stage : Stage
  outer : Nat
  left : Nat
  right : Nat
  low : Nat
  rename : Nat → Nat
  topPair : Bool

structure Reading where
  actual : RS
  reflected : RS
  deriving DecidableEq, Repr

def Reading.label (r : Reading) := caseFromMirror? (some r.actual) (some r.reflected)
def Reading.reverse (r : Reading) := Reading.mk r.reflected r.actual

def geometric (g : Geometry) (order mirroredOrder : List Nat) : Option Reading := do
  return ⟨← readback? g order,← readback? (mirror g) mirroredOrder⟩

abbrev Facts := List (List Nat × Reading)

/-- Preserve all constitution, geometry-class and descriptor-pair data through
Rule 4b. A coherent flip of all uppercase hands preserves all like/unlike pairs.
At Rule 5 the lowercase descriptors must agree as well. -/
private def earlier (stage : Stage) (flip : Bool) : Option LocalizedAuxiliaryLabel → Nat
  | none => 0
  | some (.chiral h) => if stage == .fourB || (if flip then h.swap else h) == .R then 1 else 2
  | some (.pseudoasymmetric h) => if stage != .five || h == .r then 3 else 4

def inventory (m : RawMolecule) (n : RawMolecule.CanonicalBranchNode) (facts : Facts)
    (stage : Stage) (flip : Bool) (rename : Nat → Nat) :
    Option (List (List Nat × AtomSpec × RawMolecule.CanonicalNodeProvenance × Nat)) := do
  let sites ← earlierSites m [] (m.atomCount+1) n
  return sites.map fun s =>
    let hand := (facts.lookup s.address).bind Reading.label
    (s.address.map rename,s.atom,s.provenance,earlier stage flip hand)

private def signature (stage : Stage) : Option LocalizedAuxiliaryLabel → Option RS
  | some (.chiral h) => if stage == .five then some h else none
  | some (.pseudoasymmetric h) =>
      if stage == .fourC then some (if h = .r then .R else .S) else none
  | none => none

/-- Rule 4b's natural reference and next hand when both occupy uniquely
nearest chiral sites. A tied distance in either required group declines
this method. Later groups cannot affect this first strict decision. -/
def firstPair (facts : Facts) (reverse : Bool) : Option Bool := do
  let hands := facts.filterMap fun (path,r) =>
    match (if reverse then r.reverse.label else r.label) with
    | some (.chiral h) => some (path.length,h)
    | _ => none
  let first :: second :: rest := hands.insertionSort (fun a b => decide (a.1 ≤ b.1)) | none
  guard (first.1 < second.1 && rest.all (fun t => second.1 < t.1))
  return decide (first.2 = second.2)

private def byDistance (sites : List (Nat × RS)) : List (List RS) :=
  let last := sites.foldl (fun n e => max n e.1) 0
  (List.range (last+1)).map fun d => sites.filterMap fun (i,h) => if i = d then some h else none

/-- Chiral occurrence descriptors at each distance in the original digraph. -/
def chiralSpheres (facts : Facts) (reverse : Bool) : List (List RS) :=
  byDistance (facts.filterMap fun (path,r) =>
    match (if reverse then r.reverse.label else r.label) with
    | some (.chiral h) => some (path.length,h)
    | _ => none)

/-- If all candidates in the nearest chiral sphere carry the same hand, any
highest-rank subset gives this reference, regardless of its internal order. -/
def unanimousReference? (rows : List (List RS)) : Option RS := do
  let some (h :: rest) := rows.find? (fun row => !row.isEmpty) | none
  guard (rest.all (· == h))
  return h

def pairSpheres? (facts : Facts) (reverse : Bool) : Option PairSpheres.Layers := do
  let rows := chiralSpheres facts reverse
  let ref ← unanimousReference? rows
  return rows.map fun hands => hands.map (· == ref)

def seniorLeft? (stage : Stage) (ls rs : Facts) (reverse : Bool) : Option Bool := do
  if stage == .fourB then
    return ← PairSpheres.seniorLeft? (← pairSpheres? ls reverse) (← pairSpheres? rs reverse)
  let readings (facts : Facts) :=
    let rows := byDistance (facts.filterMap fun (p,r) =>
      (signature stage (if reverse then r.reverse.label else r.label)).map (p.length,·))
    rows.map fun hs => hs.map (· == .R)
  return ← PairSpheres.seniorLeft? (readings ls) (readings rs)

private def eligibleSites (facts : Facts) (reverse : Bool) : List (List Nat × RS) :=
  facts.filterMap fun (path,r) =>
    match (if reverse then r.reverse.label else r.label) with
    | some (.chiral h) => some (path,h)
    | _ => none

/-- The nearest chiral sphere is a population of addressed occurrences. A
non-unanimous population is counted only after every candidate has the same
complete pointed Rule-4a digraph code. This proves their earlier equivalence. -/
def molecularReferences? (m : RawMolecule) (arm : RawMolecule.CanonicalBranchNode)
    (facts : Facts) (reverse : Bool) : Option (List RS) := do
  let sites := eligibleSites facts reverse
  let d ← (sites.map fun s => s.1.length).min?
  let first :: rest := sites.filter (fun s => s.1.length == d) | none
  if rest.all (fun s => s.2 == first.2) then return [first.2]
  let unit (p : List Nat) := earlier .fourB false ((facts.lookup p).bind Reading.label)
  let code (p : List Nat) := MarkedHierarchy.encode m unit p (m.atomCount+1) arm
  let base ← code first.1
  guard (← rest.allM (fun s => do return (← code s.1) == base))
  return localizedRule4bReferencesFromPopulation ((first :: rest).map Prod.snd)

private def pairLayersFor (rows : List (List RS)) (ref : RS) : PairSpheres.Layers :=
  rows.map fun hands => hands.map (· == ref)

/-- Select the greater complete reference reading independently for each
ligand. An interval tracks uncertainty in the remaining within-sphere ranks. -/
def referenceRange? (refs : List RS) (rows : List (List RS)) : Option PairSpheres.Interval :=
  let run (r : RS) := PairSpheres.referenceInterval (pairLayersFor rows r)
  match refs with
  | [a] => some (run a)
  | [a,b] => some ((run a).best (run b))
  | _ => none

/-- A marked occurrence retains every earlier-rule observation. For Rule 4b
it also retains the pairings already encountered closer to the root. At and
beyond the tested sphere the actual R/S hands have not yet broken ties. -/
def beforePairCode? (m : RawMolecule) (arm : RawMolecule.CanonicalBranchNode)
    (fs : Facts) (reverse : Bool) (ref : RS) (p : List Nat) : Option MarkedHierarchy.Code :=
  let role (q : List Nat) :=
    match (fs.lookup q).bind (fun r => if reverse then r.reverse.label else r.label) with
    | none => 0
    | some (.pseudoasymmetric _) => 1
    | some (.chiral h) => if q.length < p.length then (if h = ref then 3 else 4) else 2
  MarkedHierarchy.encode m role p (m.atomCount+1) arm

abbrev ChiralSite := List Nat × RS

/-- Two chiral sites are the only candidates in this sphere. Equal complete
pointed trees exchange them while preserving earlier classes and every prior
pairing. Like then precedes unlike, including for distinct paths to one atom. -/
def exchangeablePair (m : RawMolecule) (arm : RawMolecule.CanonicalBranchNode)
    (fs : Facts) (reverse : Bool) (ref : RS) : List ChiralSite → Bool
  | [(p,a),(q,b)] => p != q && p.length == q.length && a != b &&
      (beforePairCode? m arm fs reverse ref p).any fun x =>
        beforePairCode? m arm fs reverse ref q == some x
  | _ => false

def sphereSites (fs : Facts) (reverse : Bool) : List (List ChiralSite) :=
  let sites := eligibleSites fs reverse
  let last := sites.foldl (fun n s => max n s.1.length) 0
  (List.range (last+1)).map fun d => sites.filter (fun s => s.1.length == d)

/-- The legal orders of one sphere retain all occurrences. A proved equivalent
pair additionally places its like member first. -/
def PairOrder (exchangeable : Bool) (ref : RS) (sites order : List ChiralSite) : Prop :=
  sites.Perm order ∧ (exchangeable = true →
    (order.map fun s => s.2 == ref).Pairwise (fun a b => b = true → a = true))

/-- The Rule 4b comparison of two otherwise equivalent sites in a two-site
sphere. The same earlier digraph must be obtained by marking either site. -/
def LikeBefore (m : RawMolecule) (arm : RawMolecule.CanonicalBranchNode) (fs : Facts)
    (reverse : Bool) (ref : RS) (a b : ChiralSite) : Prop :=
  a.2 = ref ∧ b.2 ≠ ref ∧ ∃ c, beforePairCode? m arm fs reverse ref a.1 = some c ∧
    beforePairCode? m arm fs reverse ref b.1 = some c

private theorem exchanged_codes {m arm fs reverse ref sites}
    (eqv : exchangeablePair m arm fs reverse ref sites = true) :
    ∃ c, ∀ s ∈ sites, beforePairCode? m arm fs reverse ref s.1 = some c := by
  unfold exchangeablePair at eqv
  split at eqv
  next p a q b =>
    simp only [Bool.and_eq_true] at eqv
    obtain ⟨_,codes⟩ := eqv
    cases left : beforePairCode? m arm fs reverse ref p with
    | none => simp [left] at codes
    | some c =>
      have right : beforePairCode? m arm fs reverse ref q = some c := by simpa [left] using codes
      exact ⟨c,by simp [left,right]⟩
  next => contradiction

/-- Every ordering that respects the strict molecular pair comparisons obeys
the like-first constraint used by the interval proof. -/
theorem pairOrder_of_comparisons {m arm fs reverse ref sites order}
    (complete : sites.Perm order)
    (legal : sites.length = 2 → order.Pairwise (fun a b => ¬ LikeBefore m arm fs reverse ref b a)) :
    PairOrder (exchangeablePair m arm fs reverse ref sites) ref sites order := by
  refine ⟨complete,fun exchanged => ?_⟩
  have two : sites.length = 2 := by
    unfold exchangeablePair at exchanged
    split at exchanged
    · rfl
    · contradiction
  obtain ⟨c,codes⟩ := exchanged_codes exchanged
  apply List.pairwise_map.mpr
  apply (legal two).imp_of_mem
  intro a b ha hb earlier likeB
  by_contra unlikeA
  exact earlier ⟨beq_iff_eq.mp likeB,fun same => unlikeA (beq_iff_eq.mpr same),
    c,codes b (complete.mem_iff.mpr hb),codes a (complete.mem_iff.mpr ha)⟩

private theorem ranked_of_ordered (xs : List Bool)
    (h : xs.Pairwise (fun a b => b = true → a = true)) :
    xs.map Bool.toNat = PairSpheres.upper xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    obtain ⟨head,tail⟩ := List.pairwise_cons.mp h
    cases b with
    | true => simpa [PairSpheres.upper,List.count_cons,List.replicate_succ] using
        congrArg (List.cons 1) (ih tail)
    | false =>
      have absent : true ∉ xs := fun mem => Bool.noConfusion (head true mem rfl)
      simpa [PairSpheres.upper,List.count_cons,List.count_eq_zero.mpr absent,List.replicate_succ]
        using congrArg (List.cons 0) (ih tail)

theorem paired_row_bounds {exchangeable ref sites order} (h : PairOrder exchangeable ref sites order) :
    let bits := sites.map (fun s => s.2 == ref)
    let word := order.map (fun s => (s.2 == ref).toNat)
    (if exchangeable then PairSpheres.upper bits else PairSpheres.lower bits) ≤ word ∧
    word ≤ PairSpheres.upper bits := by
  let bs := order.map (fun s => s.2 == ref)
  have perm := h.1.map (fun s => s.2 == ref)
  have hi : PairSpheres.upper (sites.map (fun s => s.2 == ref)) = PairSpheres.upper bs :=
    by simp only [PairSpheres.upper,bs,perm.count_eq]
  have lo : PairSpheres.lower (sites.map (fun s => s.2 == ref)) = PairSpheres.lower bs :=
    by simp only [PairSpheres.lower,bs,perm.count_eq]
  change (if exchangeable then _ else _) ≤ _ ∧ _ ≤ _
  rw [hi,lo]
  have word : order.map (fun s => (s.2 == ref).toNat) = bs.map Bool.toNat := by simp [bs]
  rw [word]
  cases exchangeable with
  | false => exact ⟨PairSpheres.lower_le _,PairSpheres.le_upper _⟩
  | true => simp [ranked_of_ordered bs (h.2 rfl)]

def pairedRange (m : RawMolecule) (arm : RawMolecule.CanonicalBranchNode)
    (fs : Facts) (reverse : Bool) (ref : RS) : PairSpheres.Interval :=
  let rows := sphereSites fs reverse
  let bits (ss : List ChiralSite) := ss.map (fun s => s.2 == ref)
  ⟨rows.map (fun ss => if exchangeablePair m arm fs reverse ref ss then
    PairSpheres.upper (bits ss) else PairSpheres.lower (bits ss)),
   rows.map (fun ss => PairSpheres.upper (bits ss))⟩

/-- A complete word in any hierarchy respecting the exchanged pairs lies in
the computed interval, with exactly the same molecular paths in each sphere. -/
theorem pairedRange_allows {m arm fs reverse ref orders}
    (h : List.Forall₂ (fun ss order => PairOrder (exchangeablePair m arm fs reverse ref ss)
      ref ss order) (sphereSites fs reverse) orders) :
    (pairedRange m arm fs reverse ref).Allows
      (orders.map (List.map fun s => (s.2 == ref).toNat)) := by
  unfold pairedRange PairSpheres.Interval.Allows
  generalize sphereSites fs reverse = rows at *
  induction h with
  | nil => exact ⟨le_rfl,le_rfl⟩
  | cons head _ ih =>
    obtain ⟨lo,hi⟩ := paired_row_bounds head
    exact ⟨PairSpheres.cons_mono lo ih.1,PairSpheres.cons_mono hi ih.2⟩

/-- Both pieces of hierarchy apply simultaneously, sphere by sphere and
independently for each reference, before comparing alternative readings. -/
def refinedRange (m : RawMolecule) (arm : RawMolecule.CanonicalBranchNode)
    (fs : Facts) (reverse : Bool) (ref : RS) : PairSpheres.Interval :=
  let w := pairedRange m arm fs reverse ref
  let rows := pairLayersFor (chiralSpheres fs reverse) ref
  ⟨PairSpheres.referenceLower rows w.low,w.high⟩

theorem refinedRange_allows {m arm fs reverse ref orders}
    (h : List.Forall₂ (fun ss order => PairOrder (exchangeablePair m arm fs reverse ref ss)
      ref ss order) (sphereSites fs reverse) orders)
    (nearest : PairSpheres.ReferenceOrder (pairLayersFor (chiralSpheres fs reverse) ref)
      (orders.map (List.map fun s => s.2 == ref))) :
    (refinedRange m arm fs reverse ref).Allows
      (orders.map (List.map fun s => (s.2 == ref).toNat)) := by
  have lower : List.Forall₂ (· ≤ ·) (pairedRange m arm fs reverse ref).low
      (orders.map (List.map fun s => (s.2 == ref).toNat)) := by
    clear nearest
    unfold pairedRange
    generalize sphereSites fs reverse = sites at *
    induction h with
    | nil => exact .nil
    | cons head _ ih => exact .cons (paired_row_bounds head).1 ih
  have eqn : PairSpheres.ranks (orders.map (List.map fun s => s.2 == ref)) =
      orders.map (List.map fun s => (s.2 == ref).toNat) := by simp [PairSpheres.ranks,Function.comp_def]
  exact ⟨eqn ▸ PairSpheres.referenceLower_le nearest (eqn ▸ lower),(pairedRange_allows h).2⟩

private def pairedAlternatives? (m : RawMolecule) (arm : RawMolecule.CanonicalBranchNode)
    (fs : Facts) (reverse : Bool) : List RS → Option PairSpheres.Interval
  | [a] => some (refinedRange m arm fs reverse a)
  | [a,b] => some ((refinedRange m arm fs reverse a).best (refinedRange m arm fs reverse b))
  | _ => none

private def unitAt (fs : Facts) (p : List Nat) : Nat :=
  match (fs.lookup p).bind Reading.label with
  | none => 0
  | some (.pseudoasymmetric _) => 1
  | some (.chiral _) => 2

private def likeAt (fs : Facts) (rev : Bool) (ref : RS) (p : List Nat) : Option Bool := do
  let r ← fs.lookup p
  let .chiral h ← (if rev then r.reverse.label else r.label) | none
  return h == ref

def branchPrecedes (m : RawMolecule) (arm : RawMolecule.CanonicalBranchNode) (fs : Facts)
    (reverse : Bool) (ref : Option RS) :=
  ReferenceBlocks.precedes m arm (unitAt fs) (fun p => ref.bind (fun r => likeAt fs reverse r p)) ref.isSome

private def equivalentBlock (code : List Nat → Option MarkedHierarchy.Code) : List ChiralSite → Bool
  | [] => false
  | s :: ss => ss.isEmpty || (code s.1).any fun c => ss.all fun t => code t.1 == some c

private theorem equivalent_codes {code sites} (checked : equivalentBlock code sites = true)
    {a b : ChiralSite} (left : a ∈ sites) (right : b ∈ sites) (different : a ≠ b) :
    ∃ c, code a.1 = some c ∧ code b.1 = some c := by
  cases sites with
  | nil => contradiction
  | cons s ss =>
    cases ss with
    | nil => simp_all
    | cons t ts =>
      cases c : code s.1 with
      | none => simp [equivalentBlock,c] at checked
      | some val =>
        have same : ∀ x ∈ (t :: ts), code x.1 = some val := by
          simpa [equivalentBlock,c] using checked
        have all (x : ChiralSite) (hx : x ∈ s :: t :: ts) : code x.1 = some val := by
          rcases List.mem_cons.mp hx with rfl | below
          · exact c
          · exact same x below
        exact ⟨val,all a left,all b right⟩

/-- The nearest occupied sphere, its molecularly senior equivalence class,
and a proof that the proposed partition respects every cross-block comparison. -/
structure ReferencePopulation (m : RawMolecule) (arm : RawMolecule.CanonicalBranchNode)
    (fs : Facts) (rev : Bool) where
  sites : List ChiralSite
  nearest : (sphereSites fs rev).find? (fun ss => !ss.isEmpty) = some sites
  layout : ReferenceBlocks.Layout (branchPrecedes m arm fs rev none) sites
  members : List ChiralSite
  rest : List (List ChiralSite)
  first : layout.blocks = members :: rest
  equivalent : equivalentBlock (fun p => MarkedHierarchy.encode m (unitAt fs) p (m.atomCount+1) arm)
    members = true

def referencePopulation? (m : RawMolecule) (arm : RawMolecule.CanonicalBranchNode)
    (fs : Facts) (rev : Bool) : Option (ReferencePopulation m arm fs rev) := do
  let ⟨sites,nearest⟩ ← ((sphereSites fs rev).find? (fun ss => !ss.isEmpty)).attach
  let layout ← ReferenceBlocks.layout? (branchPrecedes m arm fs rev none) sites
  match eqn : layout.blocks with
  | top :: rest =>
    if equiv : equivalentBlock (fun p => MarkedHierarchy.encode m (unitAt fs) p (m.atomCount+1) arm)
        top = true then return ⟨sites,nearest,layout,top,rest,eqn,equiv⟩
    else none
  | [] => none

def ReferencePopulation.references {m arm fs rev} (pop : ReferencePopulation m arm fs rev) :=
  localizedRule4bReferencesFromPopulation (pop.members.map Prod.snd)

/-- The actual first class in every legal ordering chooses the same single
or dual reference by the published population rule. -/
theorem ReferencePopulation.invariant {m arm fs rev} (pop : ReferencePopulation m arm fs rev)
    {order} (whole : pop.sites.Perm order)
    (legal : order.Pairwise (fun a b => branchPrecedes m arm fs rev none b a ≠ true)) :
    localizedRule4bReferencesFromPopulation ((order.take pop.members.length).map Prod.snd) =
      pop.references := by
  have perm := (pop.layout.first_class pop.first (ReferenceBlocks.precedes_irrefl _ _ _ _ _) whole legal).map Prod.snd
  simp only [references,localizedRule4bReferencesFromPopulation,List.isEmpty_iff_length_eq_zero,
    perm.length_eq,(perm.filter (· == .S)).length_eq,(perm.filter (· == .R)).length_eq]

theorem ReferencePopulation.same_priorities {m arm fs rev} (pop : ReferencePopulation m arm fs rev)
    {a b} (ha : a ∈ pop.members) (hb : b ∈ pop.members) (ne : a ≠ b) :
    ∃ c, MarkedHierarchy.encode m (unitAt fs) a.1 (m.atomCount+1) arm = some c ∧
      MarkedHierarchy.encode m (unitAt fs) b.1 (m.atomCount+1) arm = some c :=
  equivalent_codes pop.equivalent ha hb ne

theorem ReferencePopulation.exchange {m arm fs rev} (pop : ReferencePopulation m arm fs rev)
    {a b} (ha : a ∈ pop.members) (hb : b ∈ pop.members) (ne : a ≠ b) :
    MarkedHierarchy.Isomorphic m m (unitAt fs) (unitAt fs) a.1 b.1 (m.atomCount+1) arm arm := by
  obtain ⟨_,left,right⟩ := pop.same_priorities ha hb ne
  exact MarkedHierarchy.isomorphic_of_code left right

/-- Complete source order of a sphere. Established parent preferences are
retained, and like precedes unlike among sites with the same prior digraph. -/
def RankedOrder (m : RawMolecule) (arm : RawMolecule.CanonicalBranchNode) (fs : Facts)
    (rev : Bool) (ref : RS) (sites order : List ChiralSite) : Prop :=
  sites.Perm order ∧ order.Pairwise (fun a b => branchPrecedes m arm fs rev (some ref) b a ≠ true) ∧
    order.Pairwise (fun a b => ¬ LikeBefore m arm fs rev ref b a)

private def likeEarlier (m : RawMolecule) (arm : RawMolecule.CanonicalBranchNode)
    (fs : Facts) (rev : Bool) (ref : RS) (a b : ChiralSite) : Bool :=
  a.2 == ref && b.2 != ref && (beforePairCode? m arm fs rev ref a.1).any
    (fun c => beforePairCode? m arm fs rev ref b.1 == some c)

private theorem likeEarlier_of_comparison {m arm fs rev ref a b}
    (h : LikeBefore m arm fs rev ref a b) : likeEarlier m arm fs rev ref a b = true := by
  obtain ⟨aLike,bUnlike,c,ca,cb⟩ := h
  simp [likeEarlier,aLike,bUnlike,ca,cb]

/-- Exhibit a complete legal linearization before using any bounds. The
candidate sorter may encounter incomparable sites, so its output is checked
against every molecular precedence and like/unlike comparison. -/
def rankedOrder? (m : RawMolecule) (arm : RawMolecule.CanonicalBranchNode)
    (fs : Facts) (rev : Bool) (ref : RS) (sites : List ChiralSite) :
    Option {order // RankedOrder m arm fs rev ref sites order} := do
  let permutes (a b : ChiralSite) := !(branchPrecedes m arm fs rev (some ref) b a ||
    likeEarlier m arm fs rev ref b a)
  let order := sites.insertionSort (fun a b => permutes a b = true)
  if h : order.Pairwise (fun a b => permutes a b = true) then
    return ⟨order,(List.perm_insertionSort _ _).symm,
      h.imp (by intro a b keep high; simp [permutes,high] at keep),
      h.imp (by intro a b keep opposite; simp [permutes,likeEarlier_of_comparison opposite] at keep)⟩
  none

private def locked (m : RawMolecule) (arm : RawMolecule.CanonicalBranchNode) (fs : Facts)
    (rev : Bool) (ref : RS) := equivalentBlock (beforePairCode? m arm fs rev ref)

private theorem block_ordered {m arm fs rev ref sites order}
    (perm : sites.Perm order) (legal : order.Pairwise (fun a b => ¬ LikeBefore m arm fs rev ref b a)) :
    ReferenceBlocks.OrderedBlock (locked m arm fs rev ref) ref sites order := by
  refine ⟨perm,fun checked => ?_⟩
  have sorted : (order.map fun s => s.2 == ref).Pairwise (fun a b => b = true → a = true) := by
    apply List.pairwise_map.mpr
    apply legal.imp_of_mem
    intro a b ha hb earlier likeB
    by_contra unlikeA
    have ne : b ≠ a := by rintro rfl; exact unlikeA likeB
    obtain ⟨c,cb,ca⟩ := equivalent_codes checked (perm.mem_iff.mpr hb) (perm.mem_iff.mpr ha) ne
    exact earlier ⟨beq_iff_eq.mp likeB,fun same => unlikeA (beq_iff_eq.mpr same),c,cb,ca⟩
  have counts := perm.map fun s => s.2 == ref
  change (order.map (fun s => s.2 == ref)).map Bool.toNat = PairSpheres.upper _
  rw [ranked_of_ordered _ sorted]
  simp only [PairSpheres.upper,counts.count_eq,ReferenceBlocks.bits]

private theorem parts_ordered {m arm fs rev ref blocks parts}
    (h : List.Forall₂ List.Perm blocks parts)
    (all : parts.flatten.Pairwise (fun a b => ¬ LikeBefore m arm fs rev ref b a)) :
    List.Forall₂ (ReferenceBlocks.OrderedBlock (locked m arm fs rev ref) ref) blocks parts := by
  induction h with
  | nil => exact .nil
  | cons head _ tail =>
    obtain ⟨front,back,_⟩ := List.pairwise_append.mp all
    exact .cons (block_ordered head front) (tail back)

def rankedSphere? (m : RawMolecule) (arm : RawMolecule.CanonicalBranchNode) (fs : Facts)
    (rev : Bool) (ref : RS) (sites : List ChiralSite) : Option (List Nat × List Nat) := do
  guard (rankedOrder? m arm fs rev ref sites).isSome
  let plan ← ReferenceBlocks.layout? (branchPrecedes m arm fs rev (some ref)) sites
  return ReferenceBlocks.bounds (locked m arm fs rev ref) ref plan.blocks

theorem rankedSphere_bounds {m arm fs rev ref sites order bounds}
    (found : rankedSphere? m arm fs rev ref sites = some bounds)
    (law : RankedOrder m arm fs rev ref sites order) :
    let word := order.map (fun s => (s.2 == ref).toNat)
    bounds.1 ≤ word ∧ word ≤ bounds.2 := by
  unfold rankedSphere? at found
  by_cases existsOrder : (rankedOrder? m arm fs rev ref sites).isSome = true
  swap
  · simp [existsOrder] at found
  simp only [existsOrder,guard,if_true,pure_bind] at found
  cases h : ReferenceBlocks.layout? (branchPrecedes m arm fs rev (some ref)) sites with
  | none => simp [h] at found
  | some plan =>
    simp [h] at found
    subst bounds
    obtain ⟨parts,perms,eqn⟩ := plan.linearize (ReferenceBlocks.precedes_irrefl _ _ _ _ _) law.1 law.2.1
    have bound := ReferenceBlocks.bounds_sound (parts_ordered perms (eqn ▸ law.2.2))
    simpa only [ReferenceBlocks.bits,List.map_map,Function.comp_def,eqn] using bound

def rankedRange? (m : RawMolecule) (arm : RawMolecule.CanonicalBranchNode) (fs : Facts)
    (rev : Bool) (ref : RS) : Option PairSpheres.Interval := do
  let rs ← (sphereSites fs rev).mapM (rankedSphere? m arm fs rev ref)
  return ⟨rs.map Prod.fst,rs.map Prod.snd⟩

theorem rankedRange_allows {m arm fs rev ref bounds orders}
    (found : rankedRange? m arm fs rev ref = some bounds)
    (legal : List.Forall₂ (RankedOrder m arm fs rev ref) (sphereSites fs rev) orders) :
    bounds.Allows (orders.map (List.map fun s => (s.2 == ref).toNat)) := by
  unfold rankedRange? at found
  cases h : (sphereSites fs rev).mapM (rankedSphere? m arm fs rev ref) with
  | none => simp [h] at found
  | some rows =>
    simp [h] at found
    subst bounds
    generalize sphereSites fs rev = sites at *
    induction legal generalizing rows with
    | nil => simp at h; subst rows; exact ⟨le_rfl,le_rfl⟩
    | @cons a b tail rest head _ ih =>
      cases first : rankedSphere? m arm fs rev ref a with
      | none => simp [List.mapM_cons,first] at h
      | some row =>
        cases after : tail.mapM (rankedSphere? m arm fs rev ref) with
        | none => simp [List.mapM_cons,first,after] at h
        | some other =>
          simp [List.mapM_cons,first,after] at h
          subst rows
          obtain ⟨lo,hi⟩ := rankedSphere_bounds first head
          obtain ⟨tailLo,tailHi⟩ := ih other after
          exact ⟨PairSpheres.cons_mono lo tailLo,PairSpheres.cons_mono hi tailHi⟩

def ReferencePopulation.range? {m arm fs rev} (pop : ReferencePopulation m arm fs rev) :
    Option PairSpheres.Interval := do
  match pop.references with
  | [a] => rankedRange? m arm fs rev a
  | [a,b] => return (← rankedRange? m arm fs rev a).best (← rankedRange? m arm fs rev b)
  | _ => none

def rankedArm? (m : RawMolecule) (arm : RawMolecule.CanonicalBranchNode) (fs : Facts)
    (rev : Bool) : Option (List RS × PairSpheres.Interval) := do
  let pop ← referencePopulation? m arm fs rev
  return (pop.references,← pop.range?)

/-- An actual complete reading for one molecular reference. The lists of
sites and their ranks come from the exact occurrence inventories. -/
def LegalWord (m : RawMolecule) (arm : RawMolecule.CanonicalBranchNode)
    (fs : Facts) (rev : Bool) (ref : RS) (w : PairSpheres.Word) : Prop :=
  ∃ orders, List.Forall₂ (RankedOrder m arm fs rev ref) (sphereSites fs rev) orders ∧
    orders.map (List.map fun s => (s.2 == ref).toNat) = w

private theorem range_is_inhabited {m arm fs rev ref bounds}
    (found : rankedRange? m arm fs rev ref = some bounds) :
    ∃ w, LegalWord m arm fs rev ref w := by
  unfold rankedRange? at found
  cases h : (sphereSites fs rev).mapM (rankedSphere? m arm fs rev ref) with
  | none => simp [h] at found
  | some rows =>
    suffices ∃ orders, List.Forall₂ (RankedOrder m arm fs rev ref) (sphereSites fs rev) orders by
      obtain ⟨orders,legal⟩ := this
      exact ⟨_,orders,legal,rfl⟩
    clear found
    generalize sphereSites fs rev = sites at *
    induction sites generalizing rows with
    | nil => exact ⟨[],.nil⟩
    | cons a tail ih =>
      cases first : rankedSphere? m arm fs rev ref a with
      | none => simp [List.mapM_cons,first] at h
      | some row =>
        cases other : tail.mapM (rankedSphere? m arm fs rev ref) with
        | none => simp [List.mapM_cons,first,other] at h
        | some rs =>
          obtain ⟨orders,rest⟩ := ih _ other
          cases checked : rankedOrder? m arm fs rev ref a with
          | none => simp [rankedSphere?,checked] at first
          | some witness => exact ⟨witness.val :: orders,.cons witness.property rest⟩

inductive BestWord (m : RawMolecule) (arm : RawMolecule.CanonicalBranchNode) (fs : Facts)
    (rev : Bool) : List RS → PairSpheres.Word → Prop where
  | single {r x} : LegalWord m arm fs rev r x → BestWord m arm fs rev [r] x
  | dual {r s x y} : LegalWord m arm fs rev r x → LegalWord m arm fs rev s y →
      BestWord m arm fs rev [r,s] (max x y)

private theorem within {m arm fs rev ref bounds word}
    (range : rankedRange? m arm fs rev ref = some bounds) (legal : LegalWord m arm fs rev ref word) :
    bounds.Allows word := by
  obtain ⟨_,order,rfl⟩ := legal
  exact rankedRange_allows range order

/-- The chosen references admit an actual complete reading, and the bounds
contain every possible reading, including the maximum over dual alternatives. -/
theorem rankedArm_sound {m arm fs rev refs bounds}
    (accepted : rankedArm? m arm fs rev = some (refs,bounds)) :
    (∃ w, BestWord m arm fs rev refs w) ∧
      ∀ w, BestWord m arm fs rev refs w → bounds.Allows w := by
  cases pop : referencePopulation? m arm fs rev with
  | none => simp [rankedArm?,pop] at accepted
  | some p =>
    cases range : p.range? with
    | none => simp [rankedArm?,pop,range] at accepted
    | some x =>
      simp [rankedArm?,pop,range] at accepted
      obtain ⟨rfl,rfl⟩ := accepted
      unfold ReferencePopulation.range? at range
      split at range
      next a eqn =>
        rw [eqn]
        obtain ⟨v,hv⟩ := range_is_inhabited range
        exact ⟨⟨_,.single hv⟩,fun _ hs => by cases hs with | single h => exact within range h⟩
      next a b eqn =>
        rw [eqn]
        cases ha : rankedRange? m arm fs rev a with
        | none => simp [ha] at range
        | some ba =>
          cases hb : rankedRange? m arm fs rev b with
          | none => simp [ha,hb] at range
          | some bb =>
            simp [ha,hb] at range
            subst x
            obtain ⟨vx,hx⟩ := range_is_inhabited ha
            obtain ⟨vy,hy⟩ := range_is_inhabited hb
            exact ⟨⟨_,.dual hx hy⟩,fun _ hs => by
              cases hs with | dual l r => exact PairSpheres.Interval.best_allows (within ha l) (within hb r)⟩
      next => contradiction

/-- Rule 4b orders one reference ahead of two. For equally many references,
compare the two independently maximized, complete site words. -/
def rankedDecision? (left right : List RS) (a b : PairSpheres.Interval) : Option Ordering :=
  if left.length < right.length then some .gt
  else if right.length < left.length then some .lt
  else a.compare? b

def RankResult (left right : List RS) (a b : PairSpheres.Word) (o : Ordering) : Prop :=
  match o with
  | .gt => left.length < right.length ∨ (left.length = right.length ∧ b < a)
  | .lt => right.length < left.length ∨ (left.length = right.length ∧ a < b)
  | .eq => left.length = right.length ∧ a = b

/-- The decision is meaningful on both arms and holds for every legal pair
of readings. An exact equality and overlapping, unresolved bounds have
different executable outcomes. -/
theorem rankedDecision_sound {m ln rn ls rs rev left right a b o}
    (l : rankedArm? m ln ls rev = some (left,a)) (r : rankedArm? m rn rs rev = some (right,b))
    (found : rankedDecision? left right a b = some o) :
    (∃ x y, BestWord m ln ls rev left x ∧ BestWord m rn rs rev right y) ∧
    ∀ x y, BestWord m ln ls rev left x → BestWord m rn rs rev right y → RankResult left right x y o := by
  obtain ⟨⟨x,hx⟩,la⟩ := rankedArm_sound l
  obtain ⟨⟨y,hy⟩,ra⟩ := rankedArm_sound r
  refine ⟨⟨x,y,hx,hy⟩,fun u v lu rv => ?_⟩
  unfold rankedDecision? at found
  split at found
  · cases found; exact .inl ‹_›
  · split at found
    · cases found; exact .inl ‹_›
    · have len : left.length = right.length := by omega
      have decision := PairSpheres.Interval.decision (la u lu) (ra v rv) found
      cases o with
      | eq => exact ⟨len,decision⟩
      | lt => exact .inr ⟨len,decision⟩
      | gt => exact .inr ⟨len,decision⟩

private def compareRanked? (m : RawMolecule) (ln rn : RawMolecule.CanonicalBranchNode)
    (ls rs : Facts) (rev : Bool) : Option Bool := do
  let (left,a) ← rankedArm? m ln ls rev
  let (right,b) ← rankedArm? m rn rs rev
  if left.length == right.length then
    guard ((sphereSites ls rev).map List.length == (sphereSites rs rev).map List.length)
  match ← rankedDecision? left right a b with
  | .lt => return false
  | .gt => return true
  | .eq => none

/-- P-92.5.2.1 gives a single reference precedence over two. Hanson et al.,
Figure 8, compare the best complete readings when both have two. -/
private def sphereSeniorLeft? (m : RawMolecule) (ln rn : RawMolecule.CanonicalBranchNode)
    (stage : Stage) (ls rs : Facts) (reverse : Bool) : Option Bool := do
  if stage != .fourB then return ← seniorLeft? stage ls rs reverse
  let left ← molecularReferences? m ln ls reverse
  let right ← molecularReferences? m rn rs reverse
  if left.length != right.length then return left.length < right.length
  let l := chiralSpheres ls reverse
  let r := chiralSpheres rs reverse
  guard (l.map List.length == r.map List.length)
  let a ← referenceRange? left l
  let b ← referenceRange? right r
  match a.compare? b with
  | some .lt => return false
  | some .gt => return true
  | some .eq => none
  | none =>
    let x ← pairedAlternatives? m ln ls reverse left
    let y ← pairedAlternatives? m rn rs reverse right
    match ← x.compare? y with
    | .lt => return false
    | .gt => return true
    | .eq => none

/-- Use independent molecular parent ranks when a distance-only comparison
cannot select a reference or separate the two complete readings. -/
def molecularSeniorLeft? (m : RawMolecule) (ln rn : RawMolecule.CanonicalBranchNode)
    (stage : Stage) (ls rs : Facts) (reverse : Bool) : Option Bool :=
  (sphereSeniorLeft? m ln rn stage ls rs reverse).orElse fun _ =>
    if stage == .fourB then compareRanked? m ln rn ls rs reverse else none

def Frame.order (f : Frame) (leftSenior : Bool) :=
  let (a,b) := if leftSenior then (f.left,f.right) else (f.right,f.left)
  if f.topPair then [a,b,f.outer,f.low] else [f.outer,a,b,f.low]

/-- Bind a proposed comparison to the retained incident cursors. The two outer
positions must already be separated from the middle group by Rule 1a. -/
def frameOK (m : RawMolecule) (path : List Nat) (depth : Nat) (f : Frame) : Bool := Id.run do
  let some n := occurrence? m path | return false
  let frame := [f.outer,f.left,f.right,f.low]
  if !(decide (frame.Perm ((occurrenceLigandCursors m n).map (·.node.atom))) && decide frame.Nodup) then
    return false
  let some [hi,l,r,lo] := frame.mapM (fun i => ligandRows? m path i depth) | return false
  return if f.topPair then decide (l = r ∧ r > hi ∧ hi > lo) else decide (hi > l ∧ l = r ∧ r > lo)

/-- A verified step that outranks one branch using a stereochemical rule.
All lower-rule inventories, both selections and both volume readings must
agree with the witnesses. -/
inductive Supported (m : RawMolecule) (g : Geometry) : List Nat → Reading → Prop where
  | atomic {depth path order r} :
    atomicOrder? m path depth = some order → geometric g order order = some r →
    Supported m g path r
  | ranked {path depth r} (ranking : AtomicRanking m path depth) :
    geometric g (ranking.arms.map (·.cursor.node.atom)) (ranking.arms.map (·.cursor.node.atom)) = some r →
    Supported m g path r
  | isotopic {path r} (ranking : IsotopePriority.Ranking m path) :
    geometric g ranking.order ranking.order = some r → Supported m g path r
  | stereo {depth path r} (f : Frame) {ln rn ls rs} :
    frameOK m path depth f = true →
    occurrence? m (path ++ [f.left]) = some ln → occurrence? m (path ++ [f.right]) = some rn →
    carbonSites m (m.atomCount+1) ln = some (ls.map Prod.fst) →
    carbonSites m (m.atomCount+1) rn = some (rs.map Prod.fst) →
    (∀ x ∈ ls, Supported m g x.1 x.2) → (∀ x ∈ rs, Supported m g x.1 x.2) →
    (∃ flip a b, inventory m ln ls f.stage flip f.rename = some a ∧
      inventory m rn rs f.stage false id = some b ∧ a.Perm b) →
    (∃ x y, molecularSeniorLeft? m ln rn f.stage ls rs false = some x ∧ molecularSeniorLeft? m ln rn f.stage ls rs true = some y ∧
      geometric g (f.order x) (f.order y) = some r) →
    Supported m g path r

/-- A shared tree comparison yields the same molecular priority witness as
a directly computed strict ranking, including all incident ligand cursors. -/
theorem supported_of_shapes {m g path order depth shapes r}
    (found : (checkedShapes? m path order depth).map Subtype.val = some shapes)
    (strict : shapes.Pairwise (fun a b => Certificate.CanonicalSphereKey.ckey 3 depth b <
      Certificate.CanonicalSphereKey.ckey 3 depth a)) (read : geometric g order order = some r) :
    Supported m g path r := by
  obtain ⟨⟨_,build⟩,_,rfl⟩ := Option.map_eq_some_iff.mp found
  obtain ⟨ranking,eq⟩ := build strict
  exact .ranked ranking (eq ▸ read)

private def collect {P : List Nat → Reading → Prop}
    (deriveSite : (q : List Nat) → Option {r // P q r}) :
    (qs : List (List Nat)) → Option {fs : Facts // fs.map Prod.fst = qs ∧ ∀ x ∈ fs, P x.1 x.2}
  | [] => some ⟨[],rfl,by simp⟩
  | q :: qs => do
    let ⟨r,hr⟩ ← deriveSite q
    let ⟨rest,keys,valid⟩ ← collect deriveSite qs
    return ⟨(q,r) :: rest,by simp [keys],by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | tail
      · exact hr
      · exact valid x tail⟩

def agree? (m : RawMolecule) (f : Frame) (ln rn : RawMolecule.CanonicalBranchNode)
    (ls rs : Facts) : Option (PLift (∃ flip a b, inventory m ln ls f.stage flip f.rename = some a ∧
      inventory m rn rs f.stage false id = some b ∧ a.Perm b)) := do
  let ⟨b,rb⟩ ← (inventory m rn rs f.stage false id).attach
  let ⟨a,la⟩ ← (inventory m ln ls f.stage false f.rename).attach
  if h : a.Perm b then return ⟨false,a,b,la,rb,h⟩
  let ⟨v,lv⟩ ← (inventory m ln ls f.stage true f.rename).attach
  if h : v.Perm b then return ⟨true,v,b,lv,rb,h⟩
  none

/-- The two priority decisions are independent of the final volume. A
witness applies to any geometry realizing all of its child readings. -/
abbrev PriorityWitness (m : RawMolecule) (p : List Nat) (f : Frame) (ls rs : Facts) :=
  {wins : Bool × Bool // ∀ g r, (∀ x ∈ ls, Supported m g x.1 x.2) →
    (∀ x ∈ rs, Supported m g x.1 x.2) →
    geometric g (f.order wins.1) (f.order wins.2) = some r → Supported m g p r}

/-- Finish one local step once the complete two lists of child occurrences
have been found. The resulting proof consumes exactly those child derivations. -/
private def priorityWithNodes? (m : RawMolecule) (path : List Nat) (depth : Nat)
    (f : Frame) (ok : frameOK m path depth f = true) {ln rn : RawMolecule.CanonicalBranchNode}
    (lc : occurrence? m (path ++ [f.left]) = some ln) (rc : occurrence? m (path ++ [f.right]) = some rn)
    (ls rs : Facts) (lk : carbonSites m (m.atomCount+1) ln = some (ls.map Prod.fst))
    (rk : carbonSites m (m.atomCount+1) rn = some (rs.map Prod.fst)) :
    Option (PriorityWitness m path f ls rs) := do
  let ⟨agree⟩ ← agree? m f ln rn ls rs
  let ⟨x,hx⟩ ← (molecularSeniorLeft? m ln rn f.stage ls rs false).attach
  let ⟨y,hy⟩ ← (molecularSeniorLeft? m ln rn f.stage ls rs true).attach
  return ⟨(x,y),fun _ _ lh rh read => .stereo f ok lc rc lk rk lh rh agree ⟨x,y,hx,hy,read⟩⟩

/-- Replay one local certificate independently of any recursion schedule.
Successful verification leaves the chemical proofs of the child readings as
explicit premises; a cached or externally supplied letter cannot discharge them. -/
def priorityStep? (m : RawMolecule) (path : List Nat) (depth : Nat)
    (f : Frame) (ls rs : Facts) :
    Option (PriorityWitness m path f ls rs) := do
  if ok : frameOK m path depth f = true then
    let ⟨ln,lc⟩ ← (occurrence? m (path ++ [f.left])).attach
    let ⟨rn,rc⟩ ← (occurrence? m (path ++ [f.right])).attach
    if lk : carbonSites m (m.atomCount+1) ln = some (ls.map Prod.fst) then
      if rk : carbonSites m (m.atomCount+1) rn = some (rs.map Prod.fst) then
        return ← priorityWithNodes? m path depth f ok lc rc ls rs lk rk
  none

private def readPriority? {m p f ls rs} (g : Geometry) (cert : PriorityWitness m p f ls rs) :
    Option {r // (∀ x ∈ ls, Supported m g x.1 x.2) →
      (∀ x ∈ rs, Supported m g x.1 x.2) → Supported m g p r} := do
  let ⟨r,h⟩ ← (geometric g (f.order cert.val.1) (f.order cert.val.2)).attach
  return ⟨r,fun l s => cert.property g r l s h⟩

def step? (m : RawMolecule) (g : Geometry) (path : List Nat) (depth : Nat)
    (f : Frame) (ls rs : Facts) :=
  (priorityStep? m path depth f ls rs).bind (readPriority? g)

theorem supported_of_priorities {m p d f ls rs wins g r}
    (checked : (priorityStep? m p d f ls rs).map Subtype.val = some wins)
    (left : ∀ x ∈ ls, Supported m g x.1 x.2) (right : ∀ x ∈ rs, Supported m g x.1 x.2)
    (read : geometric g (f.order wins.1) (f.order wins.2) = some r) : Supported m g p r := by
  obtain ⟨⟨_,h⟩,_,rfl⟩ := Option.map_eq_some_iff.mp checked
  exact h g r left right read

theorem supported_of_step {m g path depth f ls rs r}
    (ok : (step? m g path depth f ls rs).map Subtype.val = some r)
    (left : ∀ x ∈ ls, Supported m g x.1 x.2) (right : ∀ x ∈ rs, Supported m g x.1 x.2) :
    Supported m g path r := by
  obtain ⟨⟨_,h⟩,_,rfl⟩ := Option.map_eq_some_iff.mp ok
  exact h left right

/-- Find a strict molecular order before consulting a stereochemical frame.
The isotope pass compares the entire earlier constitution of the tied arms.
Both geometry readings use the same certified order. -/
def constitutionalOrder? (m : RawMolecule) (path : List Nat) (depth : Nat) :
    Option {order : List Nat // ∀ g r, geometric g order order = some r → Supported m g path r} := do
  if found : (atomicOrder? m path depth).isSome then
    let order := (atomicOrder? m path depth).get found
    return ⟨order,fun _ _ read => .atomic (Option.some_get _).symm read⟩
  let ranking ← IsotopePriority.rank? m path
  return ⟨ranking.order,fun _ _ read => .isotopic ranking read⟩

/-- Every strict constitutional assignment, including an isotope-resolved
auxiliary, has opposite hands on reflection and takes its uppercase letter
from the actual volume reading. -/
theorem constitutional_casing {g : Geometry} {order : List Nat} {r : Reading}
    (computed : geometric g order order = some r) :
    readback? g order = some r.actual ∧ r.reflected = r.actual.swap ∧
      r.label = some (.chiral r.actual) := by
  cases actual : readback? g order with
  | none => simp [geometric,actual] at computed
  | some hand =>
    simp [geometric,readback_mirror,actual] at computed
    subst r
    exact ⟨rfl,rfl,caseFromMirror?_eq_swap hand⟩

/-- Finite derivation from constitutional leaves. Each successfully derived
child is bound to a discovered address. The proof relation mentions neither a
hint oracle nor the recursion budget. -/
def derive (m : RawMolecule) (g : Geometry) (hint : List Nat → Option Frame)
    (radius : List Nat → Nat) : Nat → (path : List Nat) → Option {r // Supported m g path r}
  | 0,_ => none
  | fuel+1,path => do
    let depth := radius path
    match constitutionalOrder? m path depth with
    | some ⟨order,supported⟩ =>
      let ⟨r,read⟩ ← (geometric g order order).attach
      return ⟨r,supported g r read⟩
    | none =>
      let f ← hint path
      if ok : frameOK m path depth f = true then
        let ⟨ln,lc⟩ ← (occurrence? m (path ++ [f.left])).attach
        let ⟨rn,rc⟩ ← (occurrence? m (path ++ [f.right])).attach
        let ⟨lp,leq⟩ ← (carbonSites m (m.atomCount+1) ln).attach
        let ⟨rp,req⟩ ← (carbonSites m (m.atomCount+1) rn).attach
        let ⟨ls,lk,lh⟩ ← collect (derive m g hint radius fuel) lp
        let ⟨rs,rk,rh⟩ ← collect (derive m g hint radius fuel) rp
        let cert ← priorityWithNodes? m path depth f ok lc rc ls rs (lk.symm ▸ leq) (rk.symm ▸ req)
        let ⟨r,finish⟩ ← readPriority? g cert
        return ⟨r,finish lh rh⟩
      else none

def certify (m : RawMolecule) (g : Geometry) (hint : List Nat → Option Frame)
    (radius : List Nat → Nat) (fuel : Nat) (path : List Nat) :
    Option {r // saturatedCHO m = true ∧ Supported m g path r} := do
  if valid : saturatedCHO m = true then
    let ⟨r,h⟩ ← derive m g hint radius fuel path
    return ⟨r,valid,h⟩
  else none

/-- The same derivations with a checked domain also admitting terminal halogens. -/
def certifyHalogenated (m : RawMolecule) (g : Geometry) (hint : List Nat → Option Frame)
    (radius : List Nat → Nat) (fuel : Nat) (path : List Nat) :
    Option {r // saturatedWithHalogens m = true ∧ Supported m g path r} := do
  if valid : saturatedWithHalogens m = true then
    let ⟨r,h⟩ ← derive m g hint radius fuel path
    return ⟨r,valid,h⟩
  else none

def evaluate (m : RawMolecule) (g : Geometry) (hint : List Nat → Option Frame)
    (depth fuel : Nat) (path : List Nat) : Option Reading :=
  (certify m g hint (fun _ => depth) fuel path).map Subtype.val

end TetraStereo.Engine.RingChemicalPriority.Recursive
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Recursive.certify
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Recursive.evaluate
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Recursive.supported_of_step
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Recursive.certifyHalogenated
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Recursive.supported_of_shapes
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Recursive.supported_of_priorities
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Recursive.pairedRange_allows
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Recursive.refinedRange_allows
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Recursive.ReferencePopulation.invariant
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Recursive.rankedRange_allows
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Recursive.rankedArm_sound
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Recursive.rankedDecision_sound
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Recursive.ReferencePopulation.exchange
