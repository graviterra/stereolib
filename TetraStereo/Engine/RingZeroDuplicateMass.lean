import TetraStereo.Engine.RingMassDifference

/-! # Rebuilding ring priorities with zero mass at closure duplicates -/

set_option autoImplicit false

namespace TetraStereo.Engine.RingZeroDuplicateMass
open OneCenter RingRetainedChemicalTrace RingMassDifference
open RingRetainedConstitution (Cursor)
open LocalizedChemicalRing (Input)
open RingChildKeyRecovery (interleave)

/-- The duplicate keeps its element and closure priority. Its mass is zero
regardless of the isotope on the atom that closed the ring. -/
private def zero (o : Observation) : Observation :=
  ⟨o.atomic, o.duplicate, if o.duplicate = 0 then o.mass else 0⟩

/-- Read a closure directly without an ordinary-mass lookup. The real-atom
branch uses the original isotope reader. -/
def read? (i : Input) {d : Nat} (q : Cursor i.certified d) (terminal : Bool) : Option Observation :=
  let node := q.occurrence.val.node
  match node.provenance with
  | .ringDuplicate origin => do
    let a ← node.current?
    let recd ← i.molecule.atoms[a.val]?
    let z := recd.element.atomicNumber
    guard (z > 0)
    guard (terminal && origin ≤ i.molecule.atomCount && node.history.head? == some a &&
      node.history.tail.reverse.idxOf a == origin && node.history.tail.contains a)
    return ⟨z,duplicateValue i.molecule.atomCount (some origin),0⟩
  | _ => observation? i q terminal

private theorem read_zero {i : Input} {d : Nat} {q : Cursor i.certified d} {t o}
    (read : observation? i q t = some o) : read? i q t = some (zero o) := by
  have kind := observation_kind read
  have raw := read
  unfold observation? at raw
  obtain ⟨a,ha,tail⟩ := Option.bind_eq_some_iff.mp raw
  obtain ⟨rec,hr,tail⟩ := Option.bind_eq_some_iff.mp tail
  obtain ⟨_,hz,tail⟩ := Option.bind_eq_some_iff.mp tail
  cases prov : q.occurrence.val.node.provenance <;> simp only [prov] at tail <;> try contradiction
  case realAtom =>
    have flag := (real_source prov read).1
    have same : zero o = o := by cases o; simp_all [zero]
    simpa only [read?,prov,same] using read
  case ringDuplicate n =>
    obtain ⟨_,hg,tail⟩ := Option.bind_eq_some_iff.mp tail
    obtain ⟨_,_,out⟩ := Option.bind_eq_some_iff.mp tail
    cases Option.some.inj out
    rcases kind with ⟨cl,_⟩ | ⟨pos,_⟩
    · simp [prov] at cl
    · simp [guard] at hz hg
      simp_all [read?,guard,zero,Nat.pos_of_ne_zero hz,Nat.ne_of_gt pos]

/-- Both child orders in 'assemble' are computed from recursive zero-mass keys. -/
private def build (i : Input) {d : Nat} (children : Cursor i.certified d → List (Cursor i.certified d)) : Nat → Cursor i.certified d → Option Key
  | 0,_ => none
  | fuel+1,q => do
    let cs := children q
    let o ← read? i q cs.isEmpty
    let ks ← cs.mapM (build i children fuel)
    return assemble o ks

def rebuiltKey? (i : Input) {d : Nat} (q : Cursor i.certified d) :=
  build i i.certified.executableLocalizedRerootChildren (2*(d+1)+1) q

/-- Rebuild using a caller's molecular child index throughout the arm. -/
def rebuiltWith (i : Input) {d : Nat} (reader : i.certified.LocalizedRerootChildReader d)
    (q : Cursor i.certified d) : Option Key :=
  build i (fun t => (reader.readChildren t).getD []) (2*(d+1)+1) q

theorem rebuiltWith_eq (i : Input) {d : Nat} (reader : i.certified.LocalizedRerootChildReader d) :
    rebuiltWith i reader = rebuiltKey? i := by
  funext q
  unfold rebuiltWith rebuiltKey?
  congr 1
  funext t; rw [reader.readChildren_eq]; rfl

/-- Share the original-root child index throughout the zero-mass rebuild. -/
private def cachedKey (i : Input) {d : Nat} (q : Cursor i.certified d) :=
  let slice := CertifiedLocalizedCIPInput.localizedRerootRootSliceCache
    (i.certified.localizedRerootCarrierCache d) q.occurrence.val.root
  build i (fun c => (slice.reader.readChildren c).getD []) (2*(d+1)+1) q

@[csimp] private theorem cached_eq : @rebuiltKey? = @cachedKey := by
  funext i d q
  unfold rebuiltKey? cachedKey
  congr 1
  funext c
  rw [CertifiedLocalizedCIPInput.LocalizedRerootChildReader.readChildren_eq]
  rfl

private abbrev Sample := {o : Observation // o.duplicate ≠ 0 →
  CIPRule2MassData.rule2MassPico? o.atomic none = some o.mass}

private def oldAt (s : Stage) (o : Sample) := o.val.atStage s
private def newAt (s : Stage) (o : Sample) := (zero o.val).atStage s

private theorem same_entry (a b : Sample) (z : oldAt .atomic a = oldAt .atomic b)
    (d : oldAt .duplicate a = oldAt .duplicate b) :
    compare (newAt .mass a) (newAt .mass b) = compare (oldAt .mass a) (oldAt .mass b) := by
  change a.val.atomic = b.val.atomic at z
  change a.val.duplicate = b.val.duplicate at d
  by_cases h : a.val.duplicate = 0
  · simp [newAt,oldAt,Observation.atStage,zero,h,← d]
  · have ha := a.property h
    have hb := b.property (d ▸ h)
    rw [z] at ha
    have m := Option.some.inj (ha.symm.trans hb)
    simp [newAt,oldAt,Observation.atStage,zero,h,← d,m]

/-- Lift invariance of a comparison through a lexicographic list with two
already-tied projections. This also preserves equality and row boundaries. -/
private theorem lift_compare {α β : Type} [Ord β] (z d u v : α → β)
    (same : ∀ a b, z a = z b → d a = d b → compare (v a) (v b) = compare (u a) (u b))
    (xs ys : List α) (az : xs.map z = ys.map z) (ad : xs.map d = ys.map d) :
    compare (xs.map v) (ys.map v) = compare (xs.map u) (ys.map u) := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      obtain ⟨z1,z2⟩ := List.cons.inj az
      obtain ⟨d1,d2⟩ := List.cons.inj ad
      simp only [List.map_cons,List.compare_cons_cons,same x y z1 d1,ih ys z2 d2]

private theorem triple {α : Type} [Ord α] [Std.LawfulEqOrd α] {a b c d x y u v : α}
    (h : a = b → c = d → compare u v = compare x y) :
    compare [a,c,u] [b,d,v] = compare [a,c,x] [b,d,y] := by
  simp only [List.compare_cons_cons]
  cases az : compare a b <;> try rfl
  cases ad : compare c d <;> try rfl
  rw [h (Std.compare_eq_eq_iff_eq.mp az) (Std.compare_eq_eq_iff_eq.mp ad)]

/-- A common arrangement of observations certifies all six columns, even
though the two executable keys are assembled independently. -/
private structure Pair where
  old : Key
  newKey : Key
  oldForm : WellFormed old
  newForm : WellFormed newKey
  root : Sample
  oldRoot : old.root = root.val
  newRoot : newKey.root = zero root.val
  layers : Layers Sample
  oldLayers : ∀ s, project (oldAt s) layers = (old.column s).levels
  newLayers : ∀ s, project (newAt s) layers = (newKey.column s).levels

private def Pair.rows (p : Pair) := [p.root] :: p.layers.flatten

private theorem Pair.oldWord (p : Pair) (s : Stage) :
    (p.old.column s).word = p.rows.map (List.map (oldAt s)) := by
  rw [(p.oldForm s).2,← p.oldLayers,p.oldRoot]
  simp [Pair.rows,project,oldAt,List.map_flatten]

private theorem Pair.newWord (p : Pair) (s : Stage) :
    (p.newKey.column s).word = p.rows.map (List.map (newAt s)) := by
  rw [(p.newForm s).2,← p.newLayers,p.newRoot]
  simp [Pair.rows,project,newAt,List.map_flatten]

private def priority {α : Type} (value : Stage → Key → α) (k : Key) :=
  (stages .mass).map (value · k)

private theorem head_order (a b : Pair) :
    compare (priority headAt a.newKey) (priority headAt b.newKey) =
    compare (priority headAt a.old) (priority headAt b.old) := by
  simp only [priority,stages,List.map_cons,List.map_nil,headAt,a.newRoot,b.newRoot,a.oldRoot,b.oldRoot]
  exact triple (same_entry a.root b.root)

private theorem word_order (a b : Pair) :
    compare (priority wordAt a.newKey) (priority wordAt b.newKey) =
    compare (priority wordAt a.old) (priority wordAt b.old) := by
  simp only [priority,stages,List.map_cons,List.map_nil,wordAt,Pair.oldWord,Pair.newWord]
  apply triple
  exact lift_compare (List.map (oldAt .atomic)) (List.map (oldAt .duplicate))
    (List.map (oldAt .mass)) (List.map (newAt .mass))
    (lift_compare _ _ _ _ same_entry) a.rows b.rows

private def sorted {α : Type} [LinearOrder α] (v : Stage → Key → α) (ps : List Pair) :=
  ps.mergeSort fun a b => decide (priority v b.old ≤ priority v a.old)

private theorem sorted_old {α : Type} [LinearOrder α] (v : Stage → Key → α) (ps : List Pair) :
    (sorted v ps).map Pair.old = rank v .mass (ps.map Pair.old) :=
  List.map_mergeSort fun _ _ _ _ => rfl

private theorem sorted_new {α : Type} [LinearOrder α] (v : Stage → Key → α) (ps : List Pair)
    (leq : ∀ a b : Pair, priority v a.old ≤ priority v b.old ↔ priority v a.newKey ≤ priority v b.newKey) :
    (sorted v ps).map Pair.newKey = rank v .mass (ps.map Pair.newKey) :=
  List.map_mergeSort fun a _ b _ => by
    change decide (priority v b.old ≤ priority v a.old) = decide (priority v b.newKey ≤ priority v a.newKey)
    simp only [leq b a]

private theorem same_le {α : Type} [LinearOrder α] (cmp : α → α → Ordering)
    (lt : ∀ x y, cmp x y = .lt ↔ x < y) {a b c d : α} (h : cmp d c = cmp b a) :
    a ≤ b ↔ c ≤ d := by
  rw [← not_lt,← not_lt,← lt,← lt,h]

private theorem head_lt (a b : List Nat) : compare a b = .lt ↔ a < b :=
  DeclarativeCIP.compareLex_eq_lt_iff_of compare (fun _ _ => compare_lt_iff_lt)
    (fun _ _ => Std.compare_eq_eq_iff_eq) a b

private theorem word_lt (a b : List Word) : compare a b = .lt ↔ a < b :=
  DeclarativeCIP.compareLex_eq_lt_iff_of compare
    (DeclarativeCIP.compareLex_eq_lt_iff_of compare head_lt (fun _ _ => Std.compare_eq_eq_iff_eq))
    (fun _ _ => Std.compare_eq_eq_iff_eq) a b

private def parentLayers (cs : List Pair) : Layers Sample :=
  [(sorted headAt cs).map Pair.root,(sorted wordAt cs).map Pair.root] ::
    (sorted wordAt cs).foldr (fun p acc => interleave p.layers acc) []

private theorem forest_projection (s : Stage) (side : Pair → Key) (f : Sample → Nat)
    (h : ∀ p, project f p.layers = ((side p).column s).levels) (cs : List Pair) :
    project f (cs.foldr (fun p acc => interleave p.layers acc) []) = forest s (cs.map side) := by
  induction cs with
  | nil => rfl
  | cons p ps ih => exact (project_interleave ..).trans (congrArg₂ interleave (h p) ih)

private theorem parent_projection (cs : List Pair) (o : Observation) (s : Stage)
    (side : Pair → Key) (f : Sample → Nat) (forms : ∀ p, WellFormed (side p))
    (hr : ∀ p, f p.root = (side p).root.atStage s)
    (hl : ∀ p, project f p.layers = ((side p).column s).levels)
    (sh : (sorted headAt cs).map side = rank headAt .mass (cs.map side))
    (de : (sorted wordAt cs).map side = rank wordAt .mass (cs.map side)) :
    project f (parentLayers cs) = ((assemble o (cs.map side)).column s).levels := by
  have formed : ∀ k ∈ cs.map side, WellFormed k := by
    intro k hk
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp hk
    exact forms p
  rw [common_layout s o _ formed,← sh,← de]
  have heads (ps : List Pair) : (ps.map Pair.root).map f = (ps.map side).map (headAt s) := by
    simp only [List.map_map]
    exact List.map_congr_left fun p _ => hr p
  exact congrArg₂ List.cons (congrArg₂ (fun a b => [a,b]) (heads _) (heads _))
    (forest_projection s side f hl _)

private def parent (o : Sample) (cs : List Pair) : Pair where
  old := assemble o.val (cs.map Pair.old)
  newKey := assemble (zero o.val) (cs.map Pair.newKey)
  oldForm := assemble_framed _ _ (by
    intro k hk; obtain ⟨p,_,rfl⟩ := List.mem_map.mp hk; exact p.oldForm)
  newForm := assemble_framed _ _ (by
    intro k hk; obtain ⟨p,_,rfl⟩ := List.mem_map.mp hk; exact p.newForm)
  root := o
  oldRoot := rfl
  newRoot := rfl
  layers := parentLayers cs
  oldLayers s := parent_projection cs _ s _ _ Pair.oldForm
    (fun p => congrArg (fun v : Observation => v.atStage s) p.oldRoot.symm) (fun p => p.oldLayers s)
    (sorted_old ..) (sorted_old ..)
  newLayers s := parent_projection cs _ s _ _ Pair.newForm
    (fun p => congrArg (fun v : Observation => v.atStage s) p.newRoot.symm) (fun p => p.newLayers s)
    (sorted_new _ _ fun a b => same_le _ head_lt (head_order b a))
    (sorted_new _ _ fun a b => same_le _ word_lt (word_order b a))

private theorem pair_children {α : Type} {old newKey : α → Option Key} {ks : List Key}
    (cs : List α) (hit : cs.mapM old = some ks)
    (ih : ∀ c ∈ cs, ∀ {k}, old c = some k → ∃ p : Pair, p.old = k ∧ newKey c = some p.newKey) :
    ∃ ps : List Pair, ps.map Pair.old = ks ∧ cs.mapM newKey = some (ps.map Pair.newKey) := by
  induction cs generalizing ks with
  | nil => exact ⟨[],(Option.some.inj hit),rfl⟩
  | cons c cs step =>
    rw [List.mapM_cons] at hit
    obtain ⟨k,hk,tail⟩ := Option.bind_eq_some_iff.mp hit
    obtain ⟨ks',hks,out⟩ := Option.bind_eq_some_iff.mp tail
    cases Option.some.inj out
    obtain ⟨p,hp,hnew⟩ := ih c List.mem_cons_self hk
    obtain ⟨ps,hps,rest⟩ := step hks (fun a ha => ih a (List.mem_cons_of_mem _ ha))
    exact ⟨p::ps,by simp [hp,hps],by simp [List.mapM_cons,hnew,rest]⟩

private theorem rebuild {i : Input} {d : Nat} {q : Cursor i.certified d} {k : Key}
    (e : Expansion i q k) (valid : i.certified.LocalizedRerootCursorValid q) (fuel : Nat)
    (enough : i.certified.localizedRerootCursorBudget q < fuel) :
    ∃ p : Pair, p.old = k ∧ build i i.certified.executableLocalizedRerootChildren fuel q = some p.newKey := by
  induction e generalizing fuel with
  | @node q cs o ks frame observed lookup hit branches ih =>
    have children := Option.some.inj (((i.certified.localizedRerootChildren?_eq_some_iff q cs).mpr frame).symm.trans
      (i.certified.localizedRerootChildren?_eq_some_executable q))
    subst cs
    cases fuel with
    | zero => omega
    | succ fuel =>
      have sample : o.duplicate ≠ 0 → CIPRule2MassData.rule2MassPico? o.atomic none = some o.mass := by
        rcases observation_kind observed with ⟨_,h⟩ | ⟨_,h⟩
        · exact fun ne => False.elim (ne h)
        · exact fun _ => h
      obtain ⟨ps,hps,built⟩ := pair_children _ hit fun c hc k hk =>
        ih c hc hk (i.certified.localizedRerootChild_valid q c _ frame hc) fuel
          (by have h := i.certified.localizedRerootChild_budget_lt q c _ valid frame hc; omega)
      exact ⟨parent ⟨o,sample⟩ ps,congrArg (assemble o) hps,by simp [build,read_zero observed,built,parent]⟩

private theorem key_pair {i : Input} {d : Nat} {q : Cursor i.certified d} {k : Key}
    (valid : i.certified.LocalizedRerootCursorValid q) (hit : key? i q = some k) :
    ∃ p : Pair, p.old = k ∧ rebuiltKey? i q = some p.newKey :=
  rebuild (key_source hit) valid _ (Nat.lt_succ_of_le (i.certified.localizedRerootCursorBudget_le_twice q))

/-- The two keys have the same molecular arrangement of real and duplicate sites. -/
def Corresponds (old rebuilt : Key) : Prop := ∃ p : Pair, p.old = old ∧ p.newKey = rebuilt

theorem rebuilt_corresponds {i : Input} {d : Nat} {q : Cursor i.certified d} {k : Key}
    (valid : i.certified.LocalizedRerootCursorValid q) (found : key? i q = some k) :
    ∃ t, rebuiltKey? i q = some t ∧ Corresponds k t := by
  obtain ⟨p,h,read⟩ := key_pair valid found
  exact ⟨_,read,p,h,rfl⟩

def headPriority (k : Key) := [k.root.atomic,k.root.duplicate,k.root.mass]

theorem Corresponds.orders {a b x y : Key} (l : Corresponds a x) (r : Corresponds b y) :
    compare (headPriority x) (headPriority y) = compare (headPriority a) (headPriority b) ∧
    compare (RingRetainedChemicalPreorder.orderWord x) (RingRetainedChemicalPreorder.orderWord y) =
      compare (RingRetainedChemicalPreorder.orderWord a) (RingRetainedChemicalPreorder.orderWord b) := by
  obtain ⟨p,h,k⟩ := l
  obtain ⟨q,j,m⟩ := r
  rw [← h,← k,← j,← m]
  exact ⟨head_order p q,word_order p q⟩

/-- Compare two arms using only their independently rebuilt keys. -/
def compareArms? (i : Input) {d : Nat} (a b : Cursor i.certified d) : Option Ordering := do
  return compareKeys (← rebuiltKey? i a) (← rebuiltKey? i b)

theorem arms_agree {i : Input} {d : Nat} {a b : Cursor i.certified d} {x y : Key}
    (va : i.certified.LocalizedRerootCursorValid a) (vb : i.certified.LocalizedRerootCursorValid b)
    (ha : key? i a = some x) (hb : key? i b = some y) :
    compareArms? i a b = some (compareKeys x y) := by
  obtain ⟨l,rfl,hl⟩ := key_pair va ha
  obtain ⟨r,rfl,hr⟩ := key_pair vb hb
  unfold compareArms?
  rw [hl,hr]
  apply congrArg some
  change compareKeys l.newKey r.newKey = compareKeys l.old r.old
  rw [RingRetainedChemicalPreorder.compare_word,RingRetainedChemicalPreorder.compare_word]
  exact word_order l r

open RingRetainedChemicalPreorder (Site Direction keyFor read_key)

/-- Every pair of ligand directions on every admitted input, including a
diagonal query, has exactly the original three-way constitutional outcome. -/
theorem directions_agree (i : Input) (f : Site i) (a b : Direction i f) :
    compareArms? i ⟨a.val,some f⟩ ⟨b.val,some f⟩ = some (compareKeys (keyFor a) (keyFor b)) := by
  have valid (c : Direction i f) : i.certified.LocalizedRerootCursorValid ⟨c.val,some f⟩ :=
    (i.certified.mem_localizedRerootNeighborFrames_iff f.val c.val.val).mpr ⟨c.val.property,c.property⟩
  exact arms_agree (valid a) (valid b) (read_key a) (read_key b)

def compareAt? (i : Input) (f a b : Site i) : Option Ordering :=
  if RingRetainedConstitution.Incident i.certified f a b then compareArms? i ⟨a,some f⟩ ⟨b,some f⟩ else none

/-- Full-domain equality with the public retained comparison at molecular
depth. Neither prior ties nor successful reads are assumptions. -/
theorem compareAt_agrees (i : Input) (f a b : Site i) :
    compareAt? i f a b = (RingRetainedChemicalTrace.compareAt? i f a b).map cipTraceOutcome := by
  by_cases inc : RingRetainedConstitution.Incident i.certified f a b
  · let u : Direction i f := ⟨a,inc.2.2.1⟩
    let v : Direction i f := ⟨b,inc.2.2.2⟩
    simpa [compareAt?,RingRetainedChemicalTrace.compareAt?,inc,trace?,read_key u,read_key v,compareKeys,u,v]
      using directions_agree i f u v
  · simp [compareAt?,RingRetainedChemicalTrace.compareAt?,inc]

/-- The independently recomputed key exists for every molecular direction. -/
def rebuiltFor {i : Input} {f : Site i} (a : Direction i f) : Key :=
  (rebuiltKey? i ⟨a.val,some f⟩).get (by
    have valid : i.certified.LocalizedRerootCursorValid ⟨a.val,some f⟩ := (i.certified.mem_localizedRerootNeighborFrames_iff f.val a.val.val).mpr
      ⟨a.val.property,a.property⟩
    obtain ⟨p,_,hit⟩ := key_pair (i := i) valid (read_key a)
    exact Option.isSome_iff_exists.mpr ⟨_,hit⟩)

/-- Shallow and deep constitutional prefixes keep their respective orders
even when the two occurrences come from different foci. -/
theorem prefixes_agree {i : Input} {f g : Site i} (a : Direction i f) (b : Direction i g) :
    compare (priority headAt (rebuiltFor a)) (priority headAt (rebuiltFor b)) =
      compare (priority headAt (keyFor a)) (priority headAt (keyFor b)) ∧
    compare (priority wordAt (rebuiltFor a)) (priority wordAt (rebuiltFor b)) =
      compare (priority wordAt (keyFor a)) (priority wordAt (keyFor b)) := by
  have witness {f : Site i} (c : Direction i f) : ∃ p : Pair, p.old = keyFor c ∧ p.newKey = rebuiltFor c := by
    have valid : i.certified.LocalizedRerootCursorValid ⟨c.val,some f⟩ := (i.certified.mem_localizedRerootNeighborFrames_iff f.val c.val.val).mpr
      ⟨c.val.property,c.property⟩
    obtain ⟨p,old,hit⟩ := key_pair (i := i) valid (read_key c)
    exact ⟨p,old,Option.some.inj (hit.symm.trans (show rebuiltKey? i ⟨c.val,some f⟩ = some (rebuiltFor c) from (Option.some_get _).symm))⟩
  obtain ⟨p,op,np⟩ := witness a
  obtain ⟨q,oq,nq⟩ := witness b
  rw [← op,← np,← oq,← nq]
  exact ⟨head_order p q,word_order p q⟩

/-- Sort actual ligand occurrences by the shallow or deep constitutional
prefix, then use a supplied later rule only on ties. -/
def rankedDirections {i : Input} {f : Site i} (read : Direction i f → Key) (deep : Bool)
    (later : Direction i f → Direction i f → Ordering) (xs : List (Direction i f)) :=
  xs.mergeSort fun a b =>
    let prior := if deep then compare (priority wordAt (read a)) (priority wordAt (read b))
      else compare (priority headAt (read a)) (priority headAt (read b))
    (prior.then (later a b)) != .lt

/-- Switching to zero duplicate mass preserves the exact occurrence order of
both sorts, including repeated entries and ties in the secondary comparison. -/
theorem ranked_directions_agree {i : Input} {f : Site i} (deep : Bool)
    (later : Direction i f → Direction i f → Ordering) (xs : List (Direction i f)) :
    rankedDirections rebuiltFor deep later xs = rankedDirections keyFor deep later xs := by
  unfold rankedDirections
  congr 1
  funext a b
  cases deep <;> simp [(prefixes_agree a b).1,(prefixes_agree a b).2]

end TetraStereo.Engine.RingZeroDuplicateMass

assert_kernel_only TetraStereo.Engine.RingZeroDuplicateMass.directions_agree
assert_kernel_only TetraStereo.Engine.RingZeroDuplicateMass.compareAt_agrees

assert_kernel_only TetraStereo.Engine.RingZeroDuplicateMass.ranked_directions_agree
