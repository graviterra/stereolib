import TetraStereo.Engine.RingRecursiveSigned

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority.CursorStereo
open OneCenter CertifiedLocalizedCIPInput Recursive IsotopePriority

/-- Empty caches use the molecular recursion directly. This also leaves
the empty-cache result reducible in the kernel without hashing any paths. -/
private def cachedRead {m g depth} (rows : RecursiveSigned.Cache m g depth) (q : List Nat) :=
  if rows.isEmpty then RecursiveSigned.derive? m g depth (m.atomCount+1) q else rows.read q

private theorem cachedRead_exact {m g depth} (rows : RecursiveSigned.Cache m g depth) (q : List Nat) :
    cachedRead rows q = RecursiveSigned.derive? m g depth (m.atomCount+1) q := by
  unfold cachedRead
  split
  · rfl
  · exact rows.read_exact q

/-- In a frozen distance batch a signed observation must be strictly deeper in
the original digraph. The incoming arm may contain such sites in another
branch. Every value is computed at the original address, without restarting
the molecular digraph at the current focus. -/
def read? {m g depth} (rows : RecursiveSigned.Cache m g depth) (p : List Nat)
    (c : CanonicalRerootCursor) : Option (Option Reading) :=
  let q := c.node.history.reverse
  if UnitClasses.classAt? m [] ⟨c,[c.node],[],true⟩ = some 0 then some none
  else if p.head? = q.head? ∧ p.length < q.length then
    (cachedRead rows q).map (·.verdict)
  else none

theorem signed_source {m g depth} {rows : RecursiveSigned.Cache m g depth} {p c r}
    (found : read? rows p c = some (some r)) :
    let q := c.node.history.reverse
    p.head? = q.head? ∧ p.length < q.length ∧
    ∃ cert : RecursiveSigned.Certificate m g q,
      RecursiveSigned.derive? m g depth (m.atomCount+1) q = some cert ∧
      RecursiveSigned.Derives m g cert.published q (some r) := by
  unfold read? at found
  dsimp only at found
  split at found
  · cases found
  split at found
  · rename_i valid
    obtain ⟨cert,foundCert,verdict⟩ := Option.map_eq_some_iff.mp found
    exact ⟨valid.1,valid.2,cert,(cachedRead_exact rows _).symm.trans foundCert,verdict ▸ cert.derived⟩
  · contradiction

/-- A negative reading is justified by exclusion as a stereogenic site or by
a certified negative verdict at a previously available molecular address. -/
theorem absence_source {m g depth} {rows : RecursiveSigned.Cache m g depth} {p c}
    (found : read? rows p c = some none) :
    UnitClasses.classAt? m [] ⟨c,[c.node],[],true⟩ = some 0 ∨
    (let q := c.node.history.reverse
     p.head? = q.head? ∧ p.length < q.length ∧
     ∃ cert : RecursiveSigned.Certificate m g q,
       RecursiveSigned.derive? m g depth (m.atomCount+1) q = some cert ∧ cert.step.refuses) := by
  unfold read? at found
  dsimp only at found
  split at found
  · exact Or.inl ‹_›
  split at found
  · rename_i valid
    obtain ⟨cert,foundCert,verdict⟩ := Option.map_eq_some_iff.mp found
    exact Or.inr ⟨valid.1,valid.2,cert,(cachedRead_exact rows _).symm.trans foundCert,cert.step.reading?_eq_none_iff.mp verdict⟩
  · contradiction

/-- An address outside the focus branch is never supplied by the
descendant-only certificate for that focus, even when genuinely deeper. -/
theorem outside_branch {m g p q} (cert : RecursiveSigned.Certificate m g p)
    (outside : ¬p <+: q) : cert.published.lookup q = none := by
  cases h : cert.published.lookup q with
  | none => rfl
  | some r => exact False.elim (outside (cert.lookup_derived h).1)

def prior? {m g depth} (rows : RecursiveSigned.Cache m g depth) (p : List Nat)
    (c : CanonicalRerootCursor) : Option (FullObservation × Nat) := do
  let obs ← fullObservation? m p c
  let v ← read? rows p c
  return ({obs with prior := DuplicatePriority.originalView obs.prior}, UnitClasses.kind v)

/-- Enumerate the signed sites in the retained arm, including the portion
pointing back toward the old root. Running out of depth is inconclusive. -/
def sites? {m g depth} (rows : RecursiveSigned.Cache m g depth) (p : List Nat) :
    Nat → CanonicalRerootCursor → Option (List (CanonicalRerootCursor × Reading))
  | 0,_ => none
  | fuel+1,c => do
    let v ← read? rows p c
    let rest ← (c.children m).mapM (sites? rows p fuel)
    return ((v.map fun r => (c,r)).toList ++ rest.flatten)

private theorem member_of_mapM {α β : Type} (f : α → Option β) {xs : List α} {ys : List β} {y : β}
    (ok : xs.mapM f = some ys) (member : y ∈ ys) : ∃ x ∈ xs, f x = some y := by
  induction xs generalizing ys with
  | nil => simp at ok; subst ys; simp at member
  | cons x xs ih =>
    cases h : f x with
    | none => simp [List.mapM_cons,h] at ok
    | some b =>
      cases ht : xs.mapM f with
      | none => simp [List.mapM_cons,h,ht] at ok
      | some bs =>
        obtain rfl : b :: bs = ys := by simpa [List.mapM_cons,h,ht] using ok
        rcases List.mem_cons.mp member with rfl | rest
        · exact ⟨x,List.mem_cons_self,h⟩
        · obtain ⟨z,hz,found⟩ := ih ht rest
          exact ⟨z,List.mem_cons_of_mem _ hz,found⟩

theorem sites_source {m g depth} {rows : RecursiveSigned.Cache m g depth} {p fuel c xs}
    (closed : sites? rows p fuel c = some xs) {entry} (member : entry ∈ xs) :
    read? rows p entry.1 = some (some entry.2) := by
  induction fuel generalizing c xs with
  | zero => simp [sites?] at closed
  | succ n ih =>
    cases h : read? rows p c with
    | none => simp [sites?,h] at closed
    | some v =>
      cases tail : (c.children m).mapM (sites? rows p n) with
      | none => simp [sites?,h,tail] at closed
      | some groups =>
        obtain rfl : ((v.map fun r => (c,r)).toList ++ groups.flatten) = xs := by
          simpa [sites?,h,tail] using closed
        rcases List.mem_append.mp member with here | below
        · cases v with
          | none => simp at here
          | some val =>
            obtain rfl : entry = (c,val) := by simpa using here
            exact h
        · obtain ⟨group,inside,e⟩ := List.mem_flatten.mp below
          obtain ⟨child,_,mapped⟩ := member_of_mapM _ tail inside
          exact ih mapped e

/-- A single uppercase site on each entire arm leaves Rule 4b without a
descriptor pair and Rule 4c without a lowercase descriptor. The full matched
trees carry Rule 1, mass, and the Rule 4a class on both arms. -/
structure Pair {m g depth} (rows : RecursiveSigned.Cache m g depth) (p : List Nat) where
  domain : saturatedWithHalogens m = true
  focus : RawMolecule.CanonicalBranchNode
  reached : occurrence? m p = some focus
  carbon : (m.atoms[focus.atom]?).any (fun a => a.element == .C) = true
  left : CanonicalRerootCursor
  right : CanonicalRerootCursor
  leftAt : left ∈ occurrenceLigandCursors m focus
  rightAt : right ∈ occurrenceLigandCursors m focus
  incoming : canonicalOriginalParent? focus = some left.node
  distinct : left.node.atom ≠ right.node.atom
  matched : TreesMatch m (prior? rows p) (budget m+1) left right
  a : CanonicalRerootCursor
  b : CanonicalRerootCursor
  hand : RS
  leftOnly : sites? rows p (budget m+1) left = some [(a,⟨hand,hand.swap⟩)]
  rightOnly : sites? rows p (budget m+1) right = some [(b,⟨hand.swap,hand⟩)]

/-- Rule 5 prefers R over S. Reflection reverses which of the two singleton
sites is senior. Magnitude two is the signed source convention for this
enantiomorphic comparison. -/
def Pair.code {m g depth rows p} (pair : @Pair m g depth rows p) (reflected : Bool) : Int :=
  if (if reflected then pair.hand.swap else pair.hand) = .R then 2 else -2

theorem Pair.signed_codes {m g depth rows p} (pair : @Pair m g depth rows p) :
    (pair.code false = 2 ∧ pair.code true = -2) ∨
    (pair.code false = -2 ∧ pair.code true = 2) := by
  cases h : pair.hand <;> simp [Pair.code,h,RS.swap]

/-- The singleton Rule 5 layer uses the two actual signs in the molecular
certificate. It yields the same preference as the signed source code. -/
theorem Pair.rule5 {m g depth rows p} (pair : @Pair m g depth rows p) (rev : Bool) :
    let a := if rev then pair.hand.swap else pair.hand
    let b := if rev then pair.hand else pair.hand.swap
    PairSpheres.seniorLeft? [[a == .R]] [[b == .R]] = some (decide (0 < pair.code rev)) := by
  cases h : pair.hand <;> cases rev <;> simp only [h,Pair.code] <;> rfl

/-- Both complete singleton inventories lack a pair for Rule 4b and a
lowercase reading for Rule 4c, on either geometry. -/
theorem Pair.earlier_stereo {m g depth rows p} (pair : @Pair m g depth rows p) (rev : Bool) :
    let evidence := fun (xs : List (CanonicalRerootCursor × Reading)) =>
      xs.map fun (c,r) => (c.node.history.reverse,r)
    let l := (sites? rows p (budget m+1) pair.left).map evidence
    let r := (sites? rows p (budget m+1) pair.right).map evidence
    l.bind (fun fs => firstPair fs rev) = none ∧ r.bind (fun fs => firstPair fs rev) = none ∧
    (do let xs ← l; let ys ← r; seniorLeft? .fourC xs ys rev) = none := by
  dsimp only
  rw [pair.leftOnly,pair.rightOnly]
  cases pair.hand <;> cases rev <;> exact ⟨rfl,rfl,rfl⟩

theorem Pair.molecular_readings {m g depth rows p} (pair : @Pair m g depth rows p) :
    let q := pair.a.node.history.reverse
    let t := pair.b.node.history.reverse
    p.head? = q.head? ∧ p.head? = t.head? ∧ p.length < q.length ∧ p.length < t.length ∧
    ∃ (l : RecursiveSigned.Certificate m g q) (r : RecursiveSigned.Certificate m g t),
      RecursiveSigned.derive? m g depth (m.atomCount+1) q = some l ∧
      RecursiveSigned.derive? m g depth (m.atomCount+1) t = some r ∧
      RecursiveSigned.Derives m g l.published q (some ⟨pair.hand,pair.hand.swap⟩) ∧
      RecursiveSigned.Derives m g r.published t (some ⟨pair.hand.swap,pair.hand⟩) := by
  obtain ⟨rootX,deepX,l,lc,lv⟩ := signed_source (sites_source pair.leftOnly List.mem_cons_self)
  obtain ⟨rootY,deepY,r,rc,rv⟩ := signed_source (sites_source pair.rightOnly List.mem_cons_self)
  exact ⟨rootX,rootY,deepX,deepY,l,r,lc,rc,lv,rv⟩

def compare? {m g depth} (rows : RecursiveSigned.Cache m g depth) (p : List Nat) (i j : Nat) :
    Option {pair : Pair rows p // pair.left.node.atom = i ∧ pair.right.node.atom = j} := do
  let ⟨focus,reached⟩ ← (occurrence? m p).attach
  let cs := occurrenceLigandCursors m focus
  let ⟨l,hl⟩ ← (cs.find? fun c => c.node.atom == i).attach
  let ⟨r,hr⟩ ← (cs.find? fun c => c.node.atom == j).attach
  if frame : saturatedWithHalogens m = true ∧ (m.atoms[focus.atom]?).any (fun a => a.element == .C) = true ∧
      canonicalOriginalParent? focus = some l.node ∧ l.node.atom ≠ r.node.atom then
    let [(a,x)] ← sites? rows p (budget m+1) l | none
    let [(b,_)] ← sites? rows p (budget m+1) r | none
    if signs : sites? rows p (budget m+1) l = some [(a,⟨x.actual,x.actual.swap⟩)] ∧
        sites? rows p (budget m+1) r = some [(b,⟨x.actual.swap,x.actual⟩)] then
      if iso : treesMatch m (prior? rows p) (budget m+1) l r = true then
        return ⟨⟨frame.1,focus,reached,frame.2.1,l,r,List.mem_of_find?_eq_some hl,List.mem_of_find?_eq_some hr,
          frame.2.2.1,frame.2.2.2,treesMatch_sound iso,a,b,x.actual,signs.1,signs.2⟩,eq_of_beq (List.find?_some (p := fun c : CanonicalRerootCursor => c.node.atom == i) hl),
          eq_of_beq (List.find?_some (p := fun c : CanonicalRerootCursor => c.node.atom == j) hr)⟩
  none

open LocalizedGenericMarkedRecalculation LocalizedMarkedTerminalGaugeSwap

/-- On the unique Rule 5 pair, the sign comes from both signed molecular
sites. Every other comparison requires strictly ordered Rule 1a spheres. -/
def Pair.before {m g depth rows p} (pair : @Pair m g depth rows p) (rev : Bool) (i j : Nat) : Bool :=
  if i = pair.left.node.atom ∧ j = pair.right.node.atom then decide (0 < pair.code rev)
  else if i = pair.right.node.atom ∧ j = pair.left.node.atom then decide (pair.code rev < 0)
  else match ligandRows? m p i depth, ligandRows? m p j depth with
    | some a,some b => decide (b < a)
    | _,_ => false

structure Ranking {m g depth rows p} (pair : @Pair m g depth rows p) where
  actual : List Nat
  complete : actual.Perm ((occurrenceLigandCursors m pair.focus).map (·.node.atom))
  length : actual.length = 4
  unique : actual.Nodup
  strict : actual.Pairwise (fun i j => pair.before false i j = true)
  reflected : (actual.map (swapAtom pair.left.node.atom pair.right.node.atom)).Pairwise
    (fun i j => pair.before true i j = true)

def Pair.rank? {m g depth rows p} (pair : @Pair m g depth rows p) : Option (Ranking pair) := do
  let ids := (occurrenceLigandCursors m pair.focus).map (·.node.atom)
  let ordered := ids.insertionSort fun a b => pair.before false a b = true
  if accepted : ordered.length = 4 ∧ ordered.Nodup ∧ ordered.Pairwise (fun i j => pair.before false i j = true) ∧
      (ordered.map (swapAtom pair.left.node.atom pair.right.node.atom)).Pairwise (fun i j => pair.before true i j = true) then
    return ⟨ordered,List.perm_insertionSort _ _,accepted.1,accepted.2.1,accepted.2.2.1,accepted.2.2.2⟩
  none

/-- The only exchange of ligands under reflection cancels the spatial
reflection in the geometric reading. Both signs of the surviving pair therefore
give lowercase letters, with the actual hand deciding r versus s. -/
theorem Ranking.chemical_letter {m g depth rows p pair} (rank : @Ranking m g depth rows p pair)
    {h : RS} (raw : readback? g rank.actual = some h) :
    let reflected := rank.actual.map (swapAtom pair.left.node.atom pair.right.node.atom)
    readback? (mirror g) reflected = some h ∧
    (geometric g rank.actual reflected).bind Reading.label = some (.pseudoasymmetric (pseudoRSOfRS h)) := by
  have left := rank.complete.mem_iff.mpr (List.mem_map_of_mem (f := fun c : CanonicalRerootCursor => c.node.atom) pair.leftAt)
  have right := rank.complete.mem_iff.mpr (List.mem_map_of_mem (f := fun c : CanonicalRerootCursor => c.node.atom) pair.rightAt)
  have mirrorHand : readback? (mirror g) (rank.actual.map (swapAtom pair.left.node.atom pair.right.node.atom)) = some h := by
    rw [readback_mirror,readback_swapAtom g _ _ pair.distinct _ rank.unique rank.length left right,raw]
    cases h <;> rfl
  exact ⟨mirrorHand,by simp only [geometric,raw,mirrorHand,Reading.label]; exact caseFromMirror?_eq_same h⟩

structure Assignment {m g depth} (rows : RecursiveSigned.Cache m g depth) (p : List Nat) where
  pair : Pair rows p
  rank : Ranking pair
  hand : RS
  actual : readback? g rank.actual = some hand

def Assignment.label {m g depth rows p} (a : @Assignment m g depth rows p) :
    LocalizedAuxiliaryLabel := .pseudoasymmetric (pseudoRSOfRS a.hand)

theorem Assignment.actual_and_reflected {m g depth rows p} (a : @Assignment m g depth rows p) :
    let reflected := a.rank.actual.map (swapAtom a.pair.left.node.atom a.pair.right.node.atom)
    readback? (mirror g) reflected = some a.hand ∧
    (geometric g a.rank.actual reflected).bind Reading.label = some a.label :=
  a.rank.chemical_letter a.actual

/-- Discover the incoming arm and the single opposite arm from the actual
molecular focus. No arm identifiers, auxiliary signs or priority orders are
supplied by the caller. -/
def assign? {m g depth} (rows : RecursiveSigned.Cache m g depth) (p : List Nat) :
    Option (Assignment rows p) := do
  let focus ← occurrence? m p
  let incoming ← canonicalOriginalParent? focus
  (occurrenceLigandCursors m focus).findSome? fun other => do
    guard (other.node.atom != incoming.atom)
    let ⟨pair,_⟩ ← compare? rows p incoming.atom other.node.atom
    let rank ← pair.rank?
    let ⟨hand,read⟩ ← (readback? g rank.actual).attach
    return ⟨pair,rank,hand,read⟩

end TetraStereo.Engine.RingChemicalPriority.CursorStereo

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.CursorStereo.signed_source
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.CursorStereo.outside_branch
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.CursorStereo.Pair.signed_codes
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.CursorStereo.Pair.molecular_readings

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.CursorStereo.Pair.rule5

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.CursorStereo.Ranking.chemical_letter

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.CursorStereo.absence_source

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.CursorStereo.Assignment.actual_and_reflected

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.CursorStereo.Pair.earlier_stereo
