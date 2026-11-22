import TetraStereo.Engine.RingInventoryPriority

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority.SignedPair
open OneCenter CertifiedLocalizedCIPInput Recursive InventoryPriority

abbrev Key := List (List Nat)

/-- The finite Rule 1a prefix used for an actual incident ligand, including
the return toward the original parent when that ligand is incident. -/
structure Row (m : RawMolecule) (p : List Nat) (depth : Nat) where
  ligand : Nat
  key : Key
  molecular : ligandRows? m p ligand depth = some key
  deriving DecidableEq

private def row? (m : RawMolecule) (p : List Nat) (depth i : Nat) : Option (Row m p depth) := do
  let ⟨k,h⟩ ← (ligandRows? m p i depth).attach
  return ⟨i,k,h⟩

private def twins {m p d} (rows : List (Row m p d)) :=
  rows.filter fun a => rows.any fun b => a.ligand != b.ligand && a.key == b.key

/-- All sixteen comparisons use the source-bound prefix keys. The unique
off-diagonal tie has two outward occurrences on the original ring digraph.
Every other distinct pair has different Rule 1a keys. -/
structure Frame (m : RawMolecule) (p : List Nat) (depth : Nat) where
  domain : saturatedWithHalogens m = true
  focus : RawMolecule.CanonicalBranchNode
  reached : occurrence? m p = some focus
  carbon : (m.atoms[focus.atom]?).any (fun a => a.element == .C) = true
  rows : List (Row m p depth)
  incident : rows.map (·.ligand) = (occurrenceLigandCursors m focus).map (·.node.atom)
  four : rows.length = 4
  distinct : (rows.map (·.ligand)).Nodup
  left : Row m p depth
  right : Row m p depth
  leftMem : left ∈ rows
  rightMem : right ∈ rows
  different : left.ligand ≠ right.ligand
  tied : left.key = right.key
  allPairs : ∀ a ∈ rows, ∀ b ∈ rows, a.key = b.key ↔
    a.ligand = b.ligand ∨ (a.ligand = left.ligand ∧ b.ligand = right.ligand) ∨
      (a.ligand = right.ligand ∧ b.ligand = left.ligand)
  leftNode : RawMolecule.CanonicalBranchNode
  rightNode : RawMolecule.CanonicalBranchNode
  leftAt : leftNode ∈ m.canonicalChildren focus ∧ leftNode.history.reverse = p ++ [left.ligand]
  rightAt : rightNode ∈ m.canonicalChildren focus ∧ rightNode.history.reverse = p ++ [right.ligand]
  leftAtom : leftNode.atom = left.ligand
  rightAtom : rightNode.atom = right.ligand
  leftPaths : List (List Nat)
  rightPaths : List (List Nat)
  leftComplete : carbonSites m (m.atomCount+1) leftNode = some leftPaths
  rightComplete : carbonSites m (m.atomCount+1) rightNode = some rightPaths

private def outward? (m : RawMolecule) (focus : RawMolecule.CanonicalBranchNode)
    (p : List Nat) (i : Nat) :
    Option {n : RawMolecule.CanonicalBranchNode //
      (n ∈ m.canonicalChildren focus ∧ n.history.reverse = p ++ [i]) ∧ n.atom = i} := do
  let ⟨n,hn⟩ ← ((m.canonicalChildren focus).find? fun n => n.atom == i).attach
  if path : n.history.reverse = p ++ [i] then
    return ⟨n,⟨List.mem_of_find?_eq_some hn,path⟩,by simpa using List.find?_some hn⟩
  none

def frame? (m : RawMolecule) (p : List Nat) (depth : Nat) : Option (Frame m p depth) := do
  if domain : saturatedWithHalogens m = true then
    let ⟨n,hn⟩ ← (occurrence? m p).attach
    if carbon : (m.atoms[n.atom]?).any (fun a => a.element == .C) = true then
      let ids := (occurrenceLigandCursors m n).map (·.node.atom)
      let rows ← ids.mapM (row? m p depth)
      if valid : rows.map (·.ligand) = ids ∧ rows.length = 4 ∧ (rows.map (·.ligand)).Nodup then
        let [a,b] := twins rows | none
        if pair : a ∈ rows ∧ b ∈ rows ∧ a.ligand ≠ b.ligand ∧ a.key = b.key then
          if all : ∀ x ∈ rows, ∀ y ∈ rows, x.key = y.key ↔
              x.ligand = y.ligand ∨ (x.ligand = a.ligand ∧ y.ligand = b.ligand) ∨
                (x.ligand = b.ligand ∧ y.ligand = a.ligand) then
            let ⟨ln,la⟩ ← outward? m n p a.ligand
            let ⟨rn,ra⟩ ← outward? m n p b.ligand
            let ⟨ls,lc⟩ ← (carbonSites m (m.atomCount+1) ln).attach
            let ⟨rs,rc⟩ ← (carbonSites m (m.atomCount+1) rn).attach
            return ⟨domain,n,hn,carbon,rows,valid.1,valid.2.1,valid.2.2,a,b,
              pair.1,pair.2.1,pair.2.2.1,pair.2.2.2,all,ln,rn,la.1,ra.1,la.2,ra.2,ls,rs,lc,rc⟩
  none

def Frame.requiredPaths {m p d} (f : Frame m p d) := f.leftPaths ++ f.rightPaths

def requiredPaths? (m : RawMolecule) (p : List Nat) (depth : Nat) :=
  (frame? m p depth).map Frame.requiredPaths

/-- Zero indicates a noncandidate, one a known absent entry, and the four
remaining values distinguish all actual/reflected pairs. -/
private def handCode : Option (Option Reading) → Nat
  | none => 0
  | some none => 1
  | some (some ⟨.R,.R⟩) => 2
  | some (some ⟨.R,.S⟩) => 3
  | some (some ⟨.S,.R⟩) => 4
  | some (some ⟨.S,.S⟩) => 5

def tag (entries : Entries) (path : List Nat) := handCode (entries.lookup path)

private def decode : Nat → Option (Option Reading)
  | 1 => some none
  | 2 => some (some ⟨.R,.R⟩)
  | 3 => some (some ⟨.R,.S⟩)
  | 4 => some (some ⟨.S,.R⟩)
  | 5 => some (some ⟨.S,.S⟩)
  | _ => none

private theorem decode_exact (x : Option (Option Reading)) : decode (handCode x) = x := by
  rcases x with _ | r
  · rfl
  rcases r with _ | ⟨a,b⟩
  · rfl
  cases a <;> cases b <;> rfl

theorem lookup_of_tag {ls rs : Entries} {p q : List Nat} (same : tag ls p = tag rs q) :
    ls.lookup p = rs.lookup q := by
  simpa only [tag,decode_exact] using congrArg decode same

private def project (source : Entries) : (paths : List (List Nat)) →
    Option {es : Entries // es.map Prod.fst = paths ∧ ∀ x ∈ es, source.lookup x.1 = some x.2}
  | [] => some ⟨[],rfl,by simp⟩
  | p :: ps => do
    let ⟨r,hr⟩ ← (source.lookup p).attach
    let ⟨rest,keys,covered⟩ ← project source ps
    return ⟨(p,r) :: rest,by simp [keys],by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | tail
      · exact hr
      · exact covered x tail⟩

/-- A single retained occurrence supplies the full earlier-rule observation
and its signed reading. The nested option distinguishes missing candidates,
certified absences, and all four possible pairs of geometry readings. -/
def jointObservation? (m : RawMolecule) (p : List Nat) (es : Entries) (c : CanonicalRerootCursor) :
    Option (IsotopePriority.FullObservation × Option (Option Reading)) := do
  let o ← IsotopePriority.fullObservation? m p c
  return (o,es.lookup c.node.history.reverse)

/-- The supplied readings and verified absences must be justified by the
caller. This certificate binds each one to its occurrence and compares the
resulting complete decorated trees. -/
structure Pair (m : RawMolecule) (p : List Nat) where
  depth : Nat
  frame : Frame m p depth
  left : Entries
  right : Entries
  leftKeys : left.map Prod.fst = frame.leftPaths
  rightKeys : right.map Prod.fst = frame.rightPaths
  unique : ((left ++ right).map Prod.fst).Nodup
  code : MarkedHierarchy.Code
  leftCode : MarkedHierarchy.encode m (tag left) [] (m.atomCount+1) frame.leftNode = some code
  rightCode : MarkedHierarchy.encode m (tag right) [] (m.atomCount+1) frame.rightNode = some code
  prior : IsotopePriority.IncidentComparison m p frame.left.ligand frame.right.ligand
  checked : IsotopePriority.compareIncident? m p frame.left.ligand frame.right.ligand = some prior
  tied : prior.ordering = .eq
  leftCursor : prior.pair.left.cursor = ⟨frame.leftNode,some frame.focus⟩
  rightCursor : prior.pair.right.cursor = ⟨frame.rightNode,some frame.focus⟩
  together : IsotopePriority.TreesMatch m (jointObservation? m p (left ++ right))
    (IsotopePriority.budget m+1) prior.pair.left.cursor prior.pair.right.cursor

def Pair.required {m p} (c : Pair m p) : Entries := c.left ++ c.right

def Frame.checkWith? {m p d} (f : Frame m p d) (entries : Entries) :
    Option {c : Pair m p // ∀ x ∈ c.required, entries.lookup x.1 = some x.2} := do
  if input : (entries.map Prod.fst).Nodup then
    let ⟨l,lk,lc⟩ ← project entries f.leftPaths
    let ⟨r,rk,rc⟩ ← project entries f.rightPaths
    if unique : ((l ++ r).map Prod.fst).Nodup then
      let ⟨code,left⟩ ← (MarkedHierarchy.encode m (tag l) [] (m.atomCount+1) f.leftNode).attach
      if right : MarkedHierarchy.encode m (tag r) [] (m.atomCount+1) f.rightNode = some code then
        let ⟨prior,checked⟩ ← (IsotopePriority.compareIncident? m p f.left.ligand f.right.ligand).attach
        if bound : prior.ordering = .eq ∧ prior.pair.left.cursor = ⟨f.leftNode,some f.focus⟩ ∧
            prior.pair.right.cursor = ⟨f.rightNode,some f.focus⟩ then
          if together : IsotopePriority.treesMatch m (jointObservation? m p (l ++ r))
              (IsotopePriority.budget m+1) prior.pair.left.cursor prior.pair.right.cursor = true then
            return ⟨⟨d,f,l,r,lk,rk,unique,code,left,right,prior,checked,bound.1,bound.2.1,bound.2.2,
              IsotopePriority.treesMatch_sound together⟩,by
              intro x hx
              rcases List.mem_append.mp hx with h | h
              · exact lc x h
              · exact rc x h⟩
  none

def check? (m : RawMolecule) (p : List Nat) (depth : Nat) (entries : Entries) : Option (Pair m p) := do
  let f ← frame? m p depth
  return (← f.checkWith? entries).val

theorem Pair.matching {m p} (c : Pair m p) :
    MarkedHierarchy.Isomorphic m m (tag c.left) (tag c.right) [] [] (m.atomCount+1)
      c.frame.leftNode c.frame.rightNode :=
  MarkedHierarchy.isomorphic_of_code c.leftCode c.rightCode

theorem Pair.fullTie {m p} (c : Pair m p) :
    IsotopePriority.FullTie m p c.prior.pair.left c.prior.pair.right := c.prior.equal_trees c.tied

/-- The same matching of retained child occurrences preserves the molecular
observations and all signed entries. Any fold that respects this matching
and is invariant under child permutations has equal readings on the pair. -/
theorem Pair.joint_observer {m p} (c : Pair m p) {α : Type}
    (reader : Nat → CanonicalRerootCursor → α)
    (combine : (IsotopePriority.FullObservation × Option (Option Reading)) → List α → α)
    (atNode : ∀ n cursor o, jointObservation? m p c.required cursor = some o →
      reader (n+1) cursor = combine o ((cursor.children m).map (reader n)))
    (symmetric : ∀ o {xs ys : List α}, xs.Perm ys → combine o xs = combine o ys) :
    reader (IsotopePriority.budget m+1) c.prior.pair.left.cursor =
      reader (IsotopePriority.budget m+1) c.prior.pair.right.cursor :=
  c.together.observer_eq reader combine atNode symmetric

/-- The two selected atoms constitute the entire population with a distinct
equal partner. Every other ligand pair is constitutionally separated. -/
theorem Frame.eligible_iff {m p d} (f : Frame m p d) {a} (ha : a ∈ f.rows) :
    (∃ b ∈ f.rows, a.ligand ≠ b.ligand ∧ a.key = b.key) ↔
    a.ligand = f.left.ligand ∨ a.ligand = f.right.ligand := by
  constructor
  · rintro ⟨b,hb,ne,eq⟩
    rcases (f.allPairs a ha b hb).mp eq with same | ab | ba
    · exact (ne same).elim
    · exact Or.inl ab.1
    · exact Or.inr ba.1
  · rintro (al | ar)
    · refine ⟨f.right,f.rightMem,by rw [al]; exact f.different,?_⟩
      exact (f.allPairs a ha f.right f.rightMem).mpr (.inr (.inl ⟨al,rfl⟩))
    · refine ⟨f.left,f.leftMem,by rw [ar]; exact Ne.symm f.different,?_⟩
      exact (f.allPairs a ha f.left f.leftMem).mpr (.inr (.inr ⟨ar,rfl⟩))

theorem Frame.no_strict_permutation {m p d} (f : Frame m p d) (order : List (Row m p d))
    (perm : order.Perm f.rows) : ¬ order.Pairwise (fun a b => b.key < a.key) := by
  intro strict
  have noDup : (order.map (·.key)).Nodup :=
    List.pairwise_map.mpr (strict.imp fun h => ne_of_gt h)
  have nodup := (perm.map (fun a => a.key)).nodup_iff.mp noDup
  have same := List.inj_on_of_nodup_map nodup f.leftMem f.rightMem f.tied
  exact f.different (congrArg (fun a : Row m p d => a.ligand) same)

end TetraStereo.Engine.RingChemicalPriority.SignedPair

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.SignedPair.check?
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.SignedPair.Pair.matching
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.SignedPair.Frame.eligible_iff
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.SignedPair.Frame.no_strict_permutation
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.SignedPair.lookup_of_tag
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.SignedPair.Pair.fullTie
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.SignedPair.Pair.joint_observer
