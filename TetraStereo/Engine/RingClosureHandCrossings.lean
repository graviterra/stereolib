import TetraStereo.Engine.RingOccurrenceHandParity

/-! A single retained ligand loses its second shell at a closure. Count the
neighbors it passes directly from their original element and shell. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingClosureHandCrossings
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingNestedActivePair (Frame)
open RingGroupedTrials (atom)
open RingChemicalPriority.ReferenceFrame (pairCount)
open RingOccurrenceHandParity (labels)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open private normalized pairCount_zero pairCount_congr from TetraStereo.Engine.RingReferenceCasing
open private ranked from TetraStereo.Engine.RingSecondShellDecision
open private trace state from TetraStereo.Engine.RingOccurrenceHandParity

def priority (z : Nat → Nat) (shell : Nat → List Nat) (n : Nat) := [[z n],shell n]
def cut (shell : Nat → List Nat) (closed n : Nat) := if n = closed then [] else shell n

/-- A previously lower neighbor with the same atomic number and a nonempty
retained second shell. -/
def crossed (z : Nat → Nat) (shell : Nat → List Nat) (closed n : Nat) :=
  decide (z n = z closed ∧ shell n ≠ [] ∧ shell n < shell closed)

def crossings (z : Nat → Nat) (shell : Nat → List Nat) (closed : Nat) (neighbors : List Nat) :=
  neighbors.countP (crossed z shell closed)

private theorem key_lt {a b : Nat} {x y : List Nat} :
    [[a],x] < [[b],y] ↔ a < b ∨ a = b ∧ x < y := by simp [List.cons_lt_cons_iff]

private theorem empty_lt {s : List Nat} : [] < s ↔ s ≠ [] := by cases s <;> simp

/-- On an initially strictly descending pair, the only inversion is a
closed first ligand passing precisely one of the neighbors counted above. -/
theorem pair_crossing (z : Nat → Nat) (shell : Nat → List Nat) (k a b : Nat)
    (before : priority z shell b < priority z shell a) :
    priority z (cut shell k) a < priority z (cut shell k) b ↔ a = k ∧ crossed z shell k b = true := by
  have ne : a ≠ b := fun h => lt_irrefl _ (h ▸ before)
  simp only [priority,key_lt] at before ⊢
  by_cases ak : a = k
  · subst a
    have changed : cut shell k k = [] := if_pos rfl
    have fixed : cut shell k b = shell b := if_neg (Ne.symm ne)
    rw [changed,fixed,empty_lt]
    simp only [true_and,crossed,decide_eq_true_eq]
    grind
  · have fixed : cut shell k a = shell a := if_neg ak
    rw [fixed]
    by_cases bk : b = k
    · subst b
      rw [show cut shell k k = [] from if_pos rfl]
      simp [ak]
      grind
    · rw [show cut shell k b = shell b from if_neg bk]
      simp only [ak,false_and,iff_false]
      rcases before with h | ⟨h,t⟩ <;> grind

private theorem hub_count (z : Nat → Nat) (sh : Nat → List Nat) (k : Nat)
    (xs : List Nat) (sorted : xs.Pairwise (fun a b => priority z sh b < priority z sh a))
    (mem : k ∈ xs) :
    pairCount (fun a b => decide (priority z (cut sh k) a < priority z (cut sh k) b)) xs =
      crossings z sh k xs := by
  let pred := crossed z sh k
  let hub := fun a b : Nat => decide (a = k) && pred b
  have pair := pairCount_congr (xs := xs)
    (v := fun a b => decide (priority z (cut sh k) a < priority z (cut sh k) b)) (w := hub)
    (sorted.imp fun {a b} lt => Bool.eq_iff_iff.mpr (by simpa [hub,pred] using pair_crossing z sh k a b lt))
  rw [pair]
  clear pair
  change pairCount hub xs = xs.countP pred
  induction xs with
  | nil => contradiction
  | cons a xs ih =>
    have ⟨high,tail⟩ := List.pairwise_cons.mp sorted
    by_cases eqn : a = k
    · subst a
      have off : k ∉ xs := fun hk => lt_irrefl _ (high k hk)
      have rest : xs.Pairwise (fun i j => hub i j = false) := by
        apply List.pairwise_iff_getElem.mpr
        intro i j hi hj _
        have ne : xs[i] ≠ k := fun h => off (h ▸ List.getElem_mem hi)
        simp [hub,ne]
      have fixed : hub k = pred := by funext x; simp [hub]
      have self : pred k = false := by simp [pred,crossed]
      rw [pairCount,pairCount_zero rest,fixed]
      simp [self]
    · have present : k ∈ xs := (List.mem_cons.mp mem).resolve_left (Ne.symm eqn)
      have prior := high k present
      have no : pred a = false := by
        simp only [pred,crossed,decide_eq_false_iff_not]
        simp only [priority,key_lt] at prior
        grind
      rw [pairCount,ih tail present]
      simp [hub,eqn,no]

private theorem sorted_row {i : Input} {q : Site i} {fr : Frame i q} {row}
    (hit : RingSecondShellDecision.row? fr = some row) {key : Nat → List (List Nat)}
    (matchKey : ∀ s, RingSecondShellDecision.score fr s = key (atom fr s)) :
    (fr.atoms row).Pairwise (fun a b => key b < key a) := by
  dsimp only [RingSecondShellDecision.row?] at hit
  split at hit <;> try contradiction
  rename_i strict
  cases Option.some.inj hit
  apply List.pairwise_map.mpr
  exact strict.imp (fun {a b} h => by simpa only [matchKey] using h)

/-- The graph scores, the changed raw ligand ID and successful strict shell
checks suffice. The rank rows, coordinates and native hands are outputs. -/
theorem public_hand {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {u v : Site i} (a : Frame i u) (b : Frame i v) (same : a.center = b.center)
    (shell : Nat → List Nat) (closed : Nat) (member : closed ∈ a.ids)
    (old : ∀ s, RingSecondShellDecision.score a s =
      priority (RingAtomicNeighborOrder.atomicNumber i.molecule) shell (atom a s))
    (new : ∀ s, RingSecondShellDecision.score b s =
      priority (RingAtomicNeighborOrder.atomicNumber i.molecule) (cut shell closed) (atom b s))
    (strictA : (RingSecondShellDecision.row? a).isSome = true)
    (strictB : (RingSecondShellDecision.row? b).isSome = true) :
    ∃ h : RS, RingChemicalGraphProof.state i u = some (some (labels h)) ∧
      RingChemicalGraphProof.state i v = some (some (labels
        (if crossings (RingAtomicNeighborOrder.atomicNumber i.molecule) shell closed a.ids % 2 = 0
        then h else h.swap))) := by
  obtain ⟨ra,ha⟩ := Option.isSome_iff_exists.mp strictA
  obtain ⟨rb,hb⟩ := Option.isSome_iff_exists.mp strictB
  let z := RingAtomicNeighborOrder.atomicNumber i.molecule
  let xs := a.atoms ra
  let ys := b.atoms rb
  let ka := priority z shell
  let kb := priority z (cut shell closed)
  have sa : xs.Pairwise (fun x y => ka y < ka x) := sorted_row ha old
  have sb : ys.Pairwise (fun x y => kb y < kb x) := sorted_row hb new
  have xp := trace (ranked a ha)
  have yp := trace (ranked b hb)
  rw [←same] at yp
  have perm : xs.Perm ys := xp.trans yp.symm
  have ids : xs.Perm a.ids := xp.trans a.physical.symm
  have nd : xs.Nodup := xp.nodup_iff.mpr
    ((List.nodup_finRange 4).map (Fin.val_injective.comp (i.certified.canonicalLigandAtom_injective a.center)))
  have four : xs.length = 4 := xp.length_eq.trans (by simp [RingRetainedAuxiliary.canonical])
  let inv := fun x y => decide (kb x < kb y)
  have dist : (ys.map kb).Nodup := List.pairwise_map.mpr (sb.imp fun h => ne_of_gt h)
  have inj := (List.nodup_map_iff_inj_on (perm.nodup_iff.mp nd)).mp dist
  have opp (x) (hx : x ∈ xs) (y) (hy : y ∈ xs) (ne : x ≠ y) : inv x y = !inv y x := by
    have different : kb x ≠ kb y := fun h => ne (inj x (perm.mem_iff.mp hx) y (perm.mem_iff.mp hy) h)
    rcases lt_or_gt_of_ne different with h | h <;> simp [inv,h,not_lt_of_ge h.le]
  have zero : pairCount inv ys = 0 := pairCount_zero (sb.imp fun h => by simp [inv,not_lt_of_ge h.le])
  have count : pairCount inv xs = crossings z shell closed a.ids :=
    (hub_count z shell closed xs sa (ids.mem_iff.mpr member)).trans (ids.countP_eq _)
  have norm := normalized perm (inputGeometry i.certified) inv [] (by simpa using four) opp nd
  simp only [List.nil_append,zero,count] at norm
  change (if crossings z shell closed a.ids % 2 = 0 then readback? _ xs else (readback? _ xs).map RS.swap) =
    readback? (inputGeometry i.certified) ys at norm
  have ok := RingGroupedGeometry.calibrated geom a (ranked a ha).row (ranked a ha).permutation
  rw [(ranked a ha).atoms_eq] at ok
  obtain ⟨h,hx⟩ := Option.isSome_iff_exists.mp ok
  change readback? (inputGeometry i.certified) xs = some h at hx
  rw [hx] at norm
  refine ⟨h,by rw [state geom (ranked a ha),hx]; rfl,?_⟩
  rw [state geom (ranked b hb)]
  change some ((readback? _ ys).map labels) = _
  rw [←norm]
  change _ = some (some (labels (if crossings z shell closed a.ids % 2 = 0 then h else h.swap)))
  split <;> rfl

/-- Atom IDs of real first directions at this visit and their physical raw
second shells. A closure duplicate has an empty retained shell. -/
def retainedShell {i : Input} {u : Site i} (a : Frame i u) (n : Nat) : List Nat :=
  let real := (List.finRange 4).any fun s => atom a s == n && (a.arm s).occurrence.val.node.provenance == .realAtom
  if real then RingSecondShellDecision.shell i.molecule a.center.val.val n else []

/-- Use only molecular graph data and occurrence provenance. A successful
check witnesses a single nonempty shell becoming empty, with both rank rows strict. -/
def count? (i : Input) (u v : Site i) (closed : Nat) : Option Nat := do
  let a ← RingNestedActivePair.frame? i u
  let b ← RingNestedActivePair.frame? i v
  let z := RingAtomicNeighborOrder.atomicNumber i.molecule
  let shell := retainedShell a
  if a.center = b.center ∧ closed ∈ a.ids ∧ shell closed ≠ [] ∧
      (∀ s, RingSecondShellDecision.score a s = priority z shell (atom a s)) ∧
      (∀ s, RingSecondShellDecision.score b s = priority z (cut shell closed) (atom b s)) ∧
      (RingSecondShellDecision.row? a).isSome = true ∧ (RingSecondShellDecision.row? b).isSome = true then
    return crossings z shell closed a.ids
  else none

theorem checked {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (u v : Site i) (closed n : Nat) (got : count? i u v closed = some n) :
    ∃ h : RS, RingChemicalGraphProof.state i u = some (some (labels h)) ∧
      RingChemicalGraphProof.state i v = some (some (labels (if n % 2 = 0 then h else h.swap))) := by
  unfold count? at got
  obtain ⟨a,_,h⟩ := Option.bind_eq_some_iff.mp got
  obtain ⟨b,_,h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  split at h <;> try contradiction
  rename_i ok
  cases Option.some.inj h
  obtain ⟨center,mem,_,old,new,ha,hb⟩ := ok
  exact public_hand geom a b center _ closed mem old new ha hb

end TetraStereo.Engine.RingClosureHandCrossings
assert_kernel_only TetraStereo.Engine.RingClosureHandCrossings.pair_crossing
assert_kernel_only TetraStereo.Engine.RingClosureHandCrossings.public_hand
assert_kernel_only TetraStereo.Engine.RingClosureHandCrossings.checked
