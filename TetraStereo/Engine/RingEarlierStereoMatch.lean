import TetraStereo.Engine.RingUnitClasses

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority.EarlierStereoMatch
open OneCenter CertifiedLocalizedCIPInput Recursive

/-- A single change of convention for both hands throughout one ligand.
The same change applies to every reference, every following site and both
geometries. -/
def orient (flip : Bool) (h : RS) := if flip then h.swap else h

theorem orient_injective (flip : Bool) : Function.Injective (orient flip) := by
  intro a b eqn
  cases flip <;> cases a <;> cases b <;> simp_all [orient, RS.swap]

theorem orient_like (flip : Bool) (a b : RS) : (orient flip a = orient flip b) ↔ a = b :=
  (orient_injective flip).eq_iff

/-- Tags retain exactly the stereo information needed before the proposed
next rule. 0 is absent, 1/2 are uppercase and 3/4 are lowercase. -/
def tag (stage : Stage) (flip : Bool) : Option LocalizedAuxiliaryLabel → Nat
  | none => 0
  | some (.chiral h) => if stage == .fourB || orient flip h == .R then 1 else 2
  | some (.pseudoasymmetric h) => if stage != .five || h == .r then 3 else 4

def tagClass (v : Nat) := if v = 0 then 0 else if v ≤ 2 then 2 else 1

theorem tag_class (stage : Stage) (flip : Bool) (r : Option Reading) :
    tagClass (tag stage flip (r.bind Reading.label)) = UnitClasses.kind r := by
  cases r with
  | none => rfl
  | some r =>
    obtain ⟨a,b⟩ := r
    cases stage <;> cases flip <;> cases a <;> cases b <;> rfl

theorem fourB_tags (flip : Bool) (r : Option Reading) :
    tag .fourB flip (r.bind Reading.label) =
      (if UnitClasses.kind r = 2 then 1 else if UnitClasses.kind r = 1 then 3 else 0) := by
  cases r with
  | none => rfl
  | some r =>
    obtain ⟨a,b⟩ := r
    cases a <;> cases b <;> cases flip <;> rfl

theorem upper_tags {stage : Stage} (later : stage ≠ .fourB) (flip : Bool) (a b : RS) :
    tag stage flip (some (.chiral a)) = tag stage false (some (.chiral b)) ↔ orient flip a = b := by
  cases stage <;> cases flip <;> cases a <;> cases b <;> first | contradiction | decide

/-- Two matched uppercase occurrences give the same like/unlike decision
for the corresponding ordered pair, including when both hands are reversed. -/
theorem like_of_matched_tags {stage : Stage} (later : stage ≠ .fourB) (flip : Bool) {a b x y : RS}
    (first : tag stage flip (some (.chiral a)) = tag stage false (some (.chiral x)))
    (second : tag stage flip (some (.chiral b)) = tag stage false (some (.chiral y))) :
    (a = b) ↔ x = y := by
  rw [← (upper_tags later flip a x).mp first,← (upper_tags later flip b y).mp second]
  exact (orient_like flip a b).symm

theorem lower_tags (stage : Stage) (flip : Bool) (a b : PseudoRS) :
    tag stage flip (some (.pseudoasymmetric a)) = tag stage false (some (.pseudoasymmetric b)) ↔
      stage ≠ .five ∨ a = b := by
  cases stage <;> cases flip <;> cases a <;> cases b <;> decide

structure Tags where
  actual : Nat
  reflected : Nat
  deriving DecidableEq

def tags (stage : Stage) (flip : Bool) (r : Option Reading) : Tags :=
  ⟨tag stage flip (r.bind Reading.label),tag stage flip (r.bind fun x => x.reverse.label)⟩

/-- Reflecting the entire input exchanges the two tag projections. -/
theorem tags_mirror (stage : Stage) (flip : Bool) (r : Option Reading) :
    tags stage flip (r.map Reading.reverse) = ⟨(tags stage flip r).reflected,(tags stage flip r).actual⟩ := by
  cases r with
  | none => rfl
  | some r => cases r; rfl

structure Observation where
  constitutional : IsotopePriority.FullObservation
  unitClass : Nat
  stereo : Tags
  deriving DecidableEq

/-- Absence and signed readings are fetched from the exact outward
occurrence history. A missing real carbon is admitted only when it is
excluded by the independent two-identical-hydrogen test. -/
def onSide? (m : RawMolecule) (focus : List Nat) (stage : Stage) (flip : Bool)
    (es : UnitClasses.Facts) (c : CanonicalRerootCursor) : Option Observation := do
  let prior ← IsotopePriority.fullObservation? m focus c
  let unit ← UnitClasses.classAt? m es ⟨c,[c.node],[],true⟩
  let v := tags stage flip (es.lookup c.node.history.reverse).join
  if tagClass v.actual = unit ∧ tagClass v.reflected = unit then return ⟨prior,unit,v⟩
  none

theorem onSide?_sound {m p stage flip es c o} (h : onSide? m p stage flip es c = some o) :
    IsotopePriority.fullObservation? m p c = some o.constitutional ∧
    UnitClasses.classAt? m es ⟨c,[c.node],[],true⟩ = some o.unitClass ∧
    o.stereo = tags stage flip (es.lookup c.node.history.reverse).join := by
  cases hp : IsotopePriority.fullObservation? m p c with
  | none => simp [onSide?,hp] at h
  | some prior =>
    cases hc : UnitClasses.classAt? m es ⟨c,[c.node],[],true⟩ with
    | none => simp [onSide?,hp,hc] at h
    | some unit =>
      let v := tags stage flip (es.lookup c.node.history.reverse).join
      have hv : v = tags stage flip (es.lookup c.node.history.reverse).join := rfl
      by_cases accepted : tagClass v.actual = unit ∧ tagClass v.reflected = unit
      · have same : (⟨prior,unit,v⟩ : Observation) = o := by
          simpa [onSide?,hp,hc,← hv,accepted] using h
        subst o
        exact ⟨rfl,rfl,rfl⟩
      · simp [onSide?,hp,hc,← hv,accepted] at h

/-- Choose the inventory by the full outward path below the same focus. A
cursor outside both arms cannot provide an observation. -/
def observe? (m : RawMolecule) (p : List Nat) (i j : Nat) (stage : Stage) (flip : Bool)
    (ls rs : UnitClasses.Facts) (c : CanonicalRerootCursor) : Option Observation := do
  let address := c.node.history.reverse
  if p ++ [i] <+: address then return ← onSide? m p stage flip ls c
  if p ++ [j] <+: address then return ← onSide? m p stage false rs c
  none

/-- A common retained-tree correspondence simultaneously matches isotopic,
duplicate, and prior stereo observations on both geometries. Negative or
positive entries have to be justified by the enclosing derivation. -/
structure Decision (m : RawMolecule) (p : List Nat) (i j : Nat) (stage : Stage)
    (ls rs : UnitClasses.Facts) where
  prior : IsotopePriority.IncidentComparison m p i j
  checked : IsotopePriority.compareIncident? m p i j = some prior
  tied : prior.ordering = .eq
  left : UnitClasses.Covered m p i prior.pair.left.cursor ls
  right : UnitClasses.Covered m p j prior.pair.right.cursor rs
  leftForward : prior.pair.left.cursor.previous? = some prior.pair.focus ∧
    prior.pair.left.cursor.node.history.reverse = p ++ [i]
  rightForward : prior.pair.right.cursor.previous? = some prior.pair.focus ∧
    prior.pair.right.cursor.node.history.reverse = p ++ [j]
  distinct : ((ls ++ rs).map Prod.fst).Nodup
  flip : Bool
  matched : IsotopePriority.TreesMatch m (observe? m p i j stage flip ls rs)
    (IsotopePriority.budget m+1) prior.pair.left.cursor prior.pair.right.cursor

def check? (m : RawMolecule) (p : List Nat) (i j : Nat) (stage : Stage) (ls rs : UnitClasses.Facts) :
    Option (Decision m p i j stage ls rs) := do
  let ⟨prior,checked⟩ ← (IsotopePriority.compareIncident? m p i j).attach
  if tied : prior.ordering = .eq then
    let a := prior.pair.left.cursor
    let b := prior.pair.right.cursor
    let ⟨left⟩ ← UnitClasses.covered? m p i a ls
    let ⟨right⟩ ← UnitClasses.covered? m p j b rs
    if la : a.previous? = some prior.pair.focus ∧ a.node.history.reverse = p ++ [i] then
      if rb : b.previous? = some prior.pair.focus ∧ b.node.history.reverse = p ++ [j] then
        if unique : ((ls ++ rs).map Prod.fst).Nodup then
          let attempt (flip : Bool) : Option (Decision m p i j stage ls rs) :=
            if eqn : IsotopePriority.treesMatch m (observe? m p i j stage flip ls rs)
                (IsotopePriority.budget m+1) a b = true then
              some ⟨prior,checked,tied,left,right,la,rb,unique,flip,IsotopePriority.treesMatch_sound eqn⟩
            else none
          return ← (attempt false).orElse fun _ => if stage == .fourB then none else attempt true
  none

theorem Decision.fullTie {m p i j s ls rs} (d : Decision m p i j s ls rs) :
    IsotopePriority.FullTie m p d.prior.pair.left d.prior.pair.right :=
  d.prior.equal_trees d.tied

/-- Every reader built from the jointly matched observations and an
order-independent fold of the children agrees on the two actual ligands. -/
theorem Decision.equal_observer {m p i j s ls rs} (d : Decision m p i j s ls rs) {α : Type}
    (reader : Nat → CanonicalRerootCursor → α) (combine : Observation → List α → α)
    (atNode : ∀ n c o, observe? m p i j s d.flip ls rs c = some o →
      reader (n+1) c = combine o ((c.children m).map (reader n)))
    (symmetric : ∀ o {xs ys : List α}, xs.Perm ys → combine o xs = combine o ys) :
    reader (IsotopePriority.budget m+1) d.prior.pair.left.cursor =
      reader (IsotopePriority.budget m+1) d.prior.pair.right.cursor :=
  d.matched.observer_eq reader combine atNode symmetric

end TetraStereo.Engine.RingChemicalPriority.EarlierStereoMatch

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.EarlierStereoMatch.onSide?_sound
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.EarlierStereoMatch.Decision.fullTie
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.EarlierStereoMatch.Decision.equal_observer
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.EarlierStereoMatch.like_of_matched_tags
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.EarlierStereoMatch.lower_tags
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.EarlierStereoMatch.tags_mirror
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.EarlierStereoMatch.check?
