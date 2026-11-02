import TetraStereo.KernelOnly
import TetraStereo.OneCenter.OrganicStereoEmbeddedGraphRealization
import TetraStereo.OneCenter.OrganicStereoRealConfiguration
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.OfMap
import Mathlib.Tactic.NormNum

set_option autoImplicit false

/-!
# Constructive completion of finite partial injective atom positions

This module proves the missing *structural atom-position existence* step between a finite table of
supplied atom positions and the total conformations consumed by
`OrganicStereoEmbeddedGraphRealization.EmbeddedGraph.conformation` and by
`CIPFrontier.MolecularConformation`.

The input is an arbitrary finite vertex type `V` and a partial position

`p : PartialPosition V = V → Option EmbeddedReal3`,

where `EmbeddedReal3 = EuclideanSpace ℝ (Fin 3)` is the repository's ambient real three-space.
`KnownInjective p` says that two equally supplied positions must belong to the same vertex; no
further hypothesis is imposed on the supplied points (they may be negative, irrational, coplanar,
or all missing).

## Construction

`knownFirstBound p` is the finite sum of the absolute values of the first coordinates of all
supplied positions.  It is nonnegative and bounds *every* supplied first coordinate from above.
`missingFirst p v = knownFirstBound p + 1 + (enum v).val`, using a fixed finite enumeration
`Fintype.equivFin V`.  The total position `complete p` keeps every supplied point verbatim and
places a missing vertex `v` at

`anchor (missingFirst p v) = EuclideanSpace.single 0 (missingFirst p v)`,

the point of first coordinate `missingFirst p v` with the two remaining coordinates equal to zero.
The `+1` makes every missing first coordinate strictly larger than the sum (hence than every
supplied first coordinate), and the strictly increasing enumeration value separates the missing
vertices from each other.  This is the explicit constructive completion; it is not a
`Classical.choose` of an unproved existence statement.

## Main results

* `KnownInjective`, `Extends`, `PartialPosition`, `TotalPosition`;
* `knownFirstBound`, `knownFirst_le`, `knownFirstBound_lt_missingFirst`,
  `knownFirst_lt_missingFirst`: the bound and its strict separation properties;
* `complete_of_some`, `complete_of_none`, `complete_extends`: exact recovery of every supplied
  coordinate;
* `complete_known_lt_complete_missing`: every missing first coordinate is strictly larger than
  every supplied first coordinate;
* `complete_injective`: if `KnownInjective p`, the constructed completion is injective;
* `exists_injective_extension_iff`: `(∃ full, Extends p full ∧ Injective full) ↔ KnownInjective p`
  (both directions), and the `Nonempty` subtype form `nonempty_injective_extension_iff`;
* `exists_injective_molecularConformation_iff`: the same criterion with the completion typed as
  `MolecularConformation V` (definitionally the same type);
* `not_exists_injective_extension_of_conflict`: two distinct vertices sharing a supplied position
  have no injective completion;
* `knownInjective_update_missing` and `exists_injective_extension_prescribing_missing`: at an
  *unobserved* vertex, any point that avoids all supplied positions of the other vertices can be
  prescribed in an injective extension; `not_exists_injective_extension_prescribing_missing_of_collision`
  records the sharp converse that a point colliding with another vertex's supplied position
  cannot be prescribed;
* `knownInjective_map_toEuclideanPoint`, `exists_injective_extension_of_rational`: the exact
  rational-to-real bridge through `CartesianPoint3.toEuclideanPoint`;
* `knownInjective_of_embeddedGraph_agreement`: an `EmbeddedGraph` conformation that agrees with the
  supplied positions witnesses `KnownInjective p`;
* concrete cases: the empty vertex type (`empty_knownInjective`,
  `empty_exists_injective_extension`), the all-missing table
  (`knownInjective_of_all_missing`, `exists_injective_extension_of_all_missing`), an injective
  all-known table (`knownInjective_enumeratedPartialPosition`), and a five-vertex coplanar
  rational example with three supplied and two missing vertices.

## Scope

This is structural atom-position existence only.  It does not construct bond paths, does not
classify knots or links, asserts no energy or chemical realizability statement, and does not
duplicate the whole-graph embedding theory of `OrganicStereoEmbeddedGraphRealization`.  A
prescribed-position graph embedding can be composed with the completion once the former is
finalized; this module only supplies the total injective atom position it needs.
-/

namespace TetraStereo.OneCenter
namespace OrganicStereoPartialInjectivePositionExtension

noncomputable section

universe u v

/-! ## Partial and total atom positions, and the known-injectivity predicate -/

/-- A partial atom position: a vertex either has a supplied point of `EmbeddedReal3` or is still
missing. -/
abbrev PartialPosition (V : Type u) : Type u := V → Option EmbeddedReal3

/-- A total atom position.  This is definitionally the repository's
`MolecularConformation V = V → EuclideanSpace ℝ (Fin 3)`. -/
abbrev TotalPosition (V : Type u) : Type u := V → EmbeddedReal3

variable {V : Type u}

/-- **Known-injectivity** of a partial position: any two vertices that are supplied the same
point must be the same vertex.  Nothing is required of missing vertices or of distinct supplied
points.  The definition is stated for an arbitrary value type `X` so that it can also be applied
to exact rational position tables. -/
def KnownInjective {X : Type*} (p : V → Option X) : Prop :=
  ∀ ⦃a b : V⦄ ⦃x : X⦄, p a = some x → p b = some x → a = b

/-- `full` extends the partial position `p`: every supplied position is recovered exactly. -/
def Extends (p : PartialPosition V) (full : TotalPosition V) : Prop :=
  ∀ ⦃v : V⦄ ⦃x : EmbeddedReal3⦄, p v = some x → full v = x

/-- **Necessity.**  An injective total position that extends `p` witnesses known-injectivity of
`p`. -/
theorem knownInjective_of_extension {p : PartialPosition V} {full : TotalPosition V}
    (hext : Extends p full) (hinj : Function.Injective full) : KnownInjective p := by
  intro a b x ha hb
  exact hinj ((hext ha).trans (hext hb).symm)

/-- A conflicting pair of distinct vertices with the same supplied position makes
known-injectivity fail. -/
theorem not_knownInjective_of_conflict {p : PartialPosition V} {a b : V} (hne : a ≠ b)
    {x : EmbeddedReal3} (ha : p a = some x) (hb : p b = some x) : ¬ KnownInjective p := by
  intro hp
  exact hne (hp ha hb)

/-- **Conflict witness.**  Two distinct vertices supplied the same position have *no* injective
total extension at all. -/
theorem not_exists_injective_extension_of_conflict {p : PartialPosition V} {a b : V}
    (hne : a ≠ b) {x : EmbeddedReal3} (ha : p a = some x) (hb : p b = some x) :
    ¬ ∃ full : TotalPosition V, Extends p full ∧ Function.Injective full := by
  rintro ⟨full, hext, hinj⟩
  exact hne (knownInjective_of_extension hext hinj ha hb)

/-! ## The anchor point and the first-coordinate bound -/

/-- The canonical point with first coordinate `c` and remaining coordinates zero.  This is the
exact point used for missing vertices. -/
def anchor (c : ℝ) : EmbeddedReal3 :=
  EuclideanSpace.single (0 : Fin 3) c

/-- The first coordinate of an anchor is exactly the chosen parameter. -/
@[simp] theorem anchor_apply_zero (c : ℝ) : anchor c 0 = c := by
  simp [anchor]

/-- Anchors with different parameters are different points.  Only the first coordinate is used, so
the proof does not depend on the values of the other two coordinates. -/
theorem anchor_injective : Function.Injective anchor := by
  intro c d h
  have h0 : anchor c 0 = anchor d 0 := congrArg (fun q : EmbeddedReal3 => q 0) h
  simpa using h0

/-- A supplied injective position witnesses known-injectivity of any partial table whose supplied
values agree with it. -/
theorem knownInjective_of_injective_supplied {p : PartialPosition V} {f : TotalPosition V}
    (hf : Function.Injective f)
    (hp : ∀ (v : V) (x : EmbeddedReal3), p v = some x → x = f v) : KnownInjective p := by
  intro a b x ha hb
  exact hf ((hp a x ha).symm.trans (hp b x hb))

/-! ## The constructive completion for a finite vertex type -/

section Finite

variable [Fintype V]

/-- The finite sum of the absolute first coordinates of all supplied positions.  It bounds every
supplied first coordinate from above, including negative and irrational ones. -/
def knownFirstBound (p : PartialPosition V) : ℝ :=
  ∑ v : V, (match p v with
    | some x => |x 0|
    | none => 0)

/-- The bound is nonnegative. -/
theorem knownFirstBound_nonneg (p : PartialPosition V) : 0 ≤ knownFirstBound p := by
  rw [knownFirstBound]
  exact Finset.sum_nonneg (fun v _ => by
    cases p v with
    | none => exact le_rfl
    | some x => exact abs_nonneg (x 0))

/-- Every supplied absolute first coordinate is at most the bound. -/
theorem knownFirst_abs_le (p : PartialPosition V) {w : V} {x : EmbeddedReal3}
    (h : p w = some x) : |x 0| ≤ knownFirstBound p := by
  have hnonneg : ∀ v : V, 0 ≤ (match p v with
      | some y => |y 0|
      | none => (0 : ℝ)) := by
    intro v
    cases p v with
    | none => exact le_rfl
    | some y => exact abs_nonneg (y 0)
  have hterm :
      (match p w with
        | some y => |y 0|
        | none => (0 : ℝ)) ≤ knownFirstBound p := by
    rw [knownFirstBound]
    exact Finset.single_le_sum
      (f := fun v : V => (match p v with
        | some y => |y 0|
        | none => (0 : ℝ)))
      (fun v _ => hnonneg v) (Finset.mem_univ w)
  rw [h] at hterm
  exact hterm

/-- Every supplied first coordinate is at most the bound. -/
theorem knownFirst_le (p : PartialPosition V) {w : V} {x : EmbeddedReal3}
    (h : p w = some x) : x 0 ≤ knownFirstBound p :=
  (le_abs_self (x 0)).trans (knownFirst_abs_le p h)

/-- The first coordinate assigned to a missing vertex.  The additive constant `1` separates it
strictly above the whole supplied range, and the enumeration value separates missing vertices
from each other. -/
def missingFirst (p : PartialPosition V) (v : V) : ℝ :=
  knownFirstBound p + 1 + ((Fintype.equivFin V v).val : ℝ)

/-- Every missing first coordinate is strictly larger than the bound. -/
theorem knownFirstBound_lt_missingFirst (p : PartialPosition V) (v : V) :
    knownFirstBound p < missingFirst p v := by
  unfold missingFirst
  calc knownFirstBound p < knownFirstBound p + 1 := lt_add_one _
    _ ≤ knownFirstBound p + 1 + ((Fintype.equivFin V v).val : ℝ) :=
        le_add_of_nonneg_right (Nat.cast_nonneg _)

/-- Every supplied first coordinate is strictly smaller than every missing first coordinate. -/
theorem knownFirst_lt_missingFirst (p : PartialPosition V) {v w : V} {x : EmbeddedReal3}
    (hw : p w = some x) (_hv : p v = none) : x 0 < missingFirst p v :=
  lt_of_le_of_lt (knownFirst_le p hw) (knownFirstBound_lt_missingFirst p v)

/-- **The constructive completion.**  Supplied vertices keep their exact supplied point; a missing
vertex `v` is placed at `anchor (missingFirst p v)`, i.e. at
`(knownFirstBound p + 1 + (enum v).val, 0, 0)`. -/
def complete (p : PartialPosition V) : TotalPosition V :=
  fun v => match p v with
    | some x => x
    | none => anchor (missingFirst p v)

/-- Exact recovery of every supplied position. -/
@[simp] theorem complete_of_some {p : PartialPosition V} {v : V} {x : EmbeddedReal3}
    (h : p v = some x) : complete p v = x := by
  simp [complete, h]

/-- The explicit value at a missing vertex. -/
theorem complete_of_none {p : PartialPosition V} {v : V} (h : p v = none) :
    complete p v = anchor (missingFirst p v) := by
  simp [complete, h]

/-- The completion extends every supplied position. -/
theorem complete_extends (p : PartialPosition V) : Extends p (complete p) := by
  intro v x h
  exact complete_of_some h

/-- Every supplied first coordinate is strictly smaller than the first coordinate assigned to a
missing vertex. -/
theorem complete_known_lt_complete_missing (p : PartialPosition V) {v w : V}
    {x : EmbeddedReal3} (hw : p w = some x) (hv : p v = none) :
    x 0 < (complete p v) 0 := by
  rw [complete_of_none hv, anchor_apply_zero]
  exact knownFirst_lt_missingFirst p hw hv

/-- **Injectivity of the constructed completion**, assuming known-injectivity.  Supplied vertices
are handled by the hypothesis; a supplied vertex cannot collide with a missing one because its
first coordinate is below the bound while the missing first coordinate is above it; two missing
vertices cannot collide because their enumeration values are distinct. -/
theorem complete_injective (p : PartialPosition V) (hp : KnownInjective p) :
    Function.Injective (complete p) := by
  intro a b h
  cases ha : p a with
  | none =>
      cases hb : p b with
      | none =>
          have h0 : (complete p a) 0 = (complete p b) 0 :=
            congrArg (fun q : EmbeddedReal3 => q 0) h
          rw [complete_of_none ha, complete_of_none hb, anchor_apply_zero,
            anchor_apply_zero] at h0
          have hval : ((Fintype.equivFin V a).val : ℝ) =
              ((Fintype.equivFin V b).val : ℝ) := by
            unfold missingFirst at h0
            exact add_left_cancel h0
          have hnat : (Fintype.equivFin V a).val = (Fintype.equivFin V b).val :=
            Nat.cast_injective hval
          exact (Fintype.equivFin V).injective (Fin.ext hnat)
      | some y =>
          have h0 : (complete p a) 0 = (complete p b) 0 :=
            congrArg (fun q : EmbeddedReal3 => q 0) h
          rw [complete_of_none ha, complete_of_some hb, anchor_apply_zero] at h0
          have hlt : y 0 < missingFirst p a := knownFirst_lt_missingFirst p hb ha
          exact absurd h0.symm (ne_of_lt hlt)
  | some x =>
      cases hb : p b with
      | none =>
          have h0 : (complete p a) 0 = (complete p b) 0 :=
            congrArg (fun q : EmbeddedReal3 => q 0) h
          rw [complete_of_some ha, complete_of_none hb, anchor_apply_zero] at h0
          have hlt : x 0 < missingFirst p b := knownFirst_lt_missingFirst p ha hb
          exact absurd h0 (ne_of_lt hlt)
      | some y =>
          have hxy : x = y := by
            rw [← complete_of_some ha, ← complete_of_some hb]
            exact h
          rw [← hxy] at hb
          exact hp ha hb

/-- **Existence criterion.**  A partial position over a finite vertex type has an injective total
extension if and only if it is known-injective.  The forward direction is necessity; the reverse
direction is the explicit completion `complete`. -/
theorem exists_injective_extension_iff (p : PartialPosition V) :
    (∃ full : TotalPosition V, Extends p full ∧ Function.Injective full) ↔
      KnownInjective p := by
  constructor
  · rintro ⟨full, hext, hinj⟩
    exact knownInjective_of_extension hext hinj
  · intro hp
    exact ⟨complete p, complete_extends p, complete_injective p hp⟩

/-- The same existence criterion stated as nonemptiness of the subtype of injective extensions. -/
theorem nonempty_injective_extension_iff (p : PartialPosition V) :
    Nonempty {full : TotalPosition V // Extends p full ∧ Function.Injective full} ↔
      KnownInjective p := by
  constructor
  · rintro ⟨⟨full, hext, hinj⟩⟩
    exact knownInjective_of_extension hext hinj
  · intro hp
    exact ⟨⟨complete p, complete_extends p, complete_injective p hp⟩⟩

/-- The existence criterion with the completion typed directly as the repository's
`MolecularConformation V`.  The two types are definitionally equal. -/
theorem exists_injective_molecularConformation_iff (p : PartialPosition V) :
    (∃ c : MolecularConformation V, Extends p c ∧ Function.Injective c) ↔
      KnownInjective p :=
  exists_injective_extension_iff p

omit [Fintype V] in
/-- For a *total* known-injective partial position, every total extension is automatically
injective, so injectivity is equivalent to known-injectivity for any supplied extension. -/
theorem injective_of_knownInjective_of_total {p : PartialPosition V} {full : TotalPosition V}
    (hext : Extends p full) (htot : ∀ v : V, ∃ x : EmbeddedReal3, p v = some x)
    (hp : KnownInjective p) : Function.Injective full := by
  intro a b h
  obtain ⟨x, hx⟩ := htot a
  obtain ⟨y, hy⟩ := htot b
  have hxa : full a = x := hext hx
  have hyb : full b = y := hext hy
  have hxy : x = y := by
    rw [← hxa, ← hyb]
    exact h
  rw [← hxy] at hy
  exact hp hx hy

omit [Fintype V] in
/-- **All-known case.**  If the partial position is total, injectivity of a supplied extension is
equivalent to known-injectivity. -/
theorem injective_extension_iff_knownInjective_of_total {p : PartialPosition V}
    {full : TotalPosition V} (hext : Extends p full)
    (htot : ∀ v : V, ∃ x : EmbeddedReal3, p v = some x) :
    Function.Injective full ↔ KnownInjective p :=
  ⟨fun hinj => knownInjective_of_extension hext hinj,
   fun hp => injective_of_knownInjective_of_total hext htot hp⟩

/-! ### Prescribing a point at an unobserved vertex

At a vertex `v` with no supplied position, a chosen point `y` can be prescribed in an injective
extension exactly when `y` does not equal any supplied position of a *different* vertex.  The
construction prefills `v` with `y` and then applies the general existence criterion.  The
avoidance hypothesis is not redundant: a collision with another supplied position genuinely
obstructs injectivity. -/

/-- Replace the supplied position at `v` by the point `y`, leaving every other vertex unchanged.
The decidable equality required by the conditional is supplied classically, so the vertex type
needs no `DecidableEq` instance. -/
noncomputable def updatePosition (p : PartialPosition V) (v : V) (y : EmbeddedReal3) :
    PartialPosition V := by
  classical
  exact fun w => if w = v then some y else p w

omit [Fintype V] in
/-- Prefilling an unobserved vertex with an avoiding point preserves known-injectivity. -/
theorem knownInjective_update_missing (p : PartialPosition V) (hp : KnownInjective p)
    {v : V} (_hv : p v = none) {y : EmbeddedReal3}
    (havoid : ∀ ⦃w : V⦄ ⦃x : EmbeddedReal3⦄, w ≠ v → p w = some x → y ≠ x) :
    KnownInjective (updatePosition p v y) := by
  classical
  intro a b z ha hb
  by_cases hav : a = v
  · subst a
    simp [updatePosition] at ha
    by_cases hbv : b = v
    · subst b
      rfl
    · simp [updatePosition, hbv] at hb
      exfalso
      exact (havoid hbv hb) ha
  · simp [updatePosition, hav] at ha
    by_cases hbv : b = v
    · subst b
      simp [updatePosition] at hb
      exfalso
      exact (havoid hav ha) hb
    · simp [updatePosition, hbv] at hb
      exact hp ha hb

/-- **Prescribed point at an unobserved vertex.**  If `v` is missing from `p` and `y` avoids every
position supplied at a different vertex, then some injective total extension of `p` maps `v`
to `y`. -/
theorem exists_injective_extension_prescribing_missing (p : PartialPosition V)
    (hp : KnownInjective p) {v : V} (hv : p v = none) {y : EmbeddedReal3}
    (havoid : ∀ ⦃w : V⦄ ⦃x : EmbeddedReal3⦄, w ≠ v → p w = some x → y ≠ x) :
    ∃ full : TotalPosition V,
      Extends p full ∧ Function.Injective full ∧ full v = y := by
  classical
  let p' : PartialPosition V := updatePosition p v y
  have hp' : KnownInjective p' := knownInjective_update_missing p hp hv havoid
  obtain ⟨full, hext', hinj⟩ := (exists_injective_extension_iff p').mpr hp'
  have hfull : full v = y := hext' (by simp [p', updatePosition])
  have hext : Extends p full := by
    intro w x hw
    have hwv : w ≠ v := by
      rintro rfl
      rw [hv] at hw
      cases hw
    exact hext' (by simp [p', updatePosition, hwv, hw])
  exact ⟨full, hext, hinj, hfull⟩

omit [Fintype V] in
/-- **Sharp converse.**  If a point coincides with a position supplied at a different vertex,
then it cannot be prescribed at an unobserved vertex in any injective extension. -/
theorem not_exists_injective_extension_prescribing_missing_of_collision
    {p : PartialPosition V} {v w : V} (hne : w ≠ v) {x : EmbeddedReal3}
    (hw : p w = some x) :
    ¬ ∃ full : TotalPosition V,
      Extends p full ∧ Function.Injective full ∧ full v = x := by
  rintro ⟨full, hext, hinj, hfv⟩
  have hfw : full w = x := hext hw
  have hvw : v = w := hinj (hfv.trans hfw.symm)
  exact hne hvw.symm

/-! ### All-missing and all-known instances -/

omit [Fintype V] in
/-- The all-missing table is always known-injective. -/
theorem knownInjective_of_all_missing :
    KnownInjective (fun _ : V => (none : Option EmbeddedReal3)) := by
  intro a b x ha hb
  simp at ha

/-- The all-missing table always has an injective total extension. -/
theorem exists_injective_extension_of_all_missing :
    ∃ full : TotalPosition V,
      Extends (fun _ : V => (none : Option EmbeddedReal3)) full ∧ Function.Injective full :=
  (exists_injective_extension_iff _).mpr knownInjective_of_all_missing

/-- An explicit total position that supplies every vertex. -/
def enumeratedPartialPosition : PartialPosition V :=
  fun v => some (anchor ((Fintype.equivFin V v).val : ℝ))

/-- The explicit all-known table is known-injective. -/
theorem knownInjective_enumeratedPartialPosition :
    KnownInjective (enumeratedPartialPosition (V := V)) := by
  intro a b x ha hb
  simp only [enumeratedPartialPosition, Option.some.injEq] at ha hb
  have h : anchor ((Fintype.equivFin V a).val : ℝ) =
      anchor ((Fintype.equivFin V b).val : ℝ) := ha.trans hb.symm
  have hcast : ((Fintype.equivFin V a).val : ℝ) =
      ((Fintype.equivFin V b).val : ℝ) := anchor_injective h
  have hnat : (Fintype.equivFin V a).val = (Fintype.equivFin V b).val :=
    Nat.cast_injective hcast
  exact (Fintype.equivFin V).injective (Fin.ext hnat)

/-- The explicit all-known table is total. -/
theorem enumeratedPartialPosition_total :
    ∀ v : V, ∃ x : EmbeddedReal3, enumeratedPartialPosition v = some x :=
  fun v => ⟨anchor ((Fintype.equivFin V v).val : ℝ), rfl⟩

/-- The explicit all-known table has an injective total extension. -/
theorem exists_injective_extension_enumerated :
    ∃ full : TotalPosition V,
      Extends enumeratedPartialPosition full ∧ Function.Injective full :=
  (exists_injective_extension_iff _).mpr knownInjective_enumeratedPartialPosition

/-! ### Exact rational input through `CartesianPoint3.toEuclideanPoint` -/

/-- The rational-to-real coordinate cast introduces no identifications.  This is the exact
`CartesianPoint3.toEuclideanPoint_injective` API recorded as an iff for rewriting. -/
@[simp] theorem toEuclideanPoint_eq_iff (p q : CartesianPoint3) :
    p.toEuclideanPoint = q.toEuclideanPoint ↔ p = q :=
  CartesianPoint3.toEuclideanPoint_injective.eq_iff

omit [Fintype V] in
/-- Casting a partial rational position table into real three-space preserves known-injectivity in
both directions.  The reverse direction uses injectivity of `CartesianPoint3.toEuclideanPoint`. -/
theorem knownInjective_map_toEuclideanPoint {q : V → Option CartesianPoint3} :
    KnownInjective (fun v => (q v).map CartesianPoint3.toEuclideanPoint) ↔
      KnownInjective q := by
  constructor
  · intro h a b r ha hb
    exact h (Option.map_eq_some_iff.2 ⟨r, ha, rfl⟩)
      (Option.map_eq_some_iff.2 ⟨r, hb, rfl⟩)
  · intro h a b x ha hb
    rcases Option.map_eq_some_iff.1 ha with ⟨pa, hpa, hxa⟩
    rcases Option.map_eq_some_iff.1 hb with ⟨pb, hpb, hxb⟩
    have hpba : pb = pa :=
      CartesianPoint3.toEuclideanPoint_injective (hxb.trans hxa.symm)
    rw [hpba] at hpb
    exact h hpa hpb

/-- Existence of an injective real completion from a known-injective exact rational table. -/
theorem exists_injective_extension_of_rational {q : V → Option CartesianPoint3}
    (hq : KnownInjective q) :
    ∃ full : TotalPosition V,
      Extends (fun v => (q v).map CartesianPoint3.toEuclideanPoint) full ∧
        Function.Injective full :=
  (exists_injective_extension_iff _).mpr
    (knownInjective_map_toEuclideanPoint.mpr hq)

end Finite

/-! ## Empty vertex type -/

/-- The empty partial position. -/
def emptyPartialPosition : PartialPosition Empty := fun v => nomatch v

/-- The empty partial position is known-injective. -/
theorem empty_knownInjective : KnownInjective emptyPartialPosition := by
  intro a b x ha hb
  nomatch a

/-- The empty vertex type always has an injective total extension. -/
theorem empty_exists_injective_extension :
    ∃ full : TotalPosition Empty,
      Extends emptyPartialPosition full ∧ Function.Injective full :=
  (exists_injective_extension_iff emptyPartialPosition).mpr empty_knownInjective

/-! ## Concrete coplanar rational example

The vertex type has three supplied vertices and two missing vertices.  The supplied points are the
exact rational points `(0, 0, 0)`, `(1, 0, 0)` and `(2, 0, 0)` cast into real three-space by
`CartesianPoint3.toEuclideanPoint`.  They all have third coordinate zero, so they are coplanar
(they are in fact collinear).  The example is deliberately degenerate: no distinct-axis or
generic-position assumption is made. -/

/-- Five vertices: three with supplied rational positions and two missing. -/
inductive CoplanarVertex
  | known0
  | known1
  | known2
  | missing0
  | missing1
  deriving DecidableEq

/-- The five-element vertex type. -/
instance coplanarVertexFintype : Fintype CoplanarVertex :=
  Fintype.ofList [.known0, .known1, .known2, .missing0, .missing1] (by
    intro v
    cases v <;> decide)

/-- The first supplied coplanar rational point, `(0, 0, 0)`. -/
noncomputable def coplanarSupplied0 : EmbeddedReal3 :=
  CartesianPoint3.toEuclideanPoint ⟨0, 0, 0⟩

/-- The second supplied coplanar rational point, `(1, 0, 0)`. -/
noncomputable def coplanarSupplied1 : EmbeddedReal3 :=
  CartesianPoint3.toEuclideanPoint ⟨1, 0, 0⟩

/-- The third supplied coplanar rational point, `(2, 0, 0)`. -/
noncomputable def coplanarSupplied2 : EmbeddedReal3 :=
  CartesianPoint3.toEuclideanPoint ⟨2, 0, 0⟩

/-- A total injective position on the five vertices used to certify known-injectivity of the
partial table.  The supplied vertices carry the exact rational points; the two vertices that are
missing from the partial table are given anchor points with first coordinates `3` and `4`. -/
noncomputable def coplanarEmbedding : CoplanarVertex → EmbeddedReal3
  | .known0 => coplanarSupplied0
  | .known1 => coplanarSupplied1
  | .known2 => coplanarSupplied2
  | .missing0 => anchor 3
  | .missing1 => anchor 4

/-- The partial coplanar position: three supplied rational points and two missing vertices. -/
noncomputable def coplanarPartialPosition : PartialPosition CoplanarVertex
  | .known0 => some (coplanarEmbedding .known0)
  | .known1 => some (coplanarEmbedding .known1)
  | .known2 => some (coplanarEmbedding .known2)
  | .missing0 => none
  | .missing1 => none

/-- The auxiliary total position is injective.  All five points have pairwise distinct first
coordinates `0, 1, 2, 3, 4`, so only the first coordinate is needed. -/
theorem coplanarEmbedding_injective : Function.Injective coplanarEmbedding := by
  intro a b h
  have h0 : coplanarEmbedding a 0 = coplanarEmbedding b 0 :=
    congrArg (fun q : EmbeddedReal3 => q 0) h
  cases a <;> cases b <;>
    simp [coplanarEmbedding, coplanarSupplied0, coplanarSupplied1, coplanarSupplied2,
      CartesianPoint3.toEuclideanPoint_apply_zero, anchor] at h0 ⊢

/-- The concrete coplanar partial position is known-injective. -/
theorem coplanarPartialPosition_knownInjective :
    KnownInjective coplanarPartialPosition := by
  refine knownInjective_of_injective_supplied coplanarEmbedding_injective ?_
  intro v x h
  cases v <;> simp [coplanarPartialPosition] at h ⊢ <;> exact h.symm

/-- The concrete coplanar partial position has an injective total completion. -/
theorem coplanarPartialPosition_exists_injective_extension :
    ∃ full : TotalPosition CoplanarVertex,
      Extends coplanarPartialPosition full ∧ Function.Injective full :=
  (exists_injective_extension_iff _).mpr coplanarPartialPosition_knownInjective

/-- Exact recovery of the first supplied rational coordinate. -/
@[simp] theorem complete_coplanar_known0 :
    complete coplanarPartialPosition .known0 = coplanarSupplied0 :=
  complete_of_some (p := coplanarPartialPosition) (v := .known0) (x := coplanarSupplied0) rfl

/-- Exact recovery of the second supplied rational coordinate. -/
@[simp] theorem complete_coplanar_known1 :
    complete coplanarPartialPosition .known1 = coplanarSupplied1 :=
  complete_of_some (p := coplanarPartialPosition) (v := .known1) (x := coplanarSupplied1) rfl

/-- Exact recovery of the third supplied rational coordinate. -/
@[simp] theorem complete_coplanar_known2 :
    complete coplanarPartialPosition .known2 = coplanarSupplied2 :=
  complete_of_some (p := coplanarPartialPosition) (v := .known2) (x := coplanarSupplied2) rfl

/-- The first coordinate assigned to the first missing vertex. -/
theorem complete_coplanar_missing0_first :
    (complete coplanarPartialPosition .missing0) 0 =
      knownFirstBound coplanarPartialPosition + 1 +
        ((Fintype.equivFin CoplanarVertex .missing0).val : ℝ) := by
  rw [complete_of_none (p := coplanarPartialPosition) (v := .missing0) rfl, anchor_apply_zero]
  unfold missingFirst
  rfl

/-- The first coordinate assigned to the second missing vertex. -/
theorem complete_coplanar_missing1_first :
    (complete coplanarPartialPosition .missing1) 0 =
      knownFirstBound coplanarPartialPosition + 1 +
        ((Fintype.equivFin CoplanarVertex .missing1).val : ℝ) := by
  rw [complete_of_none (p := coplanarPartialPosition) (v := .missing1) rfl, anchor_apply_zero]
  unfold missingFirst
  rfl

/-- A supplied first coordinate is strictly below the first coordinate of a missing vertex. -/
theorem coplanar_missing_above_known :
    coplanarSupplied0 0 < (complete coplanarPartialPosition .missing0) 0 :=
  complete_known_lt_complete_missing (p := coplanarPartialPosition) (v := .missing0)
    (w := .known0) (x := coplanarSupplied0) rfl rfl

/-- The constructed completion of the coplanar example is injective. -/
theorem coplanarComplete_injective :
    Function.Injective (complete coplanarPartialPosition) :=
  complete_injective coplanarPartialPosition coplanarPartialPosition_knownInjective

/-- **Conflict witness.**  The constant partial position over two distinct vertices has no
injective total extension. -/
theorem coplanar_conflict :
    ¬ ∃ full : TotalPosition (Fin 2),
      Extends (fun _ : Fin 2 => some (anchor 0)) full ∧ Function.Injective full :=
  not_exists_injective_extension_of_conflict
    (p := fun _ : Fin 2 => some (anchor 0)) (a := 0) (b := 1)
    (by decide) rfl rfl

/-! ## Composition with the embedded-graph conformation

The following theorem is the only interface needed to combine this structural completion with the
established whole-graph embedding theory.  It does not reprove any graph embedding statement: it
applies `EmbeddedGraph.atom_injective` to the agreement of a supplied partial table with the
graph's total conformation. -/

/-- If an `EmbeddedGraph` conformation agrees with every supplied position, then the partial
position is known-injective. -/
theorem knownInjective_of_embeddedGraph_agreement {E : Type v}
    {src dst : E → V}
    (G : OrganicStereoEmbeddedGraphRealization.EmbeddedGraph src dst)
    {p : PartialPosition V}
    (h : ∀ ⦃v : V⦄ ⦃x : EmbeddedReal3⦄, p v = some x → G.conformation v = x) :
    KnownInjective p :=
  knownInjective_of_extension h G.atom_injective

/-! ## Kernel-authority checks

These commands check that the closures of the constructive endpoints use only the standard logical
principles `propext`, `Classical.choice` and `Quot.sound`.  No proof placeholder, project-level
assumption, evaluator trust or compiler trust is permitted. -/

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.anchor
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.anchor_injective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.knownInjective_of_extension
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.not_knownInjective_of_conflict
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.not_exists_injective_extension_of_conflict
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.knownFirstBound
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.knownFirstBound_nonneg
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.knownFirst_abs_le
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.knownFirst_le
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.missingFirst
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.knownFirstBound_lt_missingFirst
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.knownFirst_lt_missingFirst
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.complete
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.complete_of_some
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.complete_of_none
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.complete_extends
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.complete_known_lt_complete_missing
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.complete_injective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.exists_injective_extension_iff
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.nonempty_injective_extension_iff
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.exists_injective_molecularConformation_iff
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.injective_extension_iff_knownInjective_of_total
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.knownInjective_update_missing
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.exists_injective_extension_prescribing_missing
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.not_exists_injective_extension_prescribing_missing_of_collision
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.knownInjective_of_all_missing
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.exists_injective_extension_of_all_missing
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.knownInjective_enumeratedPartialPosition
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.exists_injective_extension_enumerated
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.toEuclideanPoint_eq_iff
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.knownInjective_map_toEuclideanPoint
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.exists_injective_extension_of_rational
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.emptyPartialPosition
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.empty_knownInjective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.empty_exists_injective_extension
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.coplanarVertexFintype
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.coplanarEmbedding
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.coplanarEmbedding_injective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.coplanarPartialPosition
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.coplanarPartialPosition_knownInjective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.coplanarPartialPosition_exists_injective_extension
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.complete_coplanar_known0
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.complete_coplanar_known1
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.complete_coplanar_known2
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.complete_coplanar_missing0_first
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.complete_coplanar_missing1_first
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.coplanar_missing_above_known
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.coplanarComplete_injective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.coplanar_conflict
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension.knownInjective_of_embeddedGraph_agreement

end

end OrganicStereoPartialInjectivePositionExtension
end TetraStereo.OneCenter
