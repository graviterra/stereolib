import TetraStereo.OneCenter.OrganicStereoRealConfiguration
import TetraStereo.OneCenter.IUPACP93MonocyclicAuthorityCarrier

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

/-!
# Real ring-conformation views of source-bound closed cycles

This module is a representation component.  It binds an arbitrary simple closed traversal of the
atoms of a certified `AuthoritativeChemicalInput` to the full real geometric configuration supplied
by `OrganicStereoRealConfiguration.RealSourceGeometry`.

The traversal is not restricted to a fixed ring length: it is any list of at least three pairwise
distinct atoms whose consecutive incidences (including the closing incidence) are the source's
binary bonds, exactly as recorded by the existing `P93AuthorityClosedCycle` relation.  Extra
chords are allowed; no chordless, mean-plane, chair/boat/skew or other conformational-name
hypothesis is introduced.  The finite view lists the complete three-dimensional real point of every
ring atom in an ordered enumeration of the whole cycle.  No scalar torsion, bond-length or bond-angle
summary replaces those points, and no tolerance or plane heuristic is used.

Cyclic shifts and reversal act only by reindexing the complete ordered cycle: they preserve the
source geometry and permute the ordered positions.  General arbitrary permutations are deliberately
not presented as path-preserving operations.

The optional rational P-94 torsion-quadruple view is not implemented here; nothing in this module
requires rational coordinates, nondegeneracy, or noncollinearity of any four points.
-/

/-! ## Cyclic reindexing of a finite cycle -/

/-- The position `i + k` on a finite cycle of length `n`, computed as a natural-number residue.
The definition is total; for `n = 0` there is no position to shift. -/
def cyclicShiftIndex (n k : ℕ) (i : Fin n) : Fin n :=
  ⟨(i.val + k) % n, Nat.mod_lt _ i.pos⟩

/-- The value of a cyclic shift is the expected residue. -/
@[simp] theorem cyclicShiftIndex_val (n k : ℕ) (i : Fin n) :
    (cyclicShiftIndex n k i).val = (i.val + k) % n := rfl

/-- Two cyclic shifts compose by adding their amounts. -/
theorem cyclicShiftIndex_comp (n k l : ℕ) (i : Fin n) :
    cyclicShiftIndex n k (cyclicShiftIndex n l i) = cyclicShiftIndex n (l + k) i := by
  apply Fin.ext
  show (((i.val + l) % n) + k) % n = (i.val + (l + k)) % n
  rw [Nat.mod_add_mod, Nat.add_assoc]

/-- Shifting by zero is the identity. -/
theorem cyclicShiftIndex_zero (n : ℕ) (i : Fin n) :
    cyclicShiftIndex n 0 i = i := by
  apply Fin.ext
  show (i.val + 0) % n = i.val
  rw [Nat.add_zero, Nat.mod_eq_of_lt i.isLt]

/-- Shifting by `k` is undone by shifting by `n - k % n` on the left. -/
theorem cyclicShiftIndex_neg (n k : ℕ) (i : Fin n) :
    cyclicShiftIndex n (n - k % n) (cyclicShiftIndex n k i) = i := by
  apply Fin.ext
  show (((i.val + k) % n + (n - k % n)) % n) = i.val
  rw [Nat.mod_add_mod]
  have hsum : i.val + k + (n - k % n) = (i.val + n) + n * (k / n) := by
    have hdiv : k % n + n * (k / n) = k := Nat.mod_add_div k n
    have hle : k % n ≤ n := by
      rcases Nat.eq_zero_or_pos n with zeroCase | positiveCase
      · subst n
        exact absurd i.isLt (Nat.not_lt_zero _)
      · exact Nat.le_of_lt (Nat.mod_lt _ positiveCase)
    have i_lt : i.val < n := i.isLt
    omega
  rw [hsum, Nat.add_mul_mod_self_left, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

/-- Shifting by `k` is undone by shifting by `n - k % n` on the right. -/
theorem cyclicShiftIndex_comp_neg (n k : ℕ) (i : Fin n) :
    cyclicShiftIndex n k (cyclicShiftIndex n (n - k % n) i) = i := by
  apply Fin.ext
  show (((i.val + (n - k % n)) % n + k) % n) = i.val
  rw [Nat.mod_add_mod]
  have hsum : i.val + (n - k % n) + k = (i.val + n) + n * (k / n) := by
    have hdiv : k % n + n * (k / n) = k := Nat.mod_add_div k n
    have hle : k % n ≤ n := by
      rcases Nat.eq_zero_or_pos n with zeroCase | positiveCase
      · subst n
        exact absurd i.isLt (Nat.not_lt_zero _)
      · exact Nat.le_of_lt (Nat.mod_lt _ positiveCase)
    have i_lt : i.val < n := i.isLt
    omega
  rw [hsum, Nat.add_mul_mod_self_left, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

/-- Cyclic shift by `k` as a permutation of the complete cycle. -/
def cyclicShiftPerm (n k : ℕ) : Equiv.Perm (Fin n) where
  toFun := cyclicShiftIndex n k
  invFun := cyclicShiftIndex n (n - k % n)
  left_inv := cyclicShiftIndex_neg n k
  right_inv := cyclicShiftIndex_comp_neg n k

/-- Evaluation of a cyclic shift permutation is the underlying index shift. -/
@[simp] theorem cyclicShiftPerm_apply (n k : ℕ) (i : Fin n) :
    cyclicShiftPerm n k i = cyclicShiftIndex n k i := rfl

/-- The zero shift is the identity permutation. -/
theorem cyclicShiftPerm_zero (n : ℕ) :
    cyclicShiftPerm n 0 = Equiv.refl (Fin n) := by
  apply Equiv.ext
  intro i
  exact cyclicShiftIndex_zero n i

/-- Composition of cyclic shifts adds their amounts. -/
theorem cyclicShiftPerm_trans (n k l : ℕ) :
    (cyclicShiftPerm n k).trans (cyclicShiftPerm n l) =
      cyclicShiftPerm n (k + l) := by
  apply Equiv.ext
  intro i
  show cyclicShiftIndex n l (cyclicShiftIndex n k i) = cyclicShiftIndex n (k + l) i
  exact cyclicShiftIndex_comp n l k i

/-- A shift followed by the complementary shift is the identity. -/
theorem cyclicShiftPerm_self_inverse (n k : ℕ) :
    (cyclicShiftPerm n k).trans (cyclicShiftPerm n (n - k % n)) =
      Equiv.refl (Fin n) := by
  apply Equiv.ext
  intro i
  show cyclicShiftIndex n (n - k % n) (cyclicShiftIndex n k i) = i
  exact cyclicShiftIndex_neg n k i

/-- The complementary shift followed by the original shift is the identity. -/
theorem cyclicShiftPerm_neg_trans (n k : ℕ) :
    (cyclicShiftPerm n (n - k % n)).trans (cyclicShiftPerm n k) =
      Equiv.refl (Fin n) := by
  apply Equiv.ext
  intro i
  show cyclicShiftIndex n k (cyclicShiftIndex n (n - k % n) i) = i
  exact cyclicShiftIndex_comp_neg n k i

/-! ## Source-bound closed ring traversals -/

/-- An arbitrary simple closed traversal of the atoms of a certified source.  The traversal is
exactly one existing `P93AuthorityClosedCycle`: at least three pairwise distinct bounded atoms and
binary-bond incidences along every consecutive pair, including the closing pair.  Chords and any
conformational profile are permitted. -/
structure OrganicRingTraversal (source : CertifiedAuthoritativeChemicalInput) where
  ringAtoms : List Nat
  closedCycle : P93AuthorityClosedCycle source.input ringAtoms

namespace OrganicRingTraversal

variable {source : CertifiedAuthoritativeChemicalInput}

/-- The traversal has at least three atoms. -/
theorem length_ge_three (traversal : OrganicRingTraversal source) :
    3 ≤ traversal.ringAtoms.length :=
  traversal.closedCycle.1

/-- The traversal is nonempty. -/
theorem length_pos (traversal : OrganicRingTraversal source) :
    0 < traversal.ringAtoms.length :=
  Nat.lt_of_lt_of_le (by decide) traversal.length_ge_three

/-- The traversal has no repeated atom. -/
theorem nodup (traversal : OrganicRingTraversal source) :
    traversal.ringAtoms.Nodup :=
  traversal.closedCycle.2.1

/-- Every traversed atom is a genuine bounded atom index of the source molecule. -/
theorem bounded (traversal : OrganicRingTraversal source) :
    P93AuthorityAtomsBounded source.input traversal.ringAtoms :=
  traversal.closedCycle.2.2.1

/-- The closing incidences are actual source binary bonds. -/
theorem closed_path (traversal : OrganicRingTraversal source) :
    ∃ first remaining,
      traversal.ringAtoms = first :: remaining ∧
        P93AuthorityConnectedPath source.input (traversal.ringAtoms ++ [first]) :=
  traversal.closedCycle.2.2.2

/-- The dependent source index of a member atom. -/
def atomIndex (traversal : OrganicRingTraversal source) (atom : Nat)
    (member : atom ∈ traversal.ringAtoms) : SourceAtomIndex source :=
  ⟨atom, traversal.bounded atom member⟩

/-- The value of an indexed member atom is that same source atom number. -/
@[simp] theorem atomIndex_val (traversal : OrganicRingTraversal source) (atom : Nat)
    (member : atom ∈ traversal.ringAtoms) :
    (traversal.atomIndex atom member).val = atom := rfl

/-- The dependent source index at a cycle position. -/
def indexAt (traversal : OrganicRingTraversal source)
    (position : Fin traversal.ringAtoms.length) : SourceAtomIndex source :=
  traversal.atomIndex (traversal.ringAtoms.get position) (List.get_mem _ _)

/-- The value of the index at a cycle position is the atom stored there. -/
@[simp] theorem indexAt_val (traversal : OrganicRingTraversal source)
    (position : Fin traversal.ringAtoms.length) :
    (traversal.indexAt position).val = traversal.ringAtoms.get position := rfl

/-- The index at a cycle position names a member atom. -/
theorem indexAt_mem (traversal : OrganicRingTraversal source)
    (position : Fin traversal.ringAtoms.length) :
    (traversal.indexAt position).val ∈ traversal.ringAtoms :=
  List.get_mem _ _

/-- Distinct cycle positions name distinct source atoms. -/
theorem indexAt_injective (traversal : OrganicRingTraversal source) :
    Function.Injective traversal.indexAt := by
  intro first second equal
  have values : traversal.ringAtoms.get first = traversal.ringAtoms.get second := by
    simpa using congrArg (fun index : SourceAtomIndex source => index.val) equal
  exact (traversal.nodup.get_inj_iff).mp values

end OrganicRingTraversal

/-! ## Full real conformation views -/

/-- A finite real conformation view of a source-bound closed ring.  The `geometry` field is the
complete `RealSourceGeometry`, so every atom of the source, including every off-ring atom, retains
its full three-dimensional real point.  The permutation `order` only reindexes the complete ordered
cycle; it never replaces a point by a derived scalar and never discards the source. -/
structure OrganicRingConformationView (source : CertifiedAuthoritativeChemicalInput)
    (traversal : OrganicRingTraversal source) where
  /-- The complete source-indexed real geometry. -/
  geometry : RealSourceGeometry source
  /-- A complete reindexing of the ordered cycle positions.  This is an arbitrary coordinate
  enumeration of the cycle: it need not preserve bond adjacency, and no claim is made that it
  does.  The path-preserving operations are `rotate` and `reverse`, whose atom-order effects are
  proved below. -/
  order : Equiv.Perm (Fin traversal.ringAtoms.length)

namespace OrganicRingConformationView

variable {source : CertifiedAuthoritativeChemicalInput}
variable {traversal : OrganicRingTraversal source}

/-- Views are determined by their full geometry and their cycle reindexing. -/
@[ext] theorem ext {first second : OrganicRingConformationView source traversal}
    (geometry : first.geometry = second.geometry) (order : first.order = second.order) :
    first = second := by
  cases first with
  | mk firstGeometry firstOrder =>
      cases second with
      | mk secondGeometry secondOrder =>
          simp_all

/-- The canonical view of a complete real geometry: the identity cyclic enumeration. -/
def ofGeometry (source : CertifiedAuthoritativeChemicalInput)
    (traversal : OrganicRingTraversal source) (geometry : RealSourceGeometry source) :
    OrganicRingConformationView source traversal where
  geometry := geometry
  order := Equiv.refl _

/-- The geometry of the canonical view is the supplied geometry. -/
@[simp] theorem ofGeometry_geometry (source : CertifiedAuthoritativeChemicalInput)
    (traversal : OrganicRingTraversal source) (geometry : RealSourceGeometry source) :
    (ofGeometry source traversal geometry).geometry = geometry := rfl

/-- The canonical view uses the identity permutation. -/
@[simp] theorem ofGeometry_order (source : CertifiedAuthoritativeChemicalInput)
    (traversal : OrganicRingTraversal source) (geometry : RealSourceGeometry source) :
    (ofGeometry source traversal geometry).order =
      (Equiv.refl (Fin traversal.ringAtoms.length)) := rfl

/-- The complete real configuration carried by a view. -/
def fullGeometry (view : OrganicRingConformationView source traversal) :
    RealSourceGeometry source :=
  view.geometry

/-- The full configuration projection is exactly the view's geometry. -/
@[simp] theorem fullGeometry_eq (view : OrganicRingConformationView source traversal) :
    view.fullGeometry = view.geometry := rfl

/-- The full configuration still carries exactly the certified source. -/
@[simp] theorem fullGeometry_sourceOf (view : OrganicRingConformationView source traversal) :
    view.fullGeometry.sourceOf = source := rfl

/-- The dependent source atom viewed at a cycle position. -/
def atomAt (view : OrganicRingConformationView source traversal)
    (position : Fin traversal.ringAtoms.length) : SourceAtomIndex source :=
  traversal.indexAt (view.order position)

/-- The value of the viewed atom at a cycle position. -/
@[simp] theorem atomAt_val (view : OrganicRingConformationView source traversal)
    (position : Fin traversal.ringAtoms.length) :
    (view.atomAt position).val = traversal.ringAtoms.get (view.order position) := rfl

/-- The source atom numbers in the view's ordered enumeration.  This records the actual ordered
atom cycle carried by the view.  The permutation `order` chooses the coordinate enumeration; it
need not preserve bond adjacency, and no theorem below claims that an arbitrary `order` does. -/
def atomOrder (view : OrganicRingConformationView source traversal) : List Nat :=
  List.ofFn fun position => (view.atomAt position).val

/-- The atom order has one entry per cycle position. -/
@[simp] theorem atomOrder_length (view : OrganicRingConformationView source traversal) :
    view.atomOrder.length = traversal.ringAtoms.length :=
  List.length_ofFn

/-- An arbitrary reindexing only permutes the ring atoms: it never invents an atom, drops one, or
changes which atoms belong to the ring.  This theorem says nothing about preserving adjacency; an
arbitrary `order` is an enumeration, not a path operation. -/
theorem atomOrder_perm (view : OrganicRingConformationView source traversal) :
    view.atomOrder.Perm traversal.ringAtoms := by
  have representation : view.atomOrder =
      List.ofFn (fun position => traversal.ringAtoms.get (view.order position)) := by
    unfold atomOrder
    congr 1
  rw [representation]
  have permuted := Equiv.Perm.ofFn_comp_perm view.order
    (fun position : Fin traversal.ringAtoms.length => traversal.ringAtoms.get position)
  simpa [Function.comp_def, List.ofFn_get] using permuted

/-- The canonical view enumerates exactly the stored traversal, in its stored order. -/
@[simp] theorem atomOrder_ofGeometry (source : CertifiedAuthoritativeChemicalInput)
    (traversal : OrganicRingTraversal source) (geometry : RealSourceGeometry source) :
    (ofGeometry source traversal geometry).atomOrder = traversal.ringAtoms := by
  unfold atomOrder
  have indices : (fun position : Fin traversal.ringAtoms.length =>
      ((ofGeometry source traversal geometry).atomAt position).val) =
      traversal.ringAtoms.get := by
    funext position
    rfl
  rw [indices, List.ofFn_get]

/-- Every viewed atom is a ring atom. -/
theorem atomAt_mem (view : OrganicRingConformationView source traversal)
    (position : Fin traversal.ringAtoms.length) :
    (view.atomAt position).val ∈ traversal.ringAtoms :=
  List.get_mem _ _

/-- The exact full three-dimensional real point viewed at a cycle position. -/
def point (view : OrganicRingConformationView source traversal)
    (position : Fin traversal.ringAtoms.length) : EuclideanSpace ℝ (Fin 3) :=
  view.geometry.conformation (view.atomAt position)

/-- The viewed point is exactly the conformation value at the viewed source atom. -/
@[simp] theorem point_eq_conformation (view : OrganicRingConformationView source traversal)
    (position : Fin traversal.ringAtoms.length) :
    view.point position = view.geometry.conformation (view.atomAt position) := rfl

/-- The canonical view's point at a cycle position is the source-indexed conformation there. -/
@[simp] theorem ofGeometry_point (source : CertifiedAuthoritativeChemicalInput)
    (traversal : OrganicRingTraversal source) (geometry : RealSourceGeometry source)
    (position : Fin traversal.ringAtoms.length) :
    (ofGeometry source traversal geometry).point position =
      geometry.conformation (traversal.indexAt position) := rfl

/-- The finite coordinate list of the complete ordered cycle. -/
def points (view : OrganicRingConformationView source traversal) :
    List (EuclideanSpace ℝ (Fin 3)) :=
  List.ofFn view.point

/-- The finite coordinate list has exactly one entry per ring atom. -/
@[simp] theorem points_length (view : OrganicRingConformationView source traversal) :
    view.points.length = traversal.ringAtoms.length :=
  List.length_ofFn

/-- Exact positional lookup in the finite coordinate list. -/
@[simp] theorem points_get (view : OrganicRingConformationView source traversal)
    (position : Fin view.points.length) :
    view.points.get position =
      view.point ⟨position.val, by simpa [points] using position.isLt⟩ := by
  simp [points, List.get_eq_getElem]

/-- Distinct cycle positions name distinct source atoms under the view's reindexing. -/
theorem atomAt_injective (view : OrganicRingConformationView source traversal) :
    Function.Injective view.atomAt := by
  intro first second equal
  exact view.order.injective (traversal.indexAt_injective equal)

/-- The viewed atom indices are exactly the ring atoms: the ordered cycle is complete. -/
theorem atomAt_range_iff (view : OrganicRingConformationView source traversal)
    (atom : SourceAtomIndex source) :
    (∃ position, view.atomAt position = atom) ↔ atom.val ∈ traversal.ringAtoms := by
  constructor
  · rintro ⟨position, rfl⟩
    exact List.get_mem _ _
  · intro member
    obtain ⟨position, observed⟩ := List.get_of_mem member
    refine ⟨view.order.symm position, ?_⟩
    simp only [atomAt, Equiv.apply_symm_apply]
    apply Fin.ext
    simpa [OrganicRingTraversal.indexAt] using observed

/-- Every ring atom occurs at exactly one viewed cycle position. -/
theorem atomAt_existsUnique (view : OrganicRingConformationView source traversal)
    {atom : SourceAtomIndex source} (member : atom.val ∈ traversal.ringAtoms) :
    ∃! position, view.atomAt position = atom := by
  have existence : ∃ position, view.atomAt position = atom :=
    (view.atomAt_range_iff atom).mpr member
  refine ⟨Classical.choose existence, Classical.choose_spec existence, ?_⟩
  intro other otherEqual
  exact view.atomAt_injective (otherEqual.trans (Classical.choose_spec existence).symm)

/-- Exact membership theorem for the finite coordinate view: a point belongs to the view if and
only if it is the full conformation value at some ring atom.  There are no invented coordinates and
no ring atom is omitted. -/
theorem mem_points_iff (view : OrganicRingConformationView source traversal)
    (point : EuclideanSpace ℝ (Fin 3)) :
    point ∈ view.points ↔
      ∃ (atom : Nat) (member : atom ∈ traversal.ringAtoms),
        view.geometry.conformation (traversal.atomIndex atom member) = point := by
  constructor
  · intro present
    have presentList : point ∈ List.ofFn view.point := present
    rw [List.mem_ofFn] at presentList
    obtain ⟨position, equality⟩ := presentList
    refine ⟨traversal.ringAtoms.get (view.order position), List.get_mem _ _, ?_⟩
    rw [← equality]
    simp only [OrganicRingConformationView.point, atomAt]
    congr 1
  · rintro ⟨atom, member, rfl⟩
    have goalList : view.geometry.conformation (traversal.atomIndex atom member) ∈
        List.ofFn view.point := by
      rw [List.mem_ofFn]
      obtain ⟨position, observed⟩ := List.get_of_mem member
      obtain ⟨viewPosition, viewObserved⟩ := view.order.surjective position
      refine ⟨viewPosition, ?_⟩
      simp only [OrganicRingConformationView.point, atomAt, viewObserved]
      congr 1
      apply Fin.ext
      simpa [OrganicRingTraversal.indexAt, OrganicRingTraversal.atomIndex] using observed
    exact goalList

/-- Every ring atom's exact full real point is present in the finite view. -/
theorem ringAtom_point_mem (view : OrganicRingConformationView source traversal)
    (atom : Nat) (member : atom ∈ traversal.ringAtoms) :
    view.geometry.conformation (traversal.atomIndex atom member) ∈ view.points :=
  (view.mem_points_iff _).mpr ⟨atom, member, rfl⟩

/-- Every viewed point comes from an actual ring atom. -/
theorem point_has_ringAtom_source (view : OrganicRingConformationView source traversal)
    (position : Fin traversal.ringAtoms.length) :
    ∃ (atom : Nat) (member : atom ∈ traversal.ringAtoms),
      view.point position = view.geometry.conformation (traversal.atomIndex atom member) :=
  ⟨traversal.ringAtoms.get (view.order position), List.get_mem _ _,
    by
      simp only [OrganicRingConformationView.point, atomAt]
      congr 1⟩

/-- The view is both sound and complete for the ring: its points are exactly the exact source
conformation values at the ring atoms. -/
theorem points_sound_and_complete (view : OrganicRingConformationView source traversal) :
    (∀ (atom : Nat) (member : atom ∈ traversal.ringAtoms),
        view.geometry.conformation (traversal.atomIndex atom member) ∈ view.points) ∧
      (∀ point ∈ view.points,
        ∃ (atom : Nat) (member : atom ∈ traversal.ringAtoms),
          view.geometry.conformation (traversal.atomIndex atom member) = point) :=
  ⟨view.ringAtom_point_mem, fun point present => (view.mem_points_iff point).mp present⟩

/-! ### Atom enumeration -/

/-- Enumerate the complete ordered cycle by an arbitrary finite index type. -/
def enumeratedPoints (view : OrganicRingConformationView source traversal) {ι : Type*}
    (equivalent : Fin traversal.ringAtoms.length ≃ ι) :
    ι → EuclideanSpace ℝ (Fin 3) :=
  fun index => view.point (equivalent.symm index)

/-- Evaluation of an enumerated point. -/
@[simp] theorem enumeratedPoints_apply (view : OrganicRingConformationView source traversal)
    {ι : Type*} (equivalent : Fin traversal.ringAtoms.length ≃ ι) (index : ι) :
    view.enumeratedPoints equivalent index = view.point (equivalent.symm index) := rfl

/-- Enumerating along the equivalence preserves every point. -/
@[simp] theorem enumeratedPoints_enumeration (view : OrganicRingConformationView source traversal)
    {ι : Type*} (equivalent : Fin traversal.ringAtoms.length ≃ ι)
    (position : Fin traversal.ringAtoms.length) :
    view.enumeratedPoints equivalent (equivalent position) = view.point position := by
  simp [enumeratedPoints]

/-- Inverse transport of an independent finite enumeration: enumerating with the inverse
equivalence recovers the original point family. -/
theorem enumeratedPoints_inverse (view : OrganicRingConformationView source traversal)
    {ι : Type*} (equivalent : Fin traversal.ringAtoms.length ≃ ι) :
    (fun position => view.enumeratedPoints equivalent (equivalent position)) = view.point := by
  funext position
  simp

/-- Transport the full source-indexed conformation along a bijection of atom indices.  This reuses
the stable `MolecularConformation.reindex` API and keeps the complete real geometry. -/
def enumeratedConformation (view : OrganicRingConformationView source traversal) {ι : Type*}
    (equivalent : SourceAtomIndex source ≃ ι) : MolecularConformation ι :=
  MolecularConformation.reindex equivalent view.geometry.conformation

/-- Evaluation of an enumerated full conformation. -/
@[simp] theorem enumeratedConformation_apply (view : OrganicRingConformationView source traversal)
    {ι : Type*} (equivalent : SourceAtomIndex source ≃ ι) (index : ι) :
    view.enumeratedConformation equivalent index =
      view.geometry.conformation (equivalent.symm index) := rfl

/-- Every viewed ring point is preserved by an independent atom enumeration. -/
@[simp] theorem enumeratedConformation_ringPoint
    (view : OrganicRingConformationView source traversal) {ι : Type*}
    (equivalent : SourceAtomIndex source ≃ ι)
    (position : Fin traversal.ringAtoms.length) :
    view.enumeratedConformation equivalent (equivalent (view.atomAt position)) =
      view.point position := by
  simp [enumeratedConformation, MolecularConformation.reindex]

/-- Inverse transport of an atom enumeration recovers the full source-indexed conformation. -/
theorem enumeratedConformation_inverse
    (view : OrganicRingConformationView source traversal) {ι : Type*}
    (equivalent : SourceAtomIndex source ≃ ι) :
    MolecularConformation.reindex equivalent.symm
        (view.enumeratedConformation equivalent) = view.geometry.conformation :=
  MolecularConformation.reindex_reindex equivalent view.geometry.conformation

/-- An independent atom enumeration remains injective on conformations. -/
theorem enumeratedConformation_injective
    (_view : OrganicRingConformationView source traversal) {ι : Type*}
    (equivalent : SourceAtomIndex source ≃ ι) :
    Function.Injective (fun conformation : SourceConformation source =>
      MolecularConformation.reindex equivalent conformation) :=
  MolecularConformation.reindex_injective equivalent

/-! ### Cyclic shifts of the complete ordered cycle -/

/-- Rotate the complete ordered cycle by `k` positions.  Only the cycle reindexing changes; the
full real geometry and the source are untouched. -/
def rotate (view : OrganicRingConformationView source traversal) (k : ℕ) :
    OrganicRingConformationView source traversal where
  geometry := view.geometry
  order := (cyclicShiftPerm traversal.ringAtoms.length k).trans view.order

/-- Rotation preserves the full geometry. -/
@[simp] theorem rotate_geometry (view : OrganicRingConformationView source traversal) (k : ℕ) :
    (view.rotate k).geometry = view.geometry := rfl

/-- The reindexing performed by a rotation. -/
@[simp] theorem rotate_order (view : OrganicRingConformationView source traversal) (k : ℕ) :
    (view.rotate k).order =
      (cyclicShiftPerm traversal.ringAtoms.length k).trans view.order := rfl

/-- The atom viewed after a rotation is the atom at the shifted cycle position. -/
@[simp] theorem rotate_atomAt (view : OrganicRingConformationView source traversal) (k : ℕ)
    (position : Fin traversal.ringAtoms.length) :
    (view.rotate k).atomAt position =
      view.atomAt (cyclicShiftIndex traversal.ringAtoms.length k position) := rfl

/-- Point preservation under a cyclic shift: the rotated view at a position is exactly the original
view at the shifted position. -/
@[simp] theorem rotate_point (view : OrganicRingConformationView source traversal) (k : ℕ)
    (position : Fin traversal.ringAtoms.length) :
    (view.rotate k).point position =
      view.point (cyclicShiftIndex traversal.ringAtoms.length k position) := rfl

/-- A cyclic shift acts on the viewed atom enumeration exactly as `List.rotate` acts on the
complete ordered atom list.  This is the precise reindexing statement for shifts; no bond is
dropped and no new atom is inserted. -/
@[simp] theorem atomOrder_rotate (view : OrganicRingConformationView source traversal) (k : ℕ) :
    (view.rotate k).atomOrder = view.atomOrder.rotate k := by
  apply List.ext_getElem
  · simp [atomOrder]
  · intro index firstBound secondBound
    simp only [atomOrder, List.length_ofFn, List.getElem_ofFn, List.getElem_rotate,
      rotate_atomAt]
    congr 1

/-- A shift of a canonical view rotates exactly the stored traversal atom list. -/
theorem atomOrder_ofGeometry_rotate (source : CertifiedAuthoritativeChemicalInput)
    (traversal : OrganicRingTraversal source) (geometry : RealSourceGeometry source) (k : ℕ) :
    ((ofGeometry source traversal geometry).rotate k).atomOrder =
      traversal.ringAtoms.rotate k := by
  rw [atomOrder_rotate, atomOrder_ofGeometry]

/-- Rotation by a shift whose permutation is the identity leaves the view unchanged. -/
theorem rotate_eq_self_of_perm_refl (view : OrganicRingConformationView source traversal)
    {k : ℕ} (identity : cyclicShiftPerm traversal.ringAtoms.length k = Equiv.refl _) :
    view.rotate k = view := by
  apply ext
  · rfl
  · show (cyclicShiftPerm traversal.ringAtoms.length k).trans view.order = view.order
    rw [identity, Equiv.refl_trans]

/-- Rotation by zero is the identity. -/
@[simp] theorem rotate_zero (view : OrganicRingConformationView source traversal) :
    view.rotate 0 = view :=
  rotate_eq_self_of_perm_refl view (cyclicShiftPerm_zero _)

/-- Successive rotations add their amounts. -/
theorem rotate_rotate (view : OrganicRingConformationView source traversal) (k l : ℕ) :
    (view.rotate k).rotate l = view.rotate (l + k) := by
  apply ext
  · rfl
  · show (cyclicShiftPerm traversal.ringAtoms.length l).trans
        ((cyclicShiftPerm traversal.ringAtoms.length k).trans view.order) =
      (cyclicShiftPerm traversal.ringAtoms.length (l + k)).trans view.order
    rw [← Equiv.trans_assoc, cyclicShiftPerm_trans]

/-- Inverse cyclic transport: rotating by `k` and then by the complementary shift returns exactly
the original complete view. -/
theorem rotate_inverse (view : OrganicRingConformationView source traversal) (k : ℕ) :
    (view.rotate k).rotate
        (traversal.ringAtoms.length - k % traversal.ringAtoms.length) = view := by
  rw [rotate_rotate]
  apply rotate_eq_self_of_perm_refl
  rw [← cyclicShiftPerm_trans (traversal.ringAtoms.length)
    (traversal.ringAtoms.length - k % traversal.ringAtoms.length) k]
  exact cyclicShiftPerm_neg_trans _ k

/-- The finite coordinate list of a rotated view is the rotated coordinate list. -/
theorem points_rotate (view : OrganicRingConformationView source traversal) (k : ℕ) :
    (view.rotate k).points = view.points.rotate k := by
  apply List.ext_getElem
  · simp [points]
  · intro index firstBound secondBound
    simp only [points, List.length_ofFn, List.getElem_ofFn, List.getElem_rotate,
      rotate_point]
    congr 1

/-- Rotation only reindexes the complete ordered cycle: the finite point set is unchanged. -/
theorem rotate_points_mem_iff (view : OrganicRingConformationView source traversal) (k : ℕ)
    (point : EuclideanSpace ℝ (Fin 3)) :
    point ∈ (view.rotate k).points ↔ point ∈ view.points := by
  rw [points_rotate]
  exact List.mem_rotate

/-! ### Reversal of the complete ordered cycle -/

/-- Reverse the complete ordered cycle.  Only the cycle reindexing changes; the full real geometry
and the source are untouched. -/
def reverse (view : OrganicRingConformationView source traversal) :
    OrganicRingConformationView source traversal where
  geometry := view.geometry
  order := (Fin.revPerm : Equiv.Perm (Fin traversal.ringAtoms.length)).trans view.order

/-- Reversal preserves the full geometry. -/
@[simp] theorem reverse_geometry (view : OrganicRingConformationView source traversal) :
    view.reverse.geometry = view.geometry := rfl

/-- The reindexing performed by a reversal. -/
@[simp] theorem reverse_order (view : OrganicRingConformationView source traversal) :
    view.reverse.order =
      (Fin.revPerm : Equiv.Perm (Fin traversal.ringAtoms.length)).trans view.order := rfl

/-- The atom viewed after reversal is the atom at the opposite cycle position. -/
@[simp] theorem reverse_atomAt (view : OrganicRingConformationView source traversal)
    (position : Fin traversal.ringAtoms.length) :
    view.reverse.atomAt position = view.atomAt (Fin.rev position) := rfl

/-- Reversal geometry correspondence: the reversed view at a position is exactly the original view
at the mirror position of the complete ordered cycle. -/
@[simp] theorem reverse_point (view : OrganicRingConformationView source traversal)
    (position : Fin traversal.ringAtoms.length) :
    view.reverse.point position = view.point (Fin.rev position) := rfl

/-- Reversal acts on the viewed atom enumeration exactly as `List.reverse` acts on the complete
ordered atom list.  This is the precise reindexing statement for reversal. -/
@[simp] theorem atomOrder_reverse (view : OrganicRingConformationView source traversal) :
    view.reverse.atomOrder = view.atomOrder.reverse := by
  apply List.ext_getElem
  · simp [atomOrder]
  · intro index firstBound secondBound
    have index_lt : index < traversal.ringAtoms.length := by
      simpa [atomOrder, List.length_ofFn] using firstBound
    simp only [atomOrder, List.length_ofFn, List.getElem_ofFn, List.getElem_reverse,
      reverse_atomAt]
    congr 1
    congr 1
    apply Fin.ext
    simp only [Fin.val_rev]
    omega

/-- Reversal of a canonical view reverses exactly the stored traversal atom list. -/
theorem atomOrder_ofGeometry_reverse (source : CertifiedAuthoritativeChemicalInput)
    (traversal : OrganicRingTraversal source) (geometry : RealSourceGeometry source) :
    (ofGeometry source traversal geometry).reverse.atomOrder =
      traversal.ringAtoms.reverse := by
  rw [atomOrder_reverse, atomOrder_ofGeometry]

/-- Reversing twice restores the complete view. -/
@[simp] theorem reverse_reverse (view : OrganicRingConformationView source traversal) :
    view.reverse.reverse = view := by
  apply ext
  · rfl
  · show (Fin.revPerm : Equiv.Perm (Fin traversal.ringAtoms.length)).trans
        ((Fin.revPerm : Equiv.Perm (Fin traversal.ringAtoms.length)).trans view.order) =
      view.order
    rw [← Equiv.trans_assoc]
    have involutive :
        (Fin.revPerm : Equiv.Perm (Fin traversal.ringAtoms.length)).trans Fin.revPerm =
          Equiv.refl _ := by
      apply Equiv.ext
      intro position
      show Fin.rev (Fin.rev position) = position
      exact Fin.rev_rev position
    rw [involutive, Equiv.refl_trans]

/-- The finite coordinate list of a reversed view is the reversed coordinate list. -/
theorem points_reverse (view : OrganicRingConformationView source traversal) :
    view.reverse.points = view.points.reverse := by
  apply List.ext_getElem
  · simp [points]
  · intro index firstBound secondBound
    simp only [points, List.getElem_ofFn, List.getElem_reverse, reverse_point]
    congr 1
    apply Fin.ext
    simp [Fin.val_rev]
    omega

/-- Reversal only reindexes the complete ordered cycle: the finite point set is unchanged. -/
theorem reverse_points_mem_iff (view : OrganicRingConformationView source traversal)
    (point : EuclideanSpace ℝ (Fin 3)) :
    point ∈ view.reverse.points ↔ point ∈ view.points := by
  rw [points_reverse, List.mem_reverse]

end OrganicRingConformationView

end OneCenter
end TetraStereo
