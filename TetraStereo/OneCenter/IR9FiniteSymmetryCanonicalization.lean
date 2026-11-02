import TetraStereo.OneCenter.IR9PolyhedralSemantics
import Mathlib.Data.List.Lex
import Mathlib.Data.Prod.Lex

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.FiniteSymmetry

/-!
# Finite-symmetry completion of the IR-9 configuration-index principle

IR-9.3.3.2 requires a configuration index to distinguish diastereomeric ligand placements, but
the Red Book gives geometry-specific digit recipes only for selected coordination polyhedra.  The
later IUPAC high-coordination technical report explicitly records that those recipes do not extend
unambiguously to every distorted high-coordinate structure.

This file closes the *finite idealized-geometry* mathematical gap without inventing a universal
distortion tolerance.  Once a geometry and its full finite vertex-symmetry group have been fixed,
we enumerate the priority-number word seen in every symmetry-related frame and choose the
lexicographically least word.  The central theorem proves both directions:

* symmetry-equivalent placements have the same canonical index; and
* equal canonical indices imply symmetry-equivalent placements.

Thus the index distinguishes exactly the relative configurations of every finite idealized
coordination geometry, including repeated and primed priority numbers.  Full symmetries make a
mirror pair share one relative index.  Repeating the construction with the proper-rotation subgroup
gives at most two absolute indices, and exactly two when the placement is chiral.

The separate choice of a nearest idealized geometry for a distorted experimental structure remains
typed evidence, as IR-9 itself provides no universal numerical boundary for that judgment.
-/

open scoped Classical

noncomputable section

variable {Position Label : Type*}
variable [Fintype Position] [DecidableEq Position]
variable [LinearOrder Label]

/-- The admitted vertex relabelings of one finite idealized coordination geometry. -/
abbrev SymmetryGroup (Position : Type*) := Subgroup (Equiv.Perm Position)

/-- Exhaustive full symmetry group derived from a complete pairwise geometry signature.  The
signature may be face/edge incidence, an angle class, or an exact squared-distance value.  Using a
rich signature prevents unrelated vertices from being identified while avoiding a hand-entered list
of permutations. -/
def signatureSymmetryGroup {Signature : Type*}
    (signature : Position → Position → Signature) : SymmetryGroup Position where
  carrier := { symmetry | ∀ left right,
    signature (symmetry left) (symmetry right) = signature left right }
  mul_mem' := by
    intro first second firstPreserves secondPreserves left right
    change signature (first (second left)) (first (second right)) = signature left right
    rw [firstPreserves, secondPreserves]
  one_mem' := by
    intro left right
    rfl
  inv_mem' := by
    intro symmetry preserves left right
    have transported := preserves (symmetry⁻¹ left) (symmetry⁻¹ right)
    simpa using transported.symm

/-- A fixed enumeration of every position.  Canonicalization over the complete symmetry group
removes dependence on the choice of symmetry-related frame. -/
def referenceOrder (Position : Type*) [Fintype Position] [DecidableEq Position] :
    List Position :=
  Finset.univ.toList

@[simp] theorem mem_referenceOrder (position : Position) :
    position ∈ referenceOrder Position := by
  simp [referenceOrder]

/-- Pull a ligand-priority placement through a vertex symmetry. -/
def relabel (symmetry : Equiv.Perm Position) (placement : Position → Label) :
    Position → Label :=
  fun position => placement (symmetry position)

/-- Relative equivalence under the admitted full symmetries of an idealized geometry. -/
def SymmetryEquivalent (group : SymmetryGroup Position)
    (left right : Position → Label) : Prop :=
  ∃ symmetry : group, right = relabel symmetry.1 left

/-- The complete priority word seen from one admitted symmetry-related frame. -/
def orbitCode (group : SymmetryGroup Position) (placement : Position → Label)
    (symmetry : group) : List Label :=
  (referenceOrder Position).map fun position => placement (symmetry.1 position)

/-- All priority words obtainable from admitted frames. -/
def orbitCodes (group : SymmetryGroup Position) (placement : Position → Label) :
    Finset (List Label) :=
  Finset.univ.image (orbitCode group placement)

theorem orbitCodes_nonempty (group : SymmetryGroup Position)
    (placement : Position → Label) : (orbitCodes group placement).Nonempty := by
  refine ⟨orbitCode group placement 1, ?_⟩
  simp [orbitCodes]

/-- The frame-independent relative configuration index. -/
def canonicalIndex (group : SymmetryGroup Position) (placement : Position → Label) :
    List Label :=
  (orbitCodes group placement).min' (orbitCodes_nonempty group placement)

private theorem eq_on_of_map_eq_map {α β : Type*} {entries : List α}
    {left right : α → β} (same : entries.map left = entries.map right)
    {entry : α} (member : entry ∈ entries) : left entry = right entry := by
  induction entries with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, List.cons.injEq] at same
      rcases same with ⟨sameHead, sameTail⟩
      rcases List.mem_cons.mp member with sameEntry | memberTail
      · subst entry
        exact sameHead
      · exact inductionHypothesis sameTail memberTail

/-- Relabeling by any admitted symmetry permutes the candidate set rather than changing it. -/
theorem orbitCodes_relabel (group : SymmetryGroup Position)
    (placement : Position → Label) (symmetry : group) :
    orbitCodes group (relabel symmetry.1 placement) = orbitCodes group placement := by
  ext code
  simp only [orbitCodes, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨candidate, rfl⟩
    refine ⟨symmetry * candidate, ?_⟩
    simp [orbitCode, relabel]
  · rintro ⟨candidate, rfl⟩
    refine ⟨symmetry⁻¹ * candidate, ?_⟩
    simp [orbitCode, relabel]

/-- The selected index is independent of the admitted geometry frame. -/
theorem canonicalIndex_relabel (group : SymmetryGroup Position)
    (placement : Position → Label) (symmetry : group) :
    canonicalIndex group (relabel symmetry.1 placement) = canonicalIndex group placement := by
  simp only [canonicalIndex, orbitCodes_relabel]

/-- A mirror operation in the full geometry group leaves the relative index unchanged. -/
theorem canonicalIndex_mirror (group : SymmetryGroup Position)
    (placement : Position → Label) (mirror : Equiv.Perm Position)
    (mirrorAdmitted : mirror ∈ group) :
    canonicalIndex group (relabel mirror placement) = canonicalIndex group placement :=
  canonicalIndex_relabel group placement ⟨mirror, mirrorAdmitted⟩

/-- **Finite idealized-geometry configuration-index theorem.**

Two complete priority placements have the same canonical index exactly when an admitted symmetry
of the coordination geometry transports one to the other.  The reverse implication is the key
completeness result: equality of chosen words supplies two symmetry frames with the same word;
because `referenceOrder` contains every position, their composite transports the full placement. -/
theorem canonicalIndex_eq_iff (group : SymmetryGroup Position)
    (left right : Position → Label) :
    canonicalIndex group left = canonicalIndex group right ↔
      SymmetryEquivalent group left right := by
  constructor
  · intro sameCanonical
    have leftMember : canonicalIndex group left ∈ orbitCodes group left := by
      exact Finset.min'_mem _ _
    have rightMember : canonicalIndex group right ∈ orbitCodes group right := by
      exact Finset.min'_mem _ _
    rcases Finset.mem_image.mp leftMember with ⟨leftSymmetry, _, leftCode⟩
    rcases Finset.mem_image.mp rightMember with ⟨rightSymmetry, _, rightCode⟩
    have codesEqual : orbitCode group left leftSymmetry =
        orbitCode group right rightSymmetry := by
      calc
        orbitCode group left leftSymmetry = canonicalIndex group left := leftCode
        _ = canonicalIndex group right := sameCanonical
        _ = orbitCode group right rightSymmetry := rightCode.symm
    have pointwise : ∀ position,
        left (leftSymmetry.1 position) = right (rightSymmetry.1 position) := by
      intro position
      exact eq_on_of_map_eq_map codesEqual (mem_referenceOrder position)
    refine ⟨leftSymmetry * rightSymmetry⁻¹, ?_⟩
    funext position
    simpa [relabel] using (pointwise (rightSymmetry.1.symm position)).symm
  · rintro ⟨symmetry, rfl⟩
    exact (canonicalIndex_relabel group left symmetry).symm

/-- Equivalently, nonsymmetry-equivalent placements always receive different indices. -/
theorem canonicalIndex_ne_iff (group : SymmetryGroup Position)
    (left right : Position → Label) :
    canonicalIndex group left ≠ canonicalIndex group right ↔
      ¬SymmetryEquivalent group left right := by
  rw [ne_eq, canonicalIndex_eq_iff]

/-- Proof object exposing the two defining obligations of a complete relative index. -/
structure CompleteRelativeIndex (group : SymmetryGroup Position) where
  index : (Position → Label) → List Label
  invariant : ∀ (placement : Position → Label) (symmetry : group),
    index (relabel symmetry.1 placement) = index placement
  exact : ∀ left right,
    index left = index right ↔ SymmetryEquivalent group left right

def completeRelativeIndex (group : SymmetryGroup Position) :
    CompleteRelativeIndex (Label := Label) group where
  index := canonicalIndex group
  invariant := canonicalIndex_relabel group
  exact := canonicalIndex_eq_iff group

/-- Every finite idealized geometry, presented by its complete symmetry group, therefore has a
complete relative configuration index. -/
theorem every_finite_idealized_geometry_has_complete_relative_index
    (group : SymmetryGroup Position) :
    ∃ index : (Position → Label) → List Label,
      (∀ placement (symmetry : group),
        index (relabel symmetry.1 placement) = index placement) ∧
      (∀ left right,
        index left = index right ↔ SymmetryEquivalent group left right) := by
  exact ⟨canonicalIndex group, canonicalIndex_relabel group, canonicalIndex_eq_iff group⟩

/-- In particular, a complete finite pairwise geometry signature automatically supplies the full
symmetry group needed by the theorem; callers do not have to assert that a permutation list is
complete. -/
theorem every_finite_signature_geometry_has_complete_relative_index
    {Signature : Type*} (signature : Position → Position → Signature) :
    ∃ index : (Position → Label) → List Label,
      (∀ placement (symmetry : signatureSymmetryGroup signature),
        index (relabel symmetry.1 placement) = index placement) ∧
      (∀ left right,
        index left = index right ↔
          SymmetryEquivalent (signatureSymmetryGroup signature) left right) :=
  every_finite_idealized_geometry_has_complete_relative_index
    (signatureSymmetryGroup signature)

/-! ## Proper symmetries and the two absolute classes -/

/-- If the full symmetry group is the union of its proper subgroup and one mirror coset, every
relative class contains at most the two proper-orbit indices represented by a placement and its
mirror. -/
theorem fullOrbit_has_at_most_two_properIndices
    (full proper : SymmetryGroup Position)
    (mirror : Equiv.Perm Position)
    (decomposition : ∀ symmetry : full,
      symmetry.1 ∈ proper ∨ ∃ rotation : proper, symmetry.1 = mirror * rotation.1)
    (placement other : Position → Label)
    (sameRelative : SymmetryEquivalent full placement other) :
    canonicalIndex proper other = canonicalIndex proper placement ∨
      canonicalIndex proper other = canonicalIndex proper (relabel mirror placement) := by
  rcases sameRelative with ⟨symmetry, rfl⟩
  rcases decomposition symmetry with properCase | mirrorCase
  · left
    exact canonicalIndex_relabel proper placement ⟨symmetry.1, properCase⟩
  · rcases mirrorCase with ⟨rotation, rotationEq⟩
    right
    rw [rotationEq]
    have relabelEq : relabel (mirror * rotation.1) placement =
        relabel rotation.1 (relabel mirror placement) := by
      funext position
      simp [relabel]
    rw [relabelEq]
    exact canonicalIndex_relabel proper (relabel mirror placement) rotation

/-- Exact formal content of “one relative configuration, two enantiomeric absolute classes”. -/
structure ExactTwoAbsoluteIndices
    (full proper : SymmetryGroup Position) (mirror : Equiv.Perm Position)
    (placement : Position → Label) : Prop where
  mirrorIsRelativeMate : SymmetryEquivalent full placement (relabel mirror placement)
  indicesDistinct : canonicalIndex proper placement ≠
    canonicalIndex proper (relabel mirror placement)
  exhaustive : ∀ other,
    SymmetryEquivalent full placement other →
      canonicalIndex proper other = canonicalIndex proper placement ∨
      canonicalIndex proper other = canonicalIndex proper (relabel mirror placement)

/-- When mirror and proper frames are the two cosets and the placement is not superimposable on its
mirror by a proper symmetry, the relative orbit has exactly two absolute indices. -/
theorem chiralRelativeOrbit_has_exactlyTwoAbsoluteIndices
    (full proper : SymmetryGroup Position)
    (mirror : Equiv.Perm Position) (mirrorFull : mirror ∈ full)
    (decomposition : ∀ symmetry : full,
      symmetry.1 ∈ proper ∨ ∃ rotation : proper, symmetry.1 = mirror * rotation.1)
    (placement : Position → Label)
    (chiral : ¬SymmetryEquivalent proper placement (relabel mirror placement)) :
    ExactTwoAbsoluteIndices full proper mirror placement where
  mirrorIsRelativeMate := ⟨⟨mirror, mirrorFull⟩, rfl⟩
  indicesDistinct := (canonicalIndex_ne_iff proper placement
    (relabel mirror placement)).2 chiral
  exhaustive := fun other sameRelative =>
    fullOrbit_has_at_most_two_properIndices full proper mirror decomposition
      placement other sameRelative

/-! ## IR-9 priority-number specialization -/

/-- Lexicographic, injective digit representation of an IR-9 priority number and its prime count. -/
abbrev CanonicalPriorityDigit := Nat ×ₗ Nat

def priorityDigit (priority : BlueBookP93.PriorityNumber) : CanonicalPriorityDigit :=
  toLex (priority.number, priority.primes)

theorem priorityDigit_injective : Function.Injective priorityDigit := by
  intro left right same
  have pairSame : (left.number, left.primes) = (right.number, right.primes) := by
    exact toLex.injective same
  cases left
  cases right
  simp_all

/-- Executable canonical IR-9 priority-number word for any finite idealized geometry. -/
def canonicalPriorityIndex (group : SymmetryGroup Position)
    (placement : Position → BlueBookP93.PriorityNumber) :
    List CanonicalPriorityDigit :=
  canonicalIndex group (fun position => priorityDigit (placement position))

/-- The priority-number word has no false collisions: equality is exactly geometric symmetry
equivalence, even when priority numbers repeat or carry primes. -/
theorem canonicalPriorityIndex_eq_iff (group : SymmetryGroup Position)
    (left right : Position → BlueBookP93.PriorityNumber) :
    canonicalPriorityIndex group left = canonicalPriorityIndex group right ↔
      SymmetryEquivalent group left right := by
  rw [canonicalPriorityIndex, canonicalPriorityIndex, canonicalIndex_eq_iff]
  constructor
  · rintro ⟨symmetry, encodedSame⟩
    refine ⟨symmetry, ?_⟩
    funext position
    exact priorityDigit_injective (congrFun encodedSame position)
  · rintro ⟨symmetry, placementSame⟩
    refine ⟨symmetry, ?_⟩
    funext position
    exact congrArg priorityDigit (congrFun placementSame position)

/-- This is the Red Book's required distinguishing property, now proved for an arbitrary finite
idealized coordination geometry rather than stipulated geometry by geometry. -/
theorem canonicalPriorityIndex_distinguishes_diastereomers
    (group : SymmetryGroup Position)
    (left right : Position → BlueBookP93.PriorityNumber)
    (diastereomeric : ¬SymmetryEquivalent group left right) :
    canonicalPriorityIndex group left ≠ canonicalPriorityIndex group right := by
  exact fun same =>
    diastereomeric ((canonicalPriorityIndex_eq_iff group left right).mp same)

end

end TetraStereo.OneCenter.RedBookIR9.FiniteSymmetry
