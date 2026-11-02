import TetraStereo.OneCenter.P93MolecularFullereneAxialHelixPreference
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Prod.Lex

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP93.Cyclic

noncomputable section

/-!
# Fu-3.1.2.1--3 priority within one reference-axis end kind

After Fu-3.1.1 and Fu-3.1.2 have fixed the eligible proper-axis order and selected ring, bond, or
atom ends, IUPAC applies a priority internal to that kind:

* for rings, larger size precedes smaller size and then atom ranks are compared;
* for bonds, the end containing the higher number of higher-ranking atoms is preferred;
* for atoms, the higher-ranking atom is preferred.

The atom rank is already derived from the three incident ring sizes.  Here the ranks belonging to
one end cell are converted to a descending multiset profile.  Consequently the result is invariant
under rotation of a stored face and exchange of the endpoints of an undirected bond.  A transparent
key `(ring size, descending rank profile)` realizes all three rules; size is zero for bonds and
atoms because candidates reaching this layer already have one common end kind.
-/

/-! ## Canonical rank profiles and transparent priority keys -/

/-- Incident-ring ranks of a finite atom family, canonically sorted from highest to lowest.  The
multiset quotient removes arbitrary input order before sorting. -/
def fullereneDescendingIncidentRingRankProfile
    (input : MolecularFullereneConfigurationInput)
    (atoms : List ℕ) : List (List ℕ) :=
  (((↑(atoms.map (fullereneAtomRingRank input)) : Multiset (List ℕ))).sort
    (fun left right => left ≤ right)).reverse

/-- Canonicalization neither invents nor drops an atom rank. -/
theorem fullereneDescendingIncidentRingRankProfile_perm
    (input : MolecularFullereneConfigurationInput)
    (atoms : List ℕ) :
    (fullereneDescendingIncidentRingRankProfile input atoms).Perm
      (atoms.map (fullereneAtomRingRank input)) := by
  unfold fullereneDescendingIncidentRingRankProfile
  apply List.Perm.trans (List.reverse_perm _)
  simpa only [Multiset.coe_sort] using
    (List.mergeSort_perm (atoms.map (fullereneAtomRingRank input))
      (fun left right => decide (left ≤ right)))

/-- Permuting the atoms supplied for an end cell cannot change its canonical rank profile. -/
theorem fullereneDescendingIncidentRingRankProfile_eq_of_perm
    (input : MolecularFullereneConfigurationInput)
    (left right : List ℕ)
    (permutation : left.Perm right) :
    fullereneDescendingIncidentRingRankProfile input left =
      fullereneDescendingIncidentRingRankProfile input right := by
  have multisetEq :
      (↑(left.map (fullereneAtomRingRank input)) : Multiset (List ℕ)) =
        ↑(right.map (fullereneAtomRingRank input)) :=
    Multiset.coe_eq_coe.mpr (permutation.map (fullereneAtomRingRank input))
  simp only [fullereneDescendingIncidentRingRankProfile, multisetEq]

/-- Fu-3.1.2.1--3 key.  The first coordinate implements larger-ring precedence; the second is the
descending multiset of official atom ranks. -/
abbrev FullereneAxisEndWithinKindPriorityKey := ℕ ×ₗ List (List ℕ)

def fullereneAxisEndWithinKindPriorityKey
    (input : MolecularFullereneConfigurationInput) :
    FullereneProperRotationAxisEnd → FullereneAxisEndWithinKindPriorityKey
  | .ring face =>
      toLex (face.length, fullereneDescendingIncidentRingRankProfile input face)
  | .bond edge =>
      toLex (0, fullereneDescendingIncidentRingRankProfile input [edge.1, edge.2])
  | .atom atom =>
      toLex (0, fullereneDescendingIncidentRingRankProfile input [atom])

@[simp] theorem fullereneAxisEndWithinKindPriorityKey_ring
    (input : MolecularFullereneConfigurationInput)
    (face : List ℕ) :
    fullereneAxisEndWithinKindPriorityKey input (.ring face) =
      toLex (face.length, fullereneDescendingIncidentRingRankProfile input face) := by
  rfl

@[simp] theorem fullereneAxisEndWithinKindPriorityKey_bond
    (input : MolecularFullereneConfigurationInput)
    (edge : ℕ × ℕ) :
    fullereneAxisEndWithinKindPriorityKey input (.bond edge) =
      toLex (0, fullereneDescendingIncidentRingRankProfile input [edge.1, edge.2]) := by
  rfl

@[simp] theorem fullereneAxisEndWithinKindPriorityKey_atom
    (input : MolecularFullereneConfigurationInput)
    (atom : ℕ) :
    fullereneAxisEndWithinKindPriorityKey input (.atom atom) =
      toLex (0, fullereneDescendingIncidentRingRankProfile input [atom]) := by
  rfl

/-- The arbitrary first vertex used to write a cyclic face cannot affect its Fu-3.1.2.1 key. -/
theorem fullereneAxisEndWithinKindPriorityKey_ring_eq_of_isRotated
    (input : MolecularFullereneConfigurationInput)
    (left right : List ℕ)
    (rotated : List.IsRotated left right) :
    fullereneAxisEndWithinKindPriorityKey input (.ring left) =
      fullereneAxisEndWithinKindPriorityKey input (.ring right) := by
  apply toLex_inj.mpr
  apply Prod.ext
  · exact rotated.perm.length_eq
  · exact fullereneDescendingIncidentRingRankProfile_eq_of_perm
      input left right rotated.perm

/-- Exchanging the two names used to write an undirected bond cannot affect its Fu-3.1.2.2 key. -/
theorem fullereneAxisEndWithinKindPriorityKey_bond_swap
    (input : MolecularFullereneConfigurationInput)
    (left right : ℕ) :
    fullereneAxisEndWithinKindPriorityKey input (.bond (left, right)) =
      fullereneAxisEndWithinKindPriorityKey input (.bond (right, left)) := by
  apply toLex_inj.mpr
  apply Prod.ext
  · rfl
  · exact fullereneDescendingIncidentRingRankProfile_eq_of_perm
      input [left, right] [right, left] (.swap right left [])

/-- Independent Fu-3.1.2.1--3 meaning of one same-kind axis end outranking another. -/
def FullereneAxisEndHigherWithinKind
    (input : MolecularFullereneConfigurationInput)
    (left right : FullereneProperRotationAxisEnd) : Prop :=
  fullereneAxisEndWithinKindPriorityKey input right <
    fullereneAxisEndWithinKindPriorityKey input left

/-- Executable comparison of two transparent same-kind priority keys. -/
def compareFullereneAxisEndsWithinKind
    (input : MolecularFullereneConfigurationInput)
    (left right : FullereneProperRotationAxisEnd) : Ordering :=
  @compare FullereneAxisEndWithinKindPriorityKey
    (inferInstanceAs (LinearOrder FullereneAxisEndWithinKindPriorityKey)).toOrd
    (fullereneAxisEndWithinKindPriorityKey input left)
    (fullereneAxisEndWithinKindPriorityKey input right)

/-- The comparator returns `gt` exactly for the independent within-kind priority relation. -/
@[simp] theorem compareFullereneAxisEndsWithinKind_eq_gt_iff
    (input : MolecularFullereneConfigurationInput)
    (left right : FullereneProperRotationAxisEnd) :
    compareFullereneAxisEndsWithinKind input left right = .gt ↔
      FullereneAxisEndHigherWithinKind input left right := by
  unfold compareFullereneAxisEndsWithinKind
  unfold FullereneAxisEndHigherWithinKind
  exact (compare_gt_iff_gt (α := FullereneAxisEndWithinKindPriorityKey))

/-! ## Maximal Fu-3.1.2.1--3 candidates -/

/-- Independent meaning of a candidate that has survived Fu-3.1.1 and Fu-3.1.2's end-kind
precedence, before comparison within that selected kind. -/
structure MolecularFullereneAxisOrderAndEndKindPreferredJudgment
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (candidate : MolecularFullereneAxialContiguousHelicalNumberingCandidate) : Prop where
  axial : MolecularFullereneAxialContiguousHelicalNumberingJudgment
    molecule input candidate
  highestEligibleAxisOrder :
    molecularFullereneHighestEligibleHelicalAxisOrder? molecule input =
      some candidate.axisOrder
  preferredAxisEndKind :
    molecularFullerenePreferredHelicalAxisEndKindRank? molecule input =
      some (fullereneAxisEndKindRank candidate.axisCandidate.axisEnd.kind)

noncomputable instance molecularFullereneAxisOrderAndEndKindPreferredJudgmentDecidable
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (candidate : MolecularFullereneAxialContiguousHelicalNumberingCandidate) :
    Decidable (MolecularFullereneAxisOrderAndEndKindPreferredJudgment
      molecule input candidate) :=
  Classical.propDecidable _

@[simp] theorem mem_molecularFullerenePreferredAxisEndKindHelicalNumberingCandidates_iff_judged
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (candidate : MolecularFullereneAxialContiguousHelicalNumberingCandidate) :
    candidate ∈ molecularFullerenePreferredAxisEndKindHelicalNumberingCandidates
        molecule input ↔
      MolecularFullereneAxisOrderAndEndKindPreferredJudgment
        molecule input candidate := by
  rw [mem_molecularFullerenePreferredAxisEndKindHelicalNumberingCandidates_iff]
  exact ⟨fun judged => ⟨judged.1, judged.2.1, judged.2.2⟩,
    fun judged => ⟨judged.axial, judged.highestEligibleAxisOrder,
      judged.preferredAxisEndKind⟩⟩

/-- Priority keys represented by candidates surviving the axis-order and end-kind filters. -/
noncomputable def molecularFullerenePreferredAxisEndWithinKindPriorityKeys
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput) :
    Finset FullereneAxisEndWithinKindPriorityKey :=
  ((molecularFullerenePreferredAxisEndKindHelicalNumberingCandidates molecule input).map
    fun candidate =>
      fullereneAxisEndWithinKindPriorityKey input candidate.axisCandidate.axisEnd).toFinset

/-- Exact priority-key membership. -/
@[simp] theorem mem_molecularFullerenePreferredAxisEndWithinKindPriorityKeys_iff
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (key : FullereneAxisEndWithinKindPriorityKey) :
    key ∈ molecularFullerenePreferredAxisEndWithinKindPriorityKeys molecule input ↔
      ∃ candidate,
        MolecularFullereneAxisOrderAndEndKindPreferredJudgment molecule input candidate ∧
          fullereneAxisEndWithinKindPriorityKey
            input candidate.axisCandidate.axisEnd = key := by
  classical
  constructor
  · intro present
    have rawPresent := present
    change key ∈
      ((molecularFullerenePreferredAxisEndKindHelicalNumberingCandidates molecule input).map
        fun candidate =>
          fullereneAxisEndWithinKindPriorityKey input
            candidate.axisCandidate.axisEnd).toFinset at rawPresent
    rcases List.mem_map.mp (List.mem_toFinset.mp rawPresent) with
      ⟨candidate, candidatePresent, keyEq⟩
    exact ⟨candidate,
      (mem_molecularFullerenePreferredAxisEndKindHelicalNumberingCandidates_iff_judged
        molecule input candidate).mp candidatePresent,
      keyEq⟩
  · rintro ⟨candidate, judged, keyEq⟩
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    exact ⟨candidate,
      (mem_molecularFullerenePreferredAxisEndKindHelicalNumberingCandidates_iff_judged
        molecule input candidate).mpr judged,
      keyEq⟩

/-- Maximum of a finite linearly ordered set, with refusal on the empty set. -/
private noncomputable def finiteMaximum?
    {α : Type} [LinearOrder α] (values : Finset α) : Option α :=
  if nonempty : values.Nonempty then
    some (values.max' nonempty)
  else
    none

private theorem finiteMaximum?_eq_some_iff
    {α : Type} [LinearOrder α]
    (values : Finset α)
    (value : α) :
    finiteMaximum? values = some value ↔
      value ∈ values ∧ ∀ other ∈ values, other ≤ value := by
  classical
  unfold finiteMaximum?
  by_cases nonempty : values.Nonempty
  · rw [dif_pos nonempty]
    constructor
    · intro computed
      have maximumEq : values.max' nonempty = value := Option.some.inj computed
      subst value
      exact ⟨values.max'_mem nonempty,
        fun other otherPresent => values.le_max' other otherPresent⟩
    · rintro ⟨present, greatest⟩
      apply congrArg some
      exact le_antisymm
        (greatest (values.max' nonempty) (values.max'_mem nonempty))
        (values.le_max' value present)
  · rw [dif_neg nonempty]
    constructor
    · intro impossible
      cases impossible
    · rintro ⟨present, _greatest⟩
      exact False.elim (nonempty ⟨value, present⟩)

private theorem finiteMaximum?_eq_none_iff
    {α : Type} [LinearOrder α]
    (values : Finset α) :
    finiteMaximum? values = none ↔ values = ∅ := by
  classical
  unfold finiteMaximum?
  by_cases nonempty : values.Nonempty
  · rw [dif_pos nonempty]
    constructor
    · intro impossible
      cases impossible
    · intro empty
      subst values
      simp at nonempty
  · rw [dif_neg nonempty]
    exact ⟨fun _ => Finset.not_nonempty_iff_eq_empty.mp nonempty, fun _ => rfl⟩

/-- Preferred Fu-3.1.2.1--3 key among candidates of the already selected end kind. -/
noncomputable def molecularFullerenePreferredAxisEndWithinKindPriorityKey?
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput) :
    Option FullereneAxisEndWithinKindPriorityKey :=
  finiteMaximum?
    (molecularFullerenePreferredAxisEndWithinKindPriorityKeys molecule input)

/-- Exact maximum-key semantics. -/
@[simp] theorem molecularFullerenePreferredAxisEndWithinKindPriorityKey?_eq_some_iff
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (key : FullereneAxisEndWithinKindPriorityKey) :
    molecularFullerenePreferredAxisEndWithinKindPriorityKey? molecule input = some key ↔
      key ∈ molecularFullerenePreferredAxisEndWithinKindPriorityKeys molecule input ∧
        ∀ otherKey ∈ molecularFullerenePreferredAxisEndWithinKindPriorityKeys molecule input,
          otherKey ≤ key := by
  exact finiteMaximum?_eq_some_iff
    (molecularFullerenePreferredAxisEndWithinKindPriorityKeys molecule input) key

/-- Refusal is exactly absence of a candidate surviving the preceding Fu-3.1 preference layers. -/
@[simp] theorem molecularFullerenePreferredAxisEndWithinKindPriorityKey?_eq_none_iff
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput) :
    molecularFullerenePreferredAxisEndWithinKindPriorityKey? molecule input = none ↔
      ¬∃ candidate,
        MolecularFullereneAxisOrderAndEndKindPreferredJudgment
          molecule input candidate := by
  rw [molecularFullerenePreferredAxisEndWithinKindPriorityKey?,
    finiteMaximum?_eq_none_iff]
  constructor
  · intro keysEmpty candidateExists
    rcases candidateExists with ⟨candidate, judged⟩
    have keyPresent :
        fullereneAxisEndWithinKindPriorityKey input candidate.axisCandidate.axisEnd ∈
          molecularFullerenePreferredAxisEndWithinKindPriorityKeys molecule input :=
      (mem_molecularFullerenePreferredAxisEndWithinKindPriorityKeys_iff molecule input _).mpr
        ⟨candidate, judged, rfl⟩
    rw [keysEmpty] at keyPresent
    simp at keyPresent
  · intro noCandidate
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro key keyPresent
    rcases (mem_molecularFullerenePreferredAxisEndWithinKindPriorityKeys_iff
      molecule input key).mp keyPresent with ⟨candidate, judged, _keyEq⟩
    exact noCandidate ⟨candidate, judged⟩

/-- Independent maximality judgment for Fu-3.1.2.1--3. -/
structure MolecularFullerenePreferredAxisEndWithinKindJudgment
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (candidate : MolecularFullereneAxialContiguousHelicalNumberingCandidate) : Prop where
  priorLayers : MolecularFullereneAxisOrderAndEndKindPreferredJudgment
    molecule input candidate
  noHigherEnd : ∀ other,
    MolecularFullereneAxisOrderAndEndKindPreferredJudgment molecule input other →
      ¬FullereneAxisEndHigherWithinKind input
        other.axisCandidate.axisEnd candidate.axisCandidate.axisEnd

noncomputable instance molecularFullerenePreferredAxisEndWithinKindJudgmentDecidable
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (candidate : MolecularFullereneAxialContiguousHelicalNumberingCandidate) :
    Decidable (MolecularFullerenePreferredAxisEndWithinKindJudgment
      molecule input candidate) :=
  Classical.propDecidable _

/-- Candidates whose end cell has the maximal official within-kind priority key. -/
noncomputable def molecularFullerenePreferredAxisEndHelicalNumberingCandidates
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput) :
    List MolecularFullereneAxialContiguousHelicalNumberingCandidate :=
  (molecularFullerenePreferredAxisEndKindHelicalNumberingCandidates molecule input).filter
    fun candidate => decide
      (molecularFullerenePreferredAxisEndWithinKindPriorityKey? molecule input =
        some (fullereneAxisEndWithinKindPriorityKey
          input candidate.axisCandidate.axisEnd))

/-- Exact Fu-3.1.2.1--3 selection: membership is precisely survival of prior layers plus absence
of any higher same-kind axis end. -/
@[simp] theorem mem_molecularFullerenePreferredAxisEndHelicalNumberingCandidates_iff
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (candidate : MolecularFullereneAxialContiguousHelicalNumberingCandidate) :
    candidate ∈ molecularFullerenePreferredAxisEndHelicalNumberingCandidates molecule input ↔
      MolecularFullerenePreferredAxisEndWithinKindJudgment
        molecule input candidate := by
  constructor
  · intro present
    have filtered := List.mem_filter.mp present
    have prior :=
      (mem_molecularFullerenePreferredAxisEndKindHelicalNumberingCandidates_iff_judged
        molecule input candidate).mp filtered.1
    have preferredEq := of_decide_eq_true filtered.2
    have maximum :=
      (molecularFullerenePreferredAxisEndWithinKindPriorityKey?_eq_some_iff
        molecule input
          (fullereneAxisEndWithinKindPriorityKey
            input candidate.axisCandidate.axisEnd)).mp preferredEq
    refine ⟨prior, ?_⟩
    intro other otherPrior higher
    have otherKeyPresent :=
      (mem_molecularFullerenePreferredAxisEndWithinKindPriorityKeys_iff molecule input _).mpr
        ⟨other, otherPrior, rfl⟩
    exact (not_lt_of_ge (maximum.2 _ otherKeyPresent)) higher
  · intro judged
    apply List.mem_filter.mpr
    refine ⟨(mem_molecularFullerenePreferredAxisEndKindHelicalNumberingCandidates_iff_judged
      molecule input candidate).mpr judged.priorLayers, ?_⟩
    simp only [decide_eq_true_eq]
    apply (molecularFullerenePreferredAxisEndWithinKindPriorityKey?_eq_some_iff
      molecule input
        (fullereneAxisEndWithinKindPriorityKey
          input candidate.axisCandidate.axisEnd)).mpr
    refine ⟨(mem_molecularFullerenePreferredAxisEndWithinKindPriorityKeys_iff
      molecule input _).mpr ⟨candidate, judged.priorLayers, rfl⟩, ?_⟩
    intro otherKey otherKeyPresent
    rcases (mem_molecularFullerenePreferredAxisEndWithinKindPriorityKeys_iff
      molecule input otherKey).mp otherKeyPresent with
      ⟨other, otherPrior, otherKeyEq⟩
    apply le_of_not_gt
    intro candidateKeyLtOther
    apply judged.noHigherEnd other otherPrior
    unfold FullereneAxisEndHigherWithinKind
    simpa [otherKeyEq] using candidateKeyLtOther

/-- Within-kind preference preserves nonemptiness exactly. -/
theorem molecularFullerenePreferredAxisEndHelicalNumberingCandidates_nonempty_iff
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput) :
    molecularFullerenePreferredAxisEndHelicalNumberingCandidates molecule input ≠ [] ↔
      molecularFullerenePreferredAxisEndKindHelicalNumberingCandidates molecule input ≠ [] := by
  constructor
  · intro nonempty
    obtain ⟨candidate, present⟩ := List.exists_mem_of_ne_nil _ nonempty
    have judged :=
      (mem_molecularFullerenePreferredAxisEndHelicalNumberingCandidates_iff
        molecule input candidate).mp present
    exact List.ne_nil_of_mem
      ((mem_molecularFullerenePreferredAxisEndKindHelicalNumberingCandidates_iff_judged
        molecule input candidate).mpr judged.priorLayers)
  · intro nonempty
    obtain ⟨candidate, candidatePresent⟩ := List.exists_mem_of_ne_nil _ nonempty
    have candidatePrior :=
      (mem_molecularFullerenePreferredAxisEndKindHelicalNumberingCandidates_iff_judged
        molecule input candidate).mp candidatePresent
    let keys := molecularFullerenePreferredAxisEndWithinKindPriorityKeys molecule input
    have keysNonempty : keys.Nonempty :=
      ⟨fullereneAxisEndWithinKindPriorityKey input candidate.axisCandidate.axisEnd,
        (mem_molecularFullerenePreferredAxisEndWithinKindPriorityKeys_iff molecule input _).mpr
          ⟨candidate, candidatePrior, rfl⟩⟩
    let bestKey := keys.max' keysNonempty
    have preferredEq :
        molecularFullerenePreferredAxisEndWithinKindPriorityKey? molecule input =
          some bestKey := by
      change finiteMaximum? keys = some bestKey
      simp [finiteMaximum?, keysNonempty, bestKey]
    have bestKeyPresent : bestKey ∈ keys := keys.max'_mem keysNonempty
    rcases (mem_molecularFullerenePreferredAxisEndWithinKindPriorityKeys_iff
      molecule input bestKey).mp bestKeyPresent with
      ⟨best, bestPrior, bestKeyEq⟩
    apply List.ne_nil_of_mem
    apply List.mem_filter.mpr
    refine ⟨(mem_molecularFullerenePreferredAxisEndKindHelicalNumberingCandidates_iff_judged
      molecule input best).mpr bestPrior, ?_⟩
    simp only [decide_eq_true_eq]
    rw [bestKeyEq]
    exact preferredEq

end

end BlueBookP93.Cyclic
end TetraStereo.OneCenter
