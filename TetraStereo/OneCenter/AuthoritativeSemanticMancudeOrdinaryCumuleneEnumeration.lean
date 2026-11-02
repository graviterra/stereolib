import TetraStereo.OneCenter.AuthoritativeSemanticMancudePerceptionBoundary

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Exhaustive source-canonical ordinary-cumulene enumeration

Rather than assuming a detector's search shape, this module first enumerates every duplicate-free
finite atom list over the molecule and then filters by the independent ordinary-double predicates.
It is intentionally finite and inefficient: its role is an authority/completeness boundary against
which optimized open-chain and cyclic perceivers can be proved.
-/

/-- Every source atom, once, in deterministic source-index order. -/
noncomputable def aromaticCanonicalAtomUniverse
    (source : AuthoritativeChemicalInput) :
    List source.AromaticCanonicalAtom :=
  Finset.univ.sort (· ≤ ·)

@[simp] theorem mem_aromaticCanonicalAtomUniverse
    (source : AuthoritativeChemicalInput)
    (atom : source.AromaticCanonicalAtom) :
    atom ∈ source.aromaticCanonicalAtomUniverse := by
  simp [aromaticCanonicalAtomUniverse]

theorem aromaticCanonicalAtomUniverse_nodup
    (source : AuthoritativeChemicalInput) :
    source.aromaticCanonicalAtomUniverse.Nodup := by
  exact Finset.sort_nodup Finset.univ (· ≤ ·)

/-- All ordered duplicate-free atom lists: take every sublist of the universe and every
permutation of that sublist. -/
noncomputable def aromaticCanonicalSimpleAtomLists
    (source : AuthoritativeChemicalInput) :
    List (List source.AromaticCanonicalAtom) :=
  source.aromaticCanonicalAtomUniverse.sublists.flatMap List.permutations

/-- The finite enumeration is extensionally exact: membership is precisely duplicate-freedom. -/
theorem mem_aromaticCanonicalSimpleAtomLists_iff
    (source : AuthoritativeChemicalInput)
    (path : List source.AromaticCanonicalAtom) :
    path ∈ source.aromaticCanonicalSimpleAtomLists ↔ path.Nodup := by
  unfold aromaticCanonicalSimpleAtomLists
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨candidate, candidateSublist, pathPermutation⟩
    have candidateNodup : candidate.Nodup :=
      (List.mem_sublists.mp candidateSublist).nodup
        source.aromaticCanonicalAtomUniverse_nodup
    exact (List.mem_permutations.mp pathPermutation).symm.nodup candidateNodup
  · intro pathNodup
    have pathSubset : path ⊆ source.aromaticCanonicalAtomUniverse := by
      intro atom _present
      exact source.mem_aromaticCanonicalAtomUniverse atom
    have subpermutation : path.Subperm source.aromaticCanonicalAtomUniverse :=
      pathNodup.subperm pathSubset
    rw [List.subperm_iff] at subpermutation
    rcases subpermutation with ⟨universeOrder, universePermutation, pathSublist⟩
    rcases List.exists_perm_sublist pathSublist universePermutation with
      ⟨candidate, candidatePermutation, candidateSublist⟩
    exact ⟨candidate, List.mem_sublists.mpr candidateSublist,
      List.mem_permutations.mpr candidatePermutation.symm⟩

/-- Every finite source-canonical ordinary-double path, without imposing maximality or a minimum
length. -/
noncomputable def aromaticCanonicalOrdinaryCumulenePaths
    (source : AuthoritativeChemicalInput) :
    List (List source.AromaticCanonicalAtom) := by
  classical
  exact source.aromaticCanonicalSimpleAtomLists.filter fun path =>
    decide (source.AromaticCanonicalOrdinaryCumulenePath path)

theorem mem_aromaticCanonicalOrdinaryCumulenePaths_iff
    (source : AuthoritativeChemicalInput)
    (path : List source.AromaticCanonicalAtom) :
    path ∈ source.aromaticCanonicalOrdinaryCumulenePaths ↔
      source.AromaticCanonicalOrdinaryCumulenePath path := by
  classical
  rw [aromaticCanonicalOrdinaryCumulenePaths, List.mem_filter,
    decide_eq_true_eq, source.mem_aromaticCanonicalSimpleAtomLists_iff]
  constructor
  · exact And.right
  · intro valid
    exact ⟨valid.1, valid⟩

/-- A nontrivial ordinary-cumulene path cannot be extended at either end while remaining a
simple ordinary-double path. -/
def AromaticCanonicalMaximalOrdinaryCumulenePath
    (source : AuthoritativeChemicalInput)
    (path : List source.AromaticCanonicalAtom) : Prop :=
  2 ≤ path.length ∧ source.AromaticCanonicalOrdinaryCumulenePath path ∧
    (∀ atom, ¬ source.AromaticCanonicalOrdinaryCumulenePath (atom :: path)) ∧
    (∀ atom, ¬ source.AromaticCanonicalOrdinaryCumulenePath (path ++ [atom]))

noncomputable def aromaticCanonicalMaximalOrdinaryCumulenePaths
    (source : AuthoritativeChemicalInput) :
    List (List source.AromaticCanonicalAtom) := by
  classical
  exact source.aromaticCanonicalSimpleAtomLists.filter fun path =>
    decide (source.AromaticCanonicalMaximalOrdinaryCumulenePath path)

/-- The maximal-path enumeration has no search gap. -/
theorem mem_aromaticCanonicalMaximalOrdinaryCumulenePaths_iff
    (source : AuthoritativeChemicalInput)
    (path : List source.AromaticCanonicalAtom) :
    path ∈ source.aromaticCanonicalMaximalOrdinaryCumulenePaths ↔
      source.AromaticCanonicalMaximalOrdinaryCumulenePath path := by
  classical
  rw [aromaticCanonicalMaximalOrdinaryCumulenePaths, List.mem_filter,
    decide_eq_true_eq, source.mem_aromaticCanonicalSimpleAtomLists_iff]
  constructor
  · exact And.right
  · intro maximal
    exact ⟨maximal.2.1.1, maximal⟩

/-- A simple ordinary-double cycle, represented by a path whose final atom closes back to its
first atom.  Length at least three excludes loops and doubled edges. -/
def AromaticCanonicalOrdinaryCumuleneCycle
    (source : AuthoritativeChemicalInput)
    (path : List source.AromaticCanonicalAtom) : Prop :=
  ∃ first middle last,
    path = first :: (middle ++ [last]) ∧
      3 ≤ path.length ∧
      source.AromaticCanonicalOrdinaryCumulenePath path ∧
      source.AromaticCanonicalOrdinaryDoubleBond last first

noncomputable def aromaticCanonicalOrdinaryCumuleneCycles
    (source : AuthoritativeChemicalInput) :
    List (List source.AromaticCanonicalAtom) := by
  classical
  exact source.aromaticCanonicalSimpleAtomLists.filter fun path =>
    decide (source.AromaticCanonicalOrdinaryCumuleneCycle path)

/-- The cyclic enumeration is extensionally complete for every finite ordinary-double cycle. -/
theorem mem_aromaticCanonicalOrdinaryCumuleneCycles_iff
    (source : AuthoritativeChemicalInput)
    (path : List source.AromaticCanonicalAtom) :
    path ∈ source.aromaticCanonicalOrdinaryCumuleneCycles ↔
      source.AromaticCanonicalOrdinaryCumuleneCycle path := by
  classical
  rw [aromaticCanonicalOrdinaryCumuleneCycles, List.mem_filter,
    decide_eq_true_eq, source.mem_aromaticCanonicalSimpleAtomLists_iff]
  constructor
  · exact And.right
  · intro cycle
    rcases cycle with ⟨first, middle, last, pathEq, length, valid, closing⟩
    exact ⟨valid.1, ⟨first, middle, last, pathEq, length, valid, closing⟩⟩

/-- No edge of an enumerated ordinary-double cycle—including its closing edge—is aromatic. -/
theorem AromaticCanonicalOrdinaryCumuleneCycle.nonaromatic
    {source : AuthoritativeChemicalInput}
    {path : List source.AromaticCanonicalAtom}
    (cycle : source.AromaticCanonicalOrdinaryCumuleneCycle path) :
    (path.IsChain fun left right =>
        semanticEdgeKey left.val right.val ∉ source.molecule.aromaticPairEdges) ∧
      ∃ first middle last,
        path = first :: (middle ++ [last]) ∧
          semanticEdgeKey last.val first.val ∉ source.molecule.aromaticPairEdges := by
  rcases cycle with ⟨first, middle, last, pathEq, _length, valid, closing⟩
  exact ⟨valid.isChain_not_aromaticPair,
    first, middle, last, pathEq, closing.not_aromaticPair⟩

/-- All exhaustive open and cyclic perceptions are functions only of the semantic source. -/
theorem aromaticCanonicalOrdinaryCumuleneEnumeration_kekule_invariant
    (source : AuthoritativeChemicalInput)
    (_leftSelection _rightSelection : List (Nat × Nat)) :
    source.aromaticCanonicalMaximalOrdinaryCumulenePaths =
        source.aromaticCanonicalMaximalOrdinaryCumulenePaths ∧
      source.aromaticCanonicalOrdinaryCumuleneCycles =
        source.aromaticCanonicalOrdinaryCumuleneCycles :=
  ⟨rfl, rfl⟩

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
