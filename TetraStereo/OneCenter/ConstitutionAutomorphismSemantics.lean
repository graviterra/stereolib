import TetraStereo.OneCenter.BranchSphereKey

set_option autoImplicit false

namespace TetraStereo.OneCenter

open RawMolecule

/-!
# Independent constitutional-automorphism semantics

This module states the mathematical object searched for by the production exact backtracker.  The
specification is independent of search order, fuel, candidate-count sorting, and early exit: a
finite list represents a bijection of the chosen vertex carrier, preserves constitutional atom
labels, and preserves every bond/nonbond class.
-/

namespace RawMolecule

/-- A list representation of a constitution-preserving bijection on `vertices`. -/
structure ConstitutionBijectionOn (mol : RawMolecule) (mancudeEdges : List (Nat × Nat))
    (vertices : List Nat) (mapping : List (Nat × Nat)) : Prop where
  source_permutation : (mapping.map Prod.fst).Perm vertices
  target_permutation : (mapping.map Prod.snd).Perm vertices
  atom_preserving : ∀ pair ∈ mapping, mol.sameConstitutionAtom pair.1 pair.2 = true
  bond_preserving : ∀ leftPair ∈ mapping, ∀ rightPair ∈ mapping,
    mol.constitutionBondClass mancudeEdges leftPair.1 rightPair.1 =
      mol.constitutionBondClass mancudeEdges leftPair.2 rightPair.2

/-- The independent meaning of a seeded constitutional automorphism. -/
def HasSeededConstitutionAutomorphism (mol : RawMolecule)
    (mancudeEdges : List (Nat × Nat)) (vertices : List Nat)
    (seed : List (Nat × Nat)) : Prop :=
  ∃ mapping, mol.ConstitutionBijectionOn mancudeEdges vertices mapping ∧
    ∀ pair ∈ seed, pair ∈ mapping

/-- Declarative admission of a target for one partial-isomorphism extension. -/
def ConstitutionCandidate (mol : RawMolecule) (mancudeEdges : List (Nat × Nat))
    (vertices : List Nat) (mapping : List (Nat × Nat)) (left right : Nat) : Prop :=
  right ∈ vertices ∧
    (∀ pair ∈ mapping, pair.2 ≠ right) ∧
    mol.sameConstitutionAtom left right = true ∧
    ∀ pair ∈ mapping,
      mol.constitutionBondClass mancudeEdges left pair.1 =
        mol.constitutionBondClass mancudeEdges right pair.2

/-- A partial injective constitutional map. Unlike a full bijection, its source carrier need not
yet cover `vertices`. -/
structure ConstitutionPartialEmbedding (mol : RawMolecule)
    (mancudeEdges : List (Nat × Nat)) (vertices : List Nat)
    (mapping : List (Nat × Nat)) : Prop where
  target_nodup : (mapping.map Prod.snd).Nodup
  target_mem : ∀ pair ∈ mapping, pair.2 ∈ vertices
  atom_preserving : ∀ pair ∈ mapping, mol.sameConstitutionAtom pair.1 pair.2 = true
  bond_preserving : ∀ leftPair ∈ mapping, ∀ rightPair ∈ mapping,
    mol.constitutionBondClass mancudeEdges leftPair.1 rightPair.1 =
      mol.constitutionBondClass mancudeEdges leftPair.2 rightPair.2

/-- The executable candidate list has exactly the declarative partial-isomorphism meaning. -/
theorem mem_exactConstitutionCandidates_iff
    (mol : RawMolecule) (mancudeEdges : List (Nat × Nat)) (vertices : List Nat)
    (mapping : List (Nat × Nat)) (left right : Nat) :
    right ∈ mol.exactConstitutionCandidates mancudeEdges vertices mapping left ↔
      mol.ConstitutionCandidate mancudeEdges vertices mapping left right := by
  simp [exactConstitutionCandidates, ConstitutionCandidate, constitutionMappingConsistent,
    List.all_eq_true, beq_iff_eq]
  aesop

/-- Undirected edge membership is symmetric in its queried endpoints. -/
theorem containsUndirectedEdge_comm (edges : List (Nat × Nat)) (left right : Nat) :
    containsUndirectedEdge edges left right = containsUndirectedEdge edges right left := by
  simp only [containsUndirectedEdge]
  congr 1
  funext edge
  simp [Bool.or_comm]

/-- Constitutional bond class is an undirected relation. -/
theorem constitutionBondClass_comm (mol : RawMolecule) (mancudeEdges : List (Nat × Nat))
    (left right : Nat) :
    mol.constitutionBondClass mancudeEdges left right =
      mol.constitutionBondClass mancudeEdges right left := by
  simp [constitutionBondClass, mol.bondOrder_symm left right,
    containsUndirectedEdge_comm mancudeEdges left right]

/-- A declaratively admitted candidate preserves the partial-embedding invariant when prepended. -/
theorem ConstitutionPartialEmbedding.cons
    {mol : RawMolecule} {mancudeEdges : List (Nat × Nat)} {vertices : List Nat}
    {mapping : List (Nat × Nat)} {left right : Nat}
    (embedding : mol.ConstitutionPartialEmbedding mancudeEdges vertices mapping)
    (candidate : mol.ConstitutionCandidate mancudeEdges vertices mapping left right) :
    mol.ConstitutionPartialEmbedding mancudeEdges vertices ((left, right) :: mapping) := by
  constructor
  · simp only [List.map_cons, List.nodup_cons]
    exact ⟨by
      intro rightMem
      rcases List.mem_map.mp rightMem with ⟨pair, pairMem, pairRight⟩
      exact candidate.2.1 pair pairMem pairRight,
      embedding.target_nodup⟩
  · intro pair pairMem
    rcases List.mem_cons.mp pairMem with pairEq | pairMem
    · subst pair
      exact candidate.1
    · exact embedding.target_mem pair pairMem
  · intro pair pairMem
    rcases List.mem_cons.mp pairMem with pairEq | pairMem
    · subst pair
      exact candidate.2.2.1
    · exact embedding.atom_preserving pair pairMem
  · intro leftPair leftMem rightPair rightMem
    rcases List.mem_cons.mp leftMem with leftEq | leftMem <;>
      rcases List.mem_cons.mp rightMem with rightEq | rightMem
    · subst leftPair
      subst rightPair
      simp [constitutionBondClass, mol.bondOrder_self]
    · subst leftPair
      exact candidate.2.2.2 rightPair rightMem
    · subst rightPair
      have forward := candidate.2.2.2 leftPair leftMem
      simpa [mol.constitutionBondClass_comm mancudeEdges] using forward
    · exact embedding.bond_preserving leftPair leftMem rightPair rightMem

/-- A partial embedding satisfies the production all-pairs seed check. -/
theorem ConstitutionPartialEmbedding.seed_valid
    {mol : RawMolecule} {mancudeEdges : List (Nat × Nat)} {vertices : List Nat}
    {mapping : List (Nat × Nat)}
    (embedding : mol.ConstitutionPartialEmbedding mancudeEdges vertices mapping) :
    mapping.all (fun pair =>
      mol.sameConstitutionAtom pair.1 pair.2 &&
        mol.constitutionMappingConsistent mancudeEdges (mapping.erase pair) pair.1 pair.2) =
      true := by
  rw [List.all_eq_true]
  intro pair pairMem
  rw [Bool.and_eq_true]
  refine ⟨embedding.atom_preserving pair pairMem, ?_⟩
  rw [constitutionMappingConsistent, List.all_eq_true]
  intro other otherMem
  exact beq_iff_eq.mpr
    (embedding.bond_preserving pair pairMem other (List.mem_of_mem_erase otherMem))

/-- Conversely, the production all-pairs seed check constructs a partial embedding once target
injectivity and carrier membership are known. -/
theorem constitutionPartialEmbedding_of_seed_valid
    {mol : RawMolecule} {mancudeEdges : List (Nat × Nat)} {vertices : List Nat}
    {mapping : List (Nat × Nat)}
    (target_nodup : (mapping.map Prod.snd).Nodup)
    (target_mem : ∀ pair ∈ mapping, pair.2 ∈ vertices)
    (seed_valid : mapping.all (fun pair =>
      mol.sameConstitutionAtom pair.1 pair.2 &&
        mol.constitutionMappingConsistent mancudeEdges (mapping.erase pair) pair.1 pair.2) =
      true) :
    mol.ConstitutionPartialEmbedding mancudeEdges vertices mapping := by
  have eachValid := List.all_eq_true.mp seed_valid
  constructor
  · exact target_nodup
  · exact target_mem
  · intro pair pairMem
    have validity := eachValid pair pairMem
    rw [Bool.and_eq_true] at validity
    exact validity.1
  · intro leftPair leftMem rightPair rightMem
    by_cases pairEq : rightPair = leftPair
    · subst rightPair
      simp [constitutionBondClass, mol.bondOrder_self]
    · have validity := eachValid leftPair leftMem
      rw [Bool.and_eq_true] at validity
      have consistency := validity.2
      rw [constitutionMappingConsistent, List.all_eq_true] at consistency
      exact beq_iff_eq.mp (consistency rightPair
        ((List.mem_erase_of_ne pairEq).2 rightMem))

end RawMolecule

/-- Descending insertion changes only order. -/
theorem insertDescBy_perm {alpha : Type*} (before : alpha → alpha → Bool)
    (value : alpha) (values : List alpha) :
    (insertDescBy before value values).Perm (value :: values) := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [insertDescBy]
      split
      · exact List.Perm.refl _
      · exact (List.Perm.cons head inductionHypothesis).trans
          (List.Perm.swap value head tail)

/-- The structural candidate-count sort changes only order. -/
theorem sortDescBy_perm {alpha : Type*} (before : alpha → alpha → Bool)
    (values : List alpha) :
    (sortDescBy before values).Perm values := by
  induction values with
  | nil => exact List.Perm.refl _
  | cons head tail inductionHypothesis =>
      exact (insertDescBy_perm before head (sortDescBy before tail)).trans
        (List.Perm.cons head inductionHypothesis)

namespace RawMolecule

/-- A finite, search-order-independent trace of extending a partial constitutional injection.
At each step any remaining source may be chosen; the relation does not mention the production
candidate-count heuristic. -/
inductive ConstitutionExtension (mol : RawMolecule) (mancudeEdges : List (Nat × Nat))
    (vertices : List Nat) :
    List Nat → List (Nat × Nat) → List (Nat × Nat) → Prop
  | nil (mapping : List (Nat × Nat)) : ConstitutionExtension mol mancudeEdges vertices [] mapping mapping
  | step {remaining : List Nat} {mapping finalMapping : List (Nat × Nat)}
      {left right : Nat}
      (left_mem : left ∈ remaining)
      (candidate : mol.ConstitutionCandidate mancudeEdges vertices mapping left right)
      (tail : ConstitutionExtension mol mancudeEdges vertices (remaining.erase left)
        ((left, right) :: mapping) finalMapping) :
      ConstitutionExtension mol mancudeEdges vertices remaining mapping finalMapping

/-- A complete extension contains exactly the original sources and all remaining sources. -/
theorem ConstitutionExtension.source_permutation
    {mol : RawMolecule} {mancudeEdges : List (Nat × Nat)} {vertices : List Nat}
    {remaining : List Nat} {mapping finalMapping : List (Nat × Nat)}
    (extension : mol.ConstitutionExtension mancudeEdges vertices remaining mapping finalMapping) :
    (finalMapping.map Prod.fst).Perm (remaining ++ mapping.map Prod.fst) := by
  induction extension with
  | nil => simp
  | @step remaining mapping finalMapping left right leftMem candidate tail inductionHypothesis =>
      have erasedReinserted : ((remaining.erase left) ++ [left]).Perm remaining :=
        (List.perm_append_comm :
          ((remaining.erase left) ++ [left]).Perm ([left] ++ remaining.erase left)).trans
          (List.perm_cons_erase leftMem).symm
      exact inductionHypothesis.trans (by
        simpa [List.append_assoc] using
          erasedReinserted.append_right (mapping.map Prod.fst))

/-- Every pair already present in the initial seed remains in the completed mapping. -/
theorem ConstitutionExtension.initial_mem
    {mol : RawMolecule} {mancudeEdges : List (Nat × Nat)} {vertices : List Nat}
    {remaining : List Nat} {mapping finalMapping : List (Nat × Nat)}
    (extension : mol.ConstitutionExtension mancudeEdges vertices remaining mapping finalMapping)
    {pair : Nat × Nat} (pairMem : pair ∈ mapping) :
    pair ∈ finalMapping := by
  induction extension with
  | nil => exact pairMem
  | step leftMem candidate tail inductionHypothesis =>
      exact inductionHypothesis (List.mem_cons_of_mem _ pairMem)

/-- Declarative extension preserves injectivity, carrier membership, atom labels, and all exposed
bond/nonbond classes. -/
theorem ConstitutionExtension.preserve_partial_embedding
    {mol : RawMolecule} {mancudeEdges : List (Nat × Nat)} {vertices : List Nat}
    {remaining : List Nat} {mapping finalMapping : List (Nat × Nat)}
    (extension : mol.ConstitutionExtension mancudeEdges vertices remaining mapping finalMapping)
    (embedding : mol.ConstitutionPartialEmbedding mancudeEdges vertices mapping) :
    mol.ConstitutionPartialEmbedding mancudeEdges vertices finalMapping := by
  induction extension with
  | nil => exact embedding
  | step leftMem candidate tail inductionHypothesis =>
      exact inductionHypothesis (embedding.cons candidate)

/-- The source selected by the production minimum-candidate ordering is genuinely remaining. -/
theorem selected_source_mem
    (mol : RawMolecule) (mancudeEdges : List (Nat × Nat)) (vertices remaining : List Nat)
    (mapping : List (Nat × Nat)) (count left : Nat)
    (selected :
      (sortDescBy (fun left right => left.1 ≤ right.1)
        (remaining.map fun source =>
          ((mol.exactConstitutionCandidates mancudeEdges vertices mapping source).length,
            source))).head? = some (count, left)) :
    left ∈ remaining := by
  let scored := remaining.map fun source =>
    ((mol.exactConstitutionCandidates mancudeEdges vertices mapping source).length, source)
  let ordered := sortDescBy (fun left right => left.1 ≤ right.1) scored
  have selected' : ordered.head? = some (count, left) := selected
  have head_mem : ∀ {values : List (Nat × Nat)} {value : Nat × Nat},
      values.head? = some value → value ∈ values := by
    intro values value equation
    cases values with
    | nil => simp at equation
    | cons head tail =>
        simp at equation
        simp [equation]
  have selectedOrdered : (count, left) ∈ ordered := by
    exact head_mem selected'
  have selectedScored : (count, left) ∈ scored :=
    (sortDescBy_perm (fun left right => left.1 ≤ right.1) scored).mem_iff.mp selectedOrdered
  rcases List.mem_map.mp selectedScored with ⟨source, sourceMem, pairEq⟩
  have sourceEq : source = left := by
    exact Prod.mk.inj pairEq |>.2
  simpa [sourceEq] using sourceMem

/-- Every successful result of the production backtracker carries a complete declarative extension
trace. This is the soundness half of the search/semantics bridge and is independent of the
minimum-candidate ordering. -/
theorem searchConstitutionAutomorphismExactAux_sound
    (mol : RawMolecule) (mancudeEdges : List (Nat × Nat)) (vertices : List Nat)
    {fuel : Nat} {remaining : List Nat} {mapping : List (Nat × Nat)}
    (length_eq : remaining.length = fuel)
    (success :
      mol.searchConstitutionAutomorphismExactAux mancudeEdges vertices fuel remaining mapping =
        true) :
    ∃ finalMapping,
      mol.ConstitutionExtension mancudeEdges vertices remaining mapping finalMapping := by
  induction fuel generalizing remaining mapping with
  | zero =>
      have remainingEq : remaining = [] := List.eq_nil_of_length_eq_zero length_eq
      subst remaining
      exact ⟨mapping, ConstitutionExtension.nil mapping⟩
  | succ fuel inductionHypothesis =>
      have remainingNonempty : remaining ≠ [] := by
        intro remainingEq
        subst remaining
        simp at length_eq
      let candidates := mol.exactConstitutionCandidates mancudeEdges vertices mapping
      let ordered := sortDescBy (fun left right => left.1 ≤ right.1)
        (remaining.map fun left => ((candidates left).length, left))
      have reduced :
          (match ordered.head? with
          | none => false
          | some (_, left) =>
              (candidates left).any (fun right =>
                mol.searchConstitutionAutomorphismExactAux mancudeEdges vertices fuel
                  (remaining.erase left) ((left, right) :: mapping))) = true := by
        simpa [searchConstitutionAutomorphismExactAux, remainingNonempty, candidates, ordered]
          using success
      cases selectedEq : ordered.head? with
      | none => simp [selectedEq] at reduced
      | some selected =>
          rcases selected with ⟨count, left⟩
          have anySuccess :
              (candidates left).any (fun right =>
                mol.searchConstitutionAutomorphismExactAux mancudeEdges vertices fuel
                  (remaining.erase left) ((left, right) :: mapping)) = true := by
            simpa [selectedEq] using reduced
          rw [List.any_eq_true] at anySuccess
          rcases anySuccess with ⟨right, rightMem, recursiveSuccess⟩
          have leftMem : left ∈ remaining := by
            apply mol.selected_source_mem mancudeEdges vertices remaining mapping count left
            exact selectedEq
          have erasedLength : (remaining.erase left).length = fuel := by
            have := List.length_erase_add_one leftMem
            omega
          rcases inductionHypothesis erasedLength recursiveSuccess with
            ⟨finalMapping, tail⟩
          exact ⟨finalMapping, ConstitutionExtension.step leftMem
            (mem_exactConstitutionCandidates_iff mol mancudeEdges vertices mapping left right |>.mp
              rightMem)
            tail⟩

/-- A successful public exact search is sound for the independent seeded-bijection semantics,
provided the caller's seed is already a partial embedding and its remaining-source decomposition
covers the vertex carrier. -/
theorem searchConstitutionAutomorphismExact_sound
    (mol : RawMolecule) (mancudeEdges : List (Nat × Nat)) (vertices remaining : List Nat)
    (mapping : List (Nat × Nat))
    (source_coverage : (remaining ++ mapping.map Prod.fst).Perm vertices)
    (seed_embedding : mol.ConstitutionPartialEmbedding mancudeEdges vertices mapping)
    (success :
      mol.searchConstitutionAutomorphismExact mancudeEdges vertices remaining mapping = true) :
    mol.HasSeededConstitutionAutomorphism mancudeEdges vertices mapping := by
  have auxiliarySuccess :
      mol.searchConstitutionAutomorphismExactAux mancudeEdges vertices remaining.length
        remaining mapping = true := by
    simpa [searchConstitutionAutomorphismExact] using success
  rcases mol.searchConstitutionAutomorphismExactAux_sound mancudeEdges vertices rfl
      auxiliarySuccess with ⟨finalMapping, extension⟩
  have sourcePermutation : (finalMapping.map Prod.fst).Perm vertices :=
    extension.source_permutation.trans source_coverage
  have finalEmbedding :
      mol.ConstitutionPartialEmbedding mancudeEdges vertices finalMapping :=
    extension.preserve_partial_embedding seed_embedding
  have targetSubset : finalMapping.map Prod.snd ⊆ vertices := by
    intro target targetMem
    rcases List.mem_map.mp targetMem with ⟨pair, pairMem, pairTarget⟩
    subst target
    exact finalEmbedding.target_mem pair pairMem
  have targetSubperm : List.Subperm (finalMapping.map Prod.snd) vertices :=
    finalEmbedding.target_nodup.subperm targetSubset
  have targetLength : (finalMapping.map Prod.snd).length = vertices.length := by
    simpa using sourcePermutation.length_eq
  have targetPermutation : (finalMapping.map Prod.snd).Perm vertices :=
    targetSubperm.perm_of_length_le (Nat.le_of_eq targetLength.symm)
  refine ⟨finalMapping, ?_, ?_⟩
  · exact {
      source_permutation := sourcePermutation
      target_permutation := targetPermutation
      atom_preserving := finalEmbedding.atom_preserving
      bond_preserving := finalEmbedding.bond_preserving }
  · intro pair pairMem
    exact extension.initial_mem pairMem

/-- A full independent bijection supplies an admissible target for every source not yet present in
the seed. This is the mathematical fact used by the completeness induction; it does not depend on
which remaining source the production heuristic selects. -/
theorem ConstitutionBijectionOn.candidate_for_remaining
    {mol : RawMolecule} {mancudeEdges : List (Nat × Nat)} {vertices remaining : List Nat}
    {seed fullMapping : List (Nat × Nat)}
    (vertices_nodup : vertices.Nodup)
    (bijection : mol.ConstitutionBijectionOn mancudeEdges vertices fullMapping)
    (extends_seed : ∀ pair ∈ seed, pair ∈ fullMapping)
    (source_coverage : (remaining ++ seed.map Prod.fst).Perm vertices)
    {left : Nat} (left_mem : left ∈ remaining) :
    ∃ right, (left, right) ∈ fullMapping ∧
      mol.ConstitutionCandidate mancudeEdges vertices seed left right := by
  have leftVertex : left ∈ vertices :=
    source_coverage.mem_iff.mp (List.mem_append_left _ left_mem)
  have leftSource : left ∈ fullMapping.map Prod.fst :=
    bijection.source_permutation.mem_iff.mpr leftVertex
  rcases List.mem_map.mp leftSource with ⟨chosenPair, chosenMem, chosenSource⟩
  rcases chosenPair with ⟨chosenLeft, right⟩
  simp only at chosenSource
  subst chosenLeft
  have sourceNodup : (remaining ++ seed.map Prod.fst).Nodup :=
    source_coverage.nodup_iff.mpr vertices_nodup
  have leftNotSeed : left ∉ seed.map Prod.fst :=
    List.disjoint_left.mp sourceNodup.disjoint left_mem
  have targetNodup : (fullMapping.map Prod.snd).Nodup :=
    bijection.target_permutation.nodup_iff.mpr vertices_nodup
  have rightVertex : right ∈ vertices :=
    bijection.target_permutation.mem_iff.mp
      (List.mem_map.mpr ⟨(left, right), chosenMem, rfl⟩)
  have targetFresh : ∀ pair ∈ seed, pair.2 ≠ right := by
    intro pair pairMem targetEq
    have pairFull : pair ∈ fullMapping := extends_seed pair pairMem
    have pairEq : pair = (left, right) :=
      List.inj_on_of_nodup_map targetNodup pairFull chosenMem targetEq
    apply leftNotSeed
    exact List.mem_map.mpr ⟨pair, pairMem, by simp [pairEq]⟩
  refine ⟨right, chosenMem, rightVertex, targetFresh,
    bijection.atom_preserving (left, right) chosenMem, ?_⟩
  intro pair pairMem
  exact bijection.bond_preserving (left, right) chosenMem pair (extends_seed pair pairMem)

/-- Completeness of the executable backtracker for the independent seeded-bijection semantics.
The only carrier hypotheses say that vertices are unique and that `remaining` plus the seed sources
is exactly the vertex carrier. -/
theorem searchConstitutionAutomorphismExactAux_complete
    (mol : RawMolecule) (mancudeEdges : List (Nat × Nat)) (vertices : List Nat)
    (vertices_nodup : vertices.Nodup)
    {fuel : Nat} {remaining : List Nat} {mapping : List (Nat × Nat)}
    (length_eq : remaining.length = fuel)
    (source_coverage : (remaining ++ mapping.map Prod.fst).Perm vertices)
    (automorphism : mol.HasSeededConstitutionAutomorphism mancudeEdges vertices mapping) :
    mol.searchConstitutionAutomorphismExactAux mancudeEdges vertices fuel remaining mapping =
      true := by
  induction fuel generalizing remaining mapping with
  | zero =>
      have remainingEq : remaining = [] := List.eq_nil_of_length_eq_zero length_eq
      subst remaining
      simp [searchConstitutionAutomorphismExactAux]
  | succ fuel inductionHypothesis =>
      have remainingNonempty : remaining ≠ [] := by
        intro remainingEq
        subst remaining
        simp at length_eq
      let candidates := mol.exactConstitutionCandidates mancudeEdges vertices mapping
      let scored := remaining.map fun left => ((candidates left).length, left)
      let ordered := sortDescBy (fun left right => left.1 ≤ right.1) scored
      have orderedPerm : ordered.Perm scored :=
        sortDescBy_perm (fun left right => left.1 ≤ right.1) scored
      cases orderedEq : ordered with
      | nil =>
          have scoredLengthZero : scored.length = 0 := by
            have := orderedPerm.length_eq
            simpa [orderedEq] using this.symm
          have scoredEq : scored = [] := List.eq_nil_of_length_eq_zero scoredLengthZero
          have remainingEq : remaining = [] := by
            simpa [scored] using scoredEq
          exact (remainingNonempty remainingEq).elim
      | cons selected rest =>
          rcases selected with ⟨count, left⟩
          have selectedHead : ordered.head? = some (count, left) := by
            simp [orderedEq]
          have leftMem : left ∈ remaining := by
            apply mol.selected_source_mem mancudeEdges vertices remaining mapping count left
            exact selectedHead
          rcases automorphism with ⟨fullMapping, bijection, extendsSeed⟩
          rcases bijection.candidate_for_remaining vertices_nodup extendsSeed source_coverage
              leftMem with ⟨right, chosenMem, candidate⟩
          have rightMem : right ∈ candidates left :=
            (mem_exactConstitutionCandidates_iff mol mancudeEdges vertices mapping left right).mpr
              candidate
          have erasedLength : (remaining.erase left).length = fuel := by
            have := List.length_erase_add_one leftMem
            omega
          have erasedReinserted : ((remaining.erase left) ++ [left]).Perm remaining :=
            (List.perm_append_comm :
              ((remaining.erase left) ++ [left]).Perm ([left] ++ remaining.erase left)).trans
              (List.perm_cons_erase leftMem).symm
          have updatedCoverage :
              ((remaining.erase left) ++ ((left, right) :: mapping).map Prod.fst).Perm vertices :=
            by
              have updatedToOld :
                  ((remaining.erase left) ++ ((left, right) :: mapping).map Prod.fst).Perm
                    (remaining ++ mapping.map Prod.fst) := by
                have := erasedReinserted.append_right (mapping.map Prod.fst)
                simpa [List.append_assoc] using this
              exact updatedToOld.trans source_coverage
          have updatedAutomorphism :
              mol.HasSeededConstitutionAutomorphism mancudeEdges vertices
                ((left, right) :: mapping) := by
            refine ⟨fullMapping, bijection, ?_⟩
            intro pair pairMem
            rcases List.mem_cons.mp pairMem with pairEq | pairMem
            · simpa [pairEq] using chosenMem
            · exact extendsSeed pair pairMem
          have recursiveSuccess := inductionHypothesis erasedLength
            updatedCoverage updatedAutomorphism
          have anySuccess :
              (candidates left).any (fun target =>
                mol.searchConstitutionAutomorphismExactAux mancudeEdges vertices fuel
                  (remaining.erase left) ((left, target) :: mapping)) = true :=
            List.any_eq_true.mpr ⟨right, rightMem, recursiveSuccess⟩
          simp [searchConstitutionAutomorphismExactAux,
            candidates, scored, ordered, orderedEq, anySuccess]

/-- Public completeness theorem for the exact seeded search. -/
theorem searchConstitutionAutomorphismExact_complete
    (mol : RawMolecule) (mancudeEdges : List (Nat × Nat)) (vertices remaining : List Nat)
    (mapping : List (Nat × Nat))
    (vertices_nodup : vertices.Nodup)
    (source_coverage : (remaining ++ mapping.map Prod.fst).Perm vertices)
    (automorphism : mol.HasSeededConstitutionAutomorphism mancudeEdges vertices mapping) :
    mol.searchConstitutionAutomorphismExact mancudeEdges vertices remaining mapping = true := by
  unfold searchConstitutionAutomorphismExact
  exact mol.searchConstitutionAutomorphismExactAux_complete mancudeEdges vertices vertices_nodup
    rfl source_coverage automorphism

/-- Exact kernel-checked characterization of the production Boolean by the independent finite
constitutional-bijection relation. -/
theorem searchConstitutionAutomorphismExact_eq_true_iff
    (mol : RawMolecule) (mancudeEdges : List (Nat × Nat)) (vertices remaining : List Nat)
    (mapping : List (Nat × Nat))
    (vertices_nodup : vertices.Nodup)
    (source_coverage : (remaining ++ mapping.map Prod.fst).Perm vertices)
    (seed_embedding : mol.ConstitutionPartialEmbedding mancudeEdges vertices mapping) :
    mol.searchConstitutionAutomorphismExact mancudeEdges vertices remaining mapping = true ↔
      mol.HasSeededConstitutionAutomorphism mancudeEdges vertices mapping := by
  constructor
  · exact mol.searchConstitutionAutomorphismExact_sound mancudeEdges vertices remaining mapping
      source_coverage seed_embedding
  · exact mol.searchConstitutionAutomorphismExact_complete mancudeEdges vertices remaining mapping
      vertices_nodup source_coverage

end RawMolecule

end TetraStereo.OneCenter
