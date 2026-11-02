import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3Through6InitialPartition
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceNaturality

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

open Rule6ReferenceFamilySemantics
open AuthoritativeCIPRule6P92Enumeration
open DeclarativeCIP.ProductionOccurrenceRules456

/-!
# Applicability-gated source-canonical Rule-6 scheduler

The Rule-6 topology gate is stated directly on the format-neutral source.  It is not an opaque
Boolean: an excluded topology is witnessed by an odd permutation of the four roots that extends
to an atom-label-preserving automorphism of the complete canonical CIP child relation.
-/

def aromaticCanonicalRule6RootAt
    {source : AuthoritativeChemicalInput} {carrierFuel : Nat}
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (rootsLength : roots.length = 4) (position : Fin 4) :
    source.AromaticCanonicalRerootCursor carrierFuel :=
  roots.get (Fin.cast rootsLength.symm position)

/-- An odd four-position symmetry that preserves the complete Rules-1a--5 partition and is
realized by one automorphism of the full source-canonical constitutional digraph. -/
def AromaticCanonicalRule6OddConstitutionAutomorphism
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalAtom)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (rootsLength : roots.length = 4)
    (partition : source.AromaticCanonicalRule3Through5InitialPartition carrierFuel) : Prop :=
  ∃ positionPermutation : Equiv.Perm (Fin 4),
    Equiv.Perm.sign positionPermutation = -1 ∧
    (∀ position,
      source.compareAromaticCanonicalRule3Through5RootPositions partition.frame
          position (positionPermutation position) = Ordering.eq) ∧
    ∃ atomPermutation : Equiv.Perm source.AromaticCanonicalAtom,
      source.AromaticCanonicalConstitutionAutomorphism atomPermutation ∧
      atomPermutation center = center ∧
      ∀ position,
        mapAromaticCanonicalOfficialCIPNode atomPermutation
            (source.aromaticCanonicalRule6RootAt roots rootsLength position).occurrence.1.node =
          (source.aromaticCanonicalRule6RootAt roots rootsLength
            (positionPermutation position)).occurrence.1.node

/-- Chemical applicability of Rule 6 is the absence of the descriptor-reversing constitutional
symmetry above. -/
def AromaticCanonicalRule6TopologyAdmissible
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalAtom)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (rootsLength : roots.length = 4)
    (partition : source.AromaticCanonicalRule3Through5InitialPartition carrierFuel) : Prop :=
  ¬ source.AromaticCanonicalRule6OddConstitutionAutomorphism
    center roots rootsLength partition

/-- Finite reflected check for one source constitution automorphism. -/
noncomputable def aromaticCanonicalConstitutionAutomorphism?
    (source : AuthoritativeChemicalInput)
    (permutation : Equiv.Perm source.AromaticCanonicalAtom) : Bool :=
  (List.finRange source.molecule.atomCount).all (fun atom =>
      source.molecule.atoms.get (permutation atom) ==
        source.molecule.atoms.get atom) &&
    (List.finRange source.molecule.atomCount).all (fun left =>
      (List.finRange source.molecule.atomCount).all (fun right =>
        source.molecule.aromaticCanonicalBondOrder left.val right.val ==
          source.molecule.aromaticCanonicalBondOrder
            (permutation left).val (permutation right).val)) &&
    (List.finRange source.molecule.atomCount).all (fun left =>
      (List.finRange source.molecule.atomCount).all (fun right =>
        source.molecule.aromaticPairEdges.contains
            (semanticEdgeKey left.val right.val) ==
          source.molecule.aromaticPairEdges.contains
            (semanticEdgeKey (permutation left).val (permutation right).val)))

theorem aromaticCanonicalConstitutionAutomorphism?_eq_true_iff
    (source : AuthoritativeChemicalInput)
    (permutation : Equiv.Perm source.AromaticCanonicalAtom) :
    source.aromaticCanonicalConstitutionAutomorphism? permutation = true ↔
      source.AromaticCanonicalConstitutionAutomorphism permutation := by
  simp [aromaticCanonicalConstitutionAutomorphism?,
    AromaticCanonicalConstitutionAutomorphism, List.all_eq_true, and_assoc]

/-- Exhaustive finite search over `S₄` and the full symmetric group of source atoms. -/
noncomputable def aromaticCanonicalRule6HasOddConstitutionAutomorphism?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalAtom)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (rootsLength : roots.length = 4)
    (partition : source.AromaticCanonicalRule3Through5InitialPartition carrierFuel) : Bool :=
  (Fintype.elems : Finset (Equiv.Perm (Fin 4))).toList.any fun positionPermutation =>
    (Equiv.Perm.sign positionPermutation == -1) &&
      (List.finRange 4).all (fun position =>
        source.compareAromaticCanonicalRule3Through5RootPositions partition.frame
            position (positionPermutation position) == Ordering.eq) &&
      (Fintype.elems : Finset
        (Equiv.Perm source.AromaticCanonicalAtom)).toList.any
        (fun atomPermutation =>
          source.aromaticCanonicalConstitutionAutomorphism? atomPermutation &&
            (atomPermutation center == center) &&
            (List.finRange 4).all (fun position =>
              mapAromaticCanonicalOfficialCIPNode atomPermutation
                  (source.aromaticCanonicalRule6RootAt
                    roots rootsLength position).occurrence.1.node ==
                (source.aromaticCanonicalRule6RootAt roots rootsLength
                  (positionPermutation position)).occurrence.1.node))

theorem aromaticCanonicalRule6HasOddConstitutionAutomorphism?_eq_true_iff
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalAtom)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (rootsLength : roots.length = 4)
    (partition : source.AromaticCanonicalRule3Through5InitialPartition carrierFuel) :
    source.aromaticCanonicalRule6HasOddConstitutionAutomorphism?
        center roots rootsLength partition = true ↔
      source.AromaticCanonicalRule6OddConstitutionAutomorphism
        center roots rootsLength partition := by
  simp [aromaticCanonicalRule6HasOddConstitutionAutomorphism?,
    AromaticCanonicalRule6OddConstitutionAutomorphism,
    source.aromaticCanonicalConstitutionAutomorphism?_eq_true_iff,
    List.all_eq_true, Fintype.complete, and_assoc]

theorem aromaticCanonicalRule6HasOddConstitutionAutomorphism?_eq_false_iff_admissible
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalAtom)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (rootsLength : roots.length = 4)
    (partition : source.AromaticCanonicalRule3Through5InitialPartition carrierFuel) :
    source.aromaticCanonicalRule6HasOddConstitutionAutomorphism?
        center roots rootsLength partition = false ↔
      source.AromaticCanonicalRule6TopologyAdmissible
        center roots rootsLength partition := by
  rw [Bool.eq_false_iff]
  exact not_congr
    (source.aromaticCanonicalRule6HasOddConstitutionAutomorphism?_eq_true_iff
      center roots rootsLength partition)

/-- Independent meaning of the exact P-92 1/2/3-group dispatch. -/
def AromaticCanonicalRule3Through6BranchDescriptorJudgment
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (partition : source.AromaticCanonicalRule3Through5InitialPartition carrierFuel)
    (parity : TetrahedralInputParity) (descriptor : RS) : Prop :=
  let backend := source.aromaticCanonicalRule3Through6RankingBackendForFrame
    partition.frame.rule3Frame target view fuel roots
  let sorted := partition.sortedPositions
  let adjacent := partition.adjacentOptions
  let groupCount := rule6GroupCount adjacent
  (groupCount = 1 ∧
      AuthoritativeFourWayDescriptorJudgment backend parity sorted descriptor) ∨
    (groupCount = 2 ∧
      CommonRule6Descriptor backend parity
        (rule6EquivalentReferencePositions sorted adjacent) descriptor) ∨
    (groupCount = 3 ∧
      CommonRule6Descriptor backend parity
        (rule6ThreeGroupReferencePositions sorted) (RS.swap descriptor))

/-- Exact source-level dispatch.  The proof argument prevents this entry point from being called
on a topology with an odd constitution-preserving automorphism. -/
noncomputable def aromaticCanonicalRule3Through6DescriptorForPartition?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalAtom)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (rootsLength : roots.length = 4)
    (partition : source.AromaticCanonicalRule3Through5InitialPartition carrierFuel)
    (_applicable : source.AromaticCanonicalRule6TopologyAdmissible
      center roots rootsLength partition)
    (parity : TetrahedralInputParity) : Option RS :=
  let backend := source.aromaticCanonicalRule3Through6RankingBackendForFrame
    partition.frame.rule3Frame target view fuel roots
  let sorted := partition.sortedPositions
  let adjacent := partition.adjacentOptions
  let groupCount := rule6GroupCount adjacent
  if groupCount = 1 then
    authoritativeOccurrenceRule6FourWayDescriptor? backend parity sorted
  else if groupCount = 2 then
    rule6FamilyDescriptorWithBackend? backend parity
      (rule6EquivalentReferencePositions sorted adjacent)
  else if groupCount = 3 then do
    let base ← rule6FamilyDescriptorWithBackend? backend parity
      (rule6ThreeGroupReferencePositions sorted)
    some (RS.swap base)
  else none

theorem aromaticCanonicalRule3Through6DescriptorForPartition?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalAtom)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (rootsLength : roots.length = 4)
    (partition : source.AromaticCanonicalRule3Through5InitialPartition carrierFuel)
    (applicable : source.AromaticCanonicalRule6TopologyAdmissible
      center roots rootsLength partition)
    (parity : TetrahedralInputParity) (descriptor : RS)
    (computed : source.aromaticCanonicalRule3Through6DescriptorForPartition?
      center target view fuel roots rootsLength partition applicable parity = some descriptor) :
    source.AromaticCanonicalRule6TopologyAdmissible
        center roots rootsLength partition ∧
      source.AromaticCanonicalRule3Through6BranchDescriptorJudgment
        target view fuel roots partition parity descriptor := by
  refine ⟨applicable, ?_⟩
  let backend := source.aromaticCanonicalRule3Through6RankingBackendForFrame
    partition.frame.rule3Frame target view fuel roots
  let sorted := partition.sortedPositions
  let adjacent := partition.adjacentOptions
  let groupCount := rule6GroupCount adjacent
  unfold aromaticCanonicalRule3Through6DescriptorForPartition? at computed
  by_cases groupOne : groupCount = 1
  · have emitted : authoritativeOccurrenceRule6FourWayDescriptor?
        backend parity sorted = some descriptor := by
      simpa [backend, sorted, adjacent, groupCount, groupOne] using computed
    exact Or.inl ⟨groupOne,
      (authoritativeOccurrenceRule6FourWayDescriptor?_eq_some_iff_judgment
        backend parity sorted descriptor).mp emitted⟩
  · by_cases groupTwo : groupCount = 2
    · have emitted : rule6FamilyDescriptorWithBackend? backend parity
          (rule6EquivalentReferencePositions sorted adjacent) = some descriptor := by
        simpa [backend, sorted, adjacent, groupCount, groupOne, groupTwo] using computed
      exact Or.inr (Or.inl ⟨groupTwo,
        (rule6FamilyDescriptorWithBackend?_eq_some_iff_commonDescriptor
          backend parity (rule6EquivalentReferencePositions sorted adjacent) descriptor).mp
            emitted⟩)
    · by_cases groupThree : groupCount = 3
      · cases familyComputed : rule6FamilyDescriptorWithBackend? backend parity
            (rule6ThreeGroupReferencePositions sorted) with
        | none =>
            simp [backend, sorted, adjacent, groupCount,
              groupThree, familyComputed] at computed
        | some base =>
            have descriptorEq : descriptor = RS.swap base := by
              simpa [backend, sorted, adjacent, groupCount, groupOne, groupTwo,
                groupThree, familyComputed] using computed.symm
            have commonBase :=
              (rule6FamilyDescriptorWithBackend?_eq_some_iff_commonDescriptor
                backend parity (rule6ThreeGroupReferencePositions sorted) base).mp
                familyComputed
            subst descriptor
            have commonBack : CommonRule6Descriptor backend parity
                (rule6ThreeGroupReferencePositions sorted)
                (RS.swap (RS.swap base)) := by
              simpa only [rs_swap_involutive] using commonBase
            exact Or.inr (Or.inr ⟨groupThree, commonBack⟩)
      · simp [adjacent, groupCount, groupOne, groupTwo,
          groupThree] at computed

/-- On an applicable topology, executable dispatch and the independent P-92 branch judgment are
equivalent in both directions. -/
theorem aromaticCanonicalRule3Through6DescriptorForPartition?_eq_some_iff_judgment
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalAtom)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (rootsLength : roots.length = 4)
    (partition : source.AromaticCanonicalRule3Through5InitialPartition carrierFuel)
    (applicable : source.AromaticCanonicalRule6TopologyAdmissible
      center roots rootsLength partition)
    (parity : TetrahedralInputParity) (descriptor : RS) :
    source.aromaticCanonicalRule3Through6DescriptorForPartition?
        center target view fuel roots rootsLength partition applicable parity =
        some descriptor ↔
      source.AromaticCanonicalRule3Through6BranchDescriptorJudgment
        target view fuel roots partition parity descriptor := by
  constructor
  · intro emitted
    exact (source.aromaticCanonicalRule3Through6DescriptorForPartition?_sound
      center target view fuel roots rootsLength partition applicable parity descriptor
      emitted).2
  · intro judged
    let backend := source.aromaticCanonicalRule3Through6RankingBackendForFrame
      partition.frame.rule3Frame target view fuel roots
    let sorted := partition.sortedPositions
    let adjacent := partition.adjacentOptions
    let groupCount := rule6GroupCount adjacent
    unfold AromaticCanonicalRule3Through6BranchDescriptorJudgment at judged
    dsimp only at judged
    change
      (groupCount = 1 ∧
          AuthoritativeFourWayDescriptorJudgment backend parity sorted descriptor) ∨
        (groupCount = 2 ∧
          CommonRule6Descriptor backend parity
            (rule6EquivalentReferencePositions sorted adjacent) descriptor) ∨
        (groupCount = 3 ∧
          CommonRule6Descriptor backend parity
            (rule6ThreeGroupReferencePositions sorted) (RS.swap descriptor)) at judged
    by_cases groupOne : groupCount = 1
    · rcases judged with one | two | three
      · have emitted :=
          (authoritativeOccurrenceRule6FourWayDescriptor?_eq_some_iff_judgment
            backend parity sorted descriptor).mpr one.2
        simpa [aromaticCanonicalRule3Through6DescriptorForPartition?,
          backend, sorted, adjacent, groupCount, groupOne] using emitted
      · omega
      · omega
    · by_cases groupTwo : groupCount = 2
      · rcases judged with one | two | three
        · omega
        · have emitted :=
            (rule6FamilyDescriptorWithBackend?_eq_some_iff_commonDescriptor
              backend parity (rule6EquivalentReferencePositions sorted adjacent)
                descriptor).mpr two.2
          simpa [aromaticCanonicalRule3Through6DescriptorForPartition?,
            backend, sorted, adjacent, groupCount, groupOne, groupTwo] using emitted
        · omega
      · by_cases groupThree : groupCount = 3
        · rcases judged with one | two | three
          · omega
          · omega
          · have family :=
              (rule6FamilyDescriptorWithBackend?_eq_some_iff_commonDescriptor
                backend parity (rule6ThreeGroupReferencePositions sorted)
                  (RS.swap descriptor)).mpr three.2
            simp [aromaticCanonicalRule3Through6DescriptorForPartition?,
              backend, sorted, adjacent, groupCount,
              groupThree, family, rs_swap_involutive]
        · rcases judged with one | two | three <;> omega

/-- Fully checked source-level Rule-6 dispatch.  The exhaustive finite topology decision supplies
the applicability proof consumed by the proof-gated core. -/
noncomputable def aromaticCanonicalRule3Through6DescriptorForPartitionChecked?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalAtom)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (rootsLength : roots.length = 4)
    (partition : source.AromaticCanonicalRule3Through5InitialPartition carrierFuel)
    (parity : TetrahedralInputParity) : Option RS :=
  if noOdd : source.aromaticCanonicalRule6HasOddConstitutionAutomorphism?
      center roots rootsLength partition = false then
    source.aromaticCanonicalRule3Through6DescriptorForPartition?
      center target view fuel roots rootsLength partition
        ((source.aromaticCanonicalRule6HasOddConstitutionAutomorphism?_eq_false_iff_admissible
          center roots rootsLength partition).mp noOdd) parity
  else none

/-- Checked emission is equivalent to both exact topology applicability and the independent P-92
branch judgment. -/
theorem aromaticCanonicalRule3Through6DescriptorForPartitionChecked?_eq_some_iff
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalAtom)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (rootsLength : roots.length = 4)
    (partition : source.AromaticCanonicalRule3Through5InitialPartition carrierFuel)
    (parity : TetrahedralInputParity) (descriptor : RS) :
    source.aromaticCanonicalRule3Through6DescriptorForPartitionChecked?
        center target view fuel roots rootsLength partition parity = some descriptor ↔
      source.AromaticCanonicalRule6TopologyAdmissible
          center roots rootsLength partition ∧
        source.AromaticCanonicalRule3Through6BranchDescriptorJudgment
          target view fuel roots partition parity descriptor := by
  unfold aromaticCanonicalRule3Through6DescriptorForPartitionChecked?
  by_cases noOdd : source.aromaticCanonicalRule6HasOddConstitutionAutomorphism?
      center roots rootsLength partition = false
  · let applicable : source.AromaticCanonicalRule6TopologyAdmissible
        center roots rootsLength partition :=
      (source.aromaticCanonicalRule6HasOddConstitutionAutomorphism?_eq_false_iff_admissible
        center roots rootsLength partition).mp noOdd
    rw [dif_pos noOdd,
      source.aromaticCanonicalRule3Through6DescriptorForPartition?_eq_some_iff_judgment
        center target view fuel roots rootsLength partition applicable parity descriptor]
    exact (and_iff_right applicable).symm
  · have notApplicable : ¬ source.AromaticCanonicalRule6TopologyAdmissible
        center roots rootsLength partition := by
      intro applicable
      exact noOdd
        ((source.aromaticCanonicalRule6HasOddConstitutionAutomorphism?_eq_false_iff_admissible
          center roots rootsLength partition).mpr applicable)
    simp [dif_neg noOdd, notApplicable]

/-- One-shot source endpoint from four rerooted ligands through Rules 1a--6. -/
noncomputable def aromaticCanonicalRule3Through6Descriptor?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalAtom)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (parity : TetrahedralInputParity) : Option RS := do
  if rootsLength : roots.length = 4 then
    let partition ← source.buildAromaticCanonicalRule3Through5InitialPartition?
      target view fuel roots
    source.aromaticCanonicalRule3Through6DescriptorForPartitionChecked?
      center target view fuel roots rootsLength partition parity
  else none

/-- Independent end-to-end meaning retained by every one-shot descriptor. -/
def AromaticCanonicalRule3Through6CompleteDescriptorJudgment
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalAtom)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (parity : TetrahedralInputParity) (descriptor : RS) : Prop :=
  ∃ (rootsLength : roots.length = 4)
      (partition : source.AromaticCanonicalRule3Through5InitialPartition carrierFuel),
    source.DeclarativeAromaticCanonicalRule3Through5InitialPartition
        target view fuel roots partition ∧
      source.AromaticCanonicalRule6TopologyAdmissible
        center roots rootsLength partition ∧
      source.AromaticCanonicalRule3Through6BranchDescriptorJudgment
        target view fuel roots partition parity descriptor

/-- Every descriptor emitted by the one-shot source Rules-1a--6 endpoint has a lawful complete
initial partition, passes the exact finite topology gate, and satisfies its independent P-92
reference-family judgment. -/
theorem aromaticCanonicalRule3Through6Descriptor?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalAtom)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (parity : TetrahedralInputParity) (descriptor : RS)
    (computed : source.aromaticCanonicalRule3Through6Descriptor?
      center target view fuel roots parity = some descriptor) :
    source.AromaticCanonicalRule3Through6CompleteDescriptorJudgment
      center target view fuel roots parity descriptor := by
  unfold aromaticCanonicalRule3Through6Descriptor? at computed
  by_cases rootsLength : roots.length = 4
  · cases partitionComputed :
        source.buildAromaticCanonicalRule3Through5InitialPartition?
          target view fuel roots with
    | none => simp [rootsLength, partitionComputed] at computed
    | some partition =>
        have checked :
            source.aromaticCanonicalRule3Through6DescriptorForPartitionChecked?
              center target view fuel roots rootsLength partition parity =
                some descriptor := by
          simpa [rootsLength, partitionComputed] using computed
        have exactMeaning :=
          (source.aromaticCanonicalRule3Through6DescriptorForPartitionChecked?_eq_some_iff
            center target view fuel roots rootsLength partition parity descriptor).mp checked
        exact ⟨rootsLength, partition,
          source.buildAromaticCanonicalRule3Through5InitialPartition?_sound
            target view fuel roots partition partitionComputed,
          exactMeaning.1, exactMeaning.2⟩
  · simp [rootsLength] at computed

/-- The one-shot function refuses every non-four-root representation. -/
theorem aromaticCanonicalRule3Through6Descriptor?_of_length_ne_four
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalAtom)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (parity : TetrahedralInputParity) (wrongLength : roots.length ≠ 4) :
    source.aromaticCanonicalRule3Through6Descriptor?
      center target view fuel roots parity = none := by
  simp [aromaticCanonicalRule3Through6Descriptor?, wrongLength]

/-- The topology gate has the exact logical boundary; no Boolean approximation is hidden in the
scheduler API. -/
theorem aromaticCanonicalRule6TopologyAdmissible_iff_no_odd_automorphism
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalAtom)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (rootsLength : roots.length = 4)
    (partition : source.AromaticCanonicalRule3Through5InitialPartition carrierFuel) :
    source.AromaticCanonicalRule6TopologyAdmissible
        center roots rootsLength partition ↔
      ¬ source.AromaticCanonicalRule6OddConstitutionAutomorphism
        center roots rootsLength partition := by
  rfl

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
