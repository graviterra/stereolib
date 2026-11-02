import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceNaturality
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRerootFrame

set_option autoImplicit false

/-!
# Canonical occurrence permutations from constitutional automorphisms

Unique official-child slots turn an atom involution into a proof-independent recursive address
map. Declarative reachability proves carrier closure, and the address involution packages the map
as a genuine occurrence equivalence preserving the scheduler dependency grade.
-/

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-- A data-carrying reachability witness.  Unlike the proof-irrelevant declarative proposition,
this `Type` remembers the exact child constructor at every depth and can therefore drive a
canonical executable address equivalence. -/
inductive AromaticCanonicalOccurrenceSubtreeWitness
    (molecularSource : AuthoritativeChemicalInput)
    (root : molecularSource.AromaticCanonicalAtom) :
    (path : List Nat) → (fuel : Nat) →
    (node : OfficialCIPNode molecularSource.AromaticCanonicalAtom) →
    (occurrence : molecularSource.AromaticCanonicalOccurrenceFrame) → Type
  | subtreeRoot (path fuel node) :
      AromaticCanonicalOccurrenceSubtreeWitness molecularSource root path fuel node
        { root := root, address := path, node := node, remaining := fuel }
  | subtreeDescendant {path fuel node child slot occurrence}
      (childAtSlot : (child, slot) ∈
        (molecularSource.molecule.aromaticCanonicalOfficialCIPChildrenAt
          molecularSource.molecule.atomCount node).zipIdx)
      (below : AromaticCanonicalOccurrenceSubtreeWitness molecularSource root
        (path ++ [slot]) fuel child occurrence) :
      AromaticCanonicalOccurrenceSubtreeWitness molecularSource root
        path (fuel + 1) node occurrence

def AromaticCanonicalOccurrenceSubtreeWitness.toDerived
    {molecularSource : AuthoritativeChemicalInput}
    {root : molecularSource.AromaticCanonicalAtom}
    {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode molecularSource.AromaticCanonicalAtom}
    {occurrence : molecularSource.AromaticCanonicalOccurrenceFrame}
    (witness : AromaticCanonicalOccurrenceSubtreeWitness molecularSource root
      path fuel node occurrence) :
    molecularSource.DeclarativeAromaticCanonicalOccurrenceSubtree
      root path fuel node occurrence := by
  induction witness with
  | subtreeRoot path fuel node =>
      exact AuthoritativeChemicalInput.DeclarativeAromaticCanonicalOccurrenceSubtree.subtreeRoot
        path fuel node
  | subtreeDescendant childAtSlot below inductionHypothesis =>
      exact AuthoritativeChemicalInput.DeclarativeAromaticCanonicalOccurrenceSubtree.subtreeDescendant
        childAtSlot inductionHypothesis

theorem nonempty_aromaticCanonicalOccurrenceSubtreeWitness_of_derived
    (molecularSource : AuthoritativeChemicalInput)
    {root : molecularSource.AromaticCanonicalAtom}
    {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode molecularSource.AromaticCanonicalAtom}
    {occurrence : molecularSource.AromaticCanonicalOccurrenceFrame}
    (derived : molecularSource.DeclarativeAromaticCanonicalOccurrenceSubtree
      root path fuel node occurrence) :
    Nonempty (AromaticCanonicalOccurrenceSubtreeWitness molecularSource root
      path fuel node occurrence) := by
  induction derived with
  | subtreeRoot path fuel node =>
      exact ⟨AromaticCanonicalOccurrenceSubtreeWitness.subtreeRoot path fuel node⟩
  | subtreeDescendant childAtSlot descendant inductionHypothesis =>
      obtain ⟨below⟩ := inductionHypothesis
      exact ⟨AromaticCanonicalOccurrenceSubtreeWitness.subtreeDescendant childAtSlot below⟩

noncomputable def mapAromaticCanonicalOccurrenceSubtreeWitness
    (molecularSource : AuthoritativeChemicalInput)
    (atomPermutation : Equiv.Perm molecularSource.AromaticCanonicalAtom)
    (constitution : molecularSource.AromaticCanonicalConstitutionAutomorphism atomPermutation)
    (noEdges : molecularSource.molecule.aromaticPairEdges = [])
    (childrenNodup : ∀ candidate,
      (molecularSource.molecule.aromaticCanonicalOfficialCIPChildrenAt
        molecularSource.molecule.atomCount candidate).Nodup)
    {root : molecularSource.AromaticCanonicalAtom}
    {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode molecularSource.AromaticCanonicalAtom}
    {occurrence : molecularSource.AromaticCanonicalOccurrenceFrame}
    (witness : AromaticCanonicalOccurrenceSubtreeWitness molecularSource root
      path fuel node occurrence) (mappedPath : List Nat) :
    Σ mappedAddress,
      AromaticCanonicalOccurrenceSubtreeWitness molecularSource (atomPermutation root)
        mappedPath fuel (mapAromaticCanonicalOfficialCIPNode atomPermutation node)
        { root := atomPermutation occurrence.root
          address := mappedAddress
          node := mapAromaticCanonicalOfficialCIPNode atomPermutation occurrence.node
          remaining := occurrence.remaining } := by
  induction witness generalizing mappedPath with
  | subtreeRoot path fuel node =>
      exact ⟨mappedPath,
        AromaticCanonicalOccurrenceSubtreeWitness.subtreeRoot mappedPath fuel
          (mapAromaticCanonicalOfficialCIPNode atomPermutation node)⟩
  | @subtreeDescendant path fuel node child slot occurrence childAtSlot below
      inductionHypothesis =>
      let mappedSlot :=
        canonicalMappedAromaticCanonicalOfficialCIPChildSlot molecularSource atomPermutation
          constitution noEdges childrenNodup node child slot childAtSlot
      let mappedChildAtSlot :=
        canonicalMappedAromaticCanonicalOfficialCIPChildSlot_mem molecularSource atomPermutation
          constitution noEdges childrenNodup node child slot childAtSlot
      let mappedBelow := inductionHypothesis (mappedPath ++ [mappedSlot])
      exact ⟨mappedBelow.1,
        AromaticCanonicalOccurrenceSubtreeWitness.subtreeDescendant
          mappedChildAtSlot mappedBelow.2⟩

theorem mapAromaticCanonicalOccurrenceSubtreeWitness_address_involutive
    (molecularSource : AuthoritativeChemicalInput)
    (atomPermutation : Equiv.Perm molecularSource.AromaticCanonicalAtom)
    (constitution : molecularSource.AromaticCanonicalConstitutionAutomorphism atomPermutation)
    (involutive : Function.Involutive atomPermutation)
    (noEdges : molecularSource.molecule.aromaticPairEdges = [])
    (childrenNodup : ∀ candidate,
      (molecularSource.molecule.aromaticCanonicalOfficialCIPChildrenAt
        molecularSource.molecule.atomCount candidate).Nodup)
    {root : molecularSource.AromaticCanonicalAtom}
    {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode molecularSource.AromaticCanonicalAtom}
    {occurrence : molecularSource.AromaticCanonicalOccurrenceFrame}
    (witness : AromaticCanonicalOccurrenceSubtreeWitness molecularSource root
      path fuel node occurrence) (mappedPath : List Nat) :
    let first := mapAromaticCanonicalOccurrenceSubtreeWitness molecularSource
      atomPermutation constitution noEdges childrenNodup witness mappedPath
    (mapAromaticCanonicalOccurrenceSubtreeWitness molecularSource
      atomPermutation constitution noEdges childrenNodup first.2 path).1 =
        occurrence.address := by
  induction witness generalizing mappedPath with
  | subtreeRoot => rfl
  | @subtreeDescendant path fuel node child slot occurrence childAtSlot below
      inductionHypothesis =>
      simp only [mapAromaticCanonicalOccurrenceSubtreeWitness]
      rw [canonicalMappedAromaticCanonicalOfficialCIPChildSlot_involutive
        molecularSource atomPermutation constitution involutive noEdges childrenNodup
          node child slot childAtSlot]
      exact inductionHypothesis _

theorem getElem?_eq_some_of_mem_zipIdx
    {V : Type*} {values : List V} {value : V} {slot : Nat}
    (present : (value, slot) ∈ values.zipIdx) :
    values[slot]? = some value := by
  have bound := List.snd_lt_of_mem_zipIdx present
  rw [List.getElem?_eq_getElem bound]
  exact congrArg some (List.fst_eq_of_mem_zipIdx present).symm

theorem idxOf_eq_slot_of_mem_zipIdx_of_nodup
    {V : Type*} [DecidableEq V] {values : List V} (nodup : values.Nodup)
    {value : V} {slot : Nat} (present : (value, slot) ∈ values.zipIdx) :
    values.idxOf value = slot := by
  have bound := List.snd_lt_of_mem_zipIdx present
  have valueAtSlot := List.fst_eq_of_mem_zipIdx present
  simp only [Nat.add_zero, Nat.sub_zero] at bound valueAtSlot
  rw [valueAtSlot, nodup.idxOf_getElem]

/-- Total address relabeling.  On a valid subtree address, each source slot is replaced by the
unique target slot of the atom-mapped child; invalid suffixes are harmlessly truncated. -/
def mapAromaticCanonicalOccurrenceAddressFromNode
    (molecularSource : AuthoritativeChemicalInput)
    (atomPermutation : Equiv.Perm molecularSource.AromaticCanonicalAtom) :
    OfficialCIPNode molecularSource.AromaticCanonicalAtom → List Nat → List Nat
  | _, [] => []
  | node, slot :: rest =>
      let children := molecularSource.molecule.aromaticCanonicalOfficialCIPChildrenAt
        molecularSource.molecule.atomCount node
      match children[slot]? with
      | none => []
      | some child =>
          let mappedChildren :=
            molecularSource.molecule.aromaticCanonicalOfficialCIPChildrenAt
              molecularSource.molecule.atomCount
              (mapAromaticCanonicalOfficialCIPNode atomPermutation node)
          mappedChildren.idxOf
              (mapAromaticCanonicalOfficialCIPNode atomPermutation child) ::
            mapAromaticCanonicalOccurrenceAddressFromNode molecularSource atomPermutation
              child rest

theorem mapAromaticCanonicalOccurrenceAddressFromNode_cons_of_childAtSlot
    (molecularSource : AuthoritativeChemicalInput)
    (atomPermutation : Equiv.Perm molecularSource.AromaticCanonicalAtom)
    (constitution : molecularSource.AromaticCanonicalConstitutionAutomorphism atomPermutation)
    (noEdges : molecularSource.molecule.aromaticPairEdges = [])
    (childrenNodup : ∀ candidate,
      (molecularSource.molecule.aromaticCanonicalOfficialCIPChildrenAt
        molecularSource.molecule.atomCount candidate).Nodup)
    (node child : OfficialCIPNode molecularSource.AromaticCanonicalAtom)
    (slot : Nat) (rest : List Nat)
    (childAtSlot : (child, slot) ∈
      (molecularSource.molecule.aromaticCanonicalOfficialCIPChildrenAt
        molecularSource.molecule.atomCount node).zipIdx) :
    mapAromaticCanonicalOccurrenceAddressFromNode molecularSource atomPermutation
        node (slot :: rest) =
      canonicalMappedAromaticCanonicalOfficialCIPChildSlot molecularSource atomPermutation
          constitution noEdges childrenNodup node child slot childAtSlot ::
        mapAromaticCanonicalOccurrenceAddressFromNode molecularSource atomPermutation
          child rest := by
  rw [mapAromaticCanonicalOccurrenceAddressFromNode,
    getElem?_eq_some_of_mem_zipIdx childAtSlot]
  dsimp only
  congr 1
  exact idxOf_eq_slot_of_mem_zipIdx_of_nodup
    (childrenNodup (mapAromaticCanonicalOfficialCIPNode atomPermutation node))
      (canonicalMappedAromaticCanonicalOfficialCIPChildSlot_mem molecularSource
        atomPermutation constitution noEdges childrenNodup node child slot childAtSlot)

theorem mapAromaticCanonicalOccurrenceAddressFromNode_involutive_of_witness
    (molecularSource : AuthoritativeChemicalInput)
    (atomPermutation : Equiv.Perm molecularSource.AromaticCanonicalAtom)
    (constitution : molecularSource.AromaticCanonicalConstitutionAutomorphism atomPermutation)
    (involutive : Function.Involutive atomPermutation)
    (noEdges : molecularSource.molecule.aromaticPairEdges = [])
    (childrenNodup : ∀ candidate,
      (molecularSource.molecule.aromaticCanonicalOfficialCIPChildrenAt
        molecularSource.molecule.atomCount candidate).Nodup)
    {root : molecularSource.AromaticCanonicalAtom}
    {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode molecularSource.AromaticCanonicalAtom}
    {occurrence : molecularSource.AromaticCanonicalOccurrenceFrame}
    (witness : AromaticCanonicalOccurrenceSubtreeWitness molecularSource root
      path fuel node occurrence) :
    mapAromaticCanonicalOccurrenceAddressFromNode molecularSource atomPermutation
        (mapAromaticCanonicalOfficialCIPNode atomPermutation node)
        (mapAromaticCanonicalOccurrenceAddressFromNode molecularSource atomPermutation
          node (occurrence.address.drop path.length)) =
      occurrence.address.drop path.length := by
  induction witness with
  | subtreeRoot => simp [mapAromaticCanonicalOccurrenceAddressFromNode]
  | @subtreeDescendant path fuel node child slot occurrence childAtSlot below
      inductionHypothesis =>
      obtain ⟨suffix, addressEq⟩ :=
        molecularSource.declarativeAromaticCanonicalOccurrenceSubtree_addressPrefix
          below.toDerived
      rw [← addressEq]
      rw [List.append_assoc]
      simp only [List.drop_append_of_le_length (Nat.le_refl _), List.drop_length,
        List.nil_append]
      rw [List.singleton_append]
      rw [mapAromaticCanonicalOccurrenceAddressFromNode_cons_of_childAtSlot
        molecularSource atomPermutation constitution noEdges childrenNodup
          node child slot suffix childAtSlot]
      rw [mapAromaticCanonicalOccurrenceAddressFromNode_cons_of_childAtSlot
        molecularSource atomPermutation constitution noEdges childrenNodup
          (mapAromaticCanonicalOfficialCIPNode atomPermutation node)
          (mapAromaticCanonicalOfficialCIPNode atomPermutation child)
          (canonicalMappedAromaticCanonicalOfficialCIPChildSlot molecularSource
            atomPermutation constitution noEdges childrenNodup node child slot childAtSlot)
          (mapAromaticCanonicalOccurrenceAddressFromNode molecularSource atomPermutation
            child suffix)
          (canonicalMappedAromaticCanonicalOfficialCIPChildSlot_mem molecularSource
            atomPermutation constitution noEdges childrenNodup node child slot childAtSlot)]
      rw [canonicalMappedAromaticCanonicalOfficialCIPChildSlot_involutive
        molecularSource atomPermutation constitution involutive noEdges childrenNodup
          node child slot childAtSlot]
      congr 1
      rw [← addressEq] at inductionHypothesis
      simpa using inductionHypothesis

theorem mapped_declarativeAromaticCanonicalOccurrenceSubtree_of_witness
    (molecularSource : AuthoritativeChemicalInput)
    (atomPermutation : Equiv.Perm molecularSource.AromaticCanonicalAtom)
    (constitution : molecularSource.AromaticCanonicalConstitutionAutomorphism atomPermutation)
    (noEdges : molecularSource.molecule.aromaticPairEdges = [])
    (childrenNodup : ∀ candidate,
      (molecularSource.molecule.aromaticCanonicalOfficialCIPChildrenAt
        molecularSource.molecule.atomCount candidate).Nodup)
    {root : molecularSource.AromaticCanonicalAtom}
    {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode molecularSource.AromaticCanonicalAtom}
    {occurrence : molecularSource.AromaticCanonicalOccurrenceFrame}
    (witness : AromaticCanonicalOccurrenceSubtreeWitness molecularSource root
      path fuel node occurrence) (mappedPath : List Nat) :
    molecularSource.DeclarativeAromaticCanonicalOccurrenceSubtree
      (atomPermutation root) mappedPath fuel
      (mapAromaticCanonicalOfficialCIPNode atomPermutation node)
      { root := atomPermutation occurrence.root
        address := mappedPath ++
          mapAromaticCanonicalOccurrenceAddressFromNode molecularSource atomPermutation
            node (occurrence.address.drop path.length)
        node := mapAromaticCanonicalOfficialCIPNode atomPermutation occurrence.node
        remaining := occurrence.remaining } := by
  induction witness generalizing mappedPath with
  | subtreeRoot path fuel node =>
      simpa [mapAromaticCanonicalOccurrenceAddressFromNode] using
        (AuthoritativeChemicalInput.DeclarativeAromaticCanonicalOccurrenceSubtree.subtreeRoot
          (source := molecularSource) (root := atomPermutation root) mappedPath fuel
          (mapAromaticCanonicalOfficialCIPNode atomPermutation node))
  | @subtreeDescendant path fuel node child slot occurrence childAtSlot below
      inductionHypothesis =>
      let mappedSlot :=
        canonicalMappedAromaticCanonicalOfficialCIPChildSlot molecularSource atomPermutation
          constitution noEdges childrenNodup node child slot childAtSlot
      have mappedChildAtSlot :=
        canonicalMappedAromaticCanonicalOfficialCIPChildSlot_mem molecularSource atomPermutation
          constitution noEdges childrenNodup node child slot childAtSlot
      have belowMapped := inductionHypothesis (mappedPath ++ [mappedSlot])
      have descendantMapped :=
        AuthoritativeChemicalInput.DeclarativeAromaticCanonicalOccurrenceSubtree.subtreeDescendant
          mappedChildAtSlot belowMapped
      obtain ⟨suffix, addressEq⟩ :=
        molecularSource.declarativeAromaticCanonicalOccurrenceSubtree_addressPrefix
          below.toDerived
      rw [← addressEq]
      rw [List.append_assoc]
      simp only [List.drop_append_of_le_length (Nat.le_refl _), List.drop_length,
        List.nil_append, List.singleton_append]
      rw [mapAromaticCanonicalOccurrenceAddressFromNode_cons_of_childAtSlot
        molecularSource atomPermutation constitution noEdges childrenNodup
          node child slot suffix childAtSlot]
      rw [← addressEq] at descendantMapped
      simpa [mappedSlot, List.append_assoc] using descendantMapped

noncomputable def aromaticCanonicalOccurrenceSubtreeWitnessOfCarrier
    (molecularSource : AuthoritativeChemicalInput) (fuel : Nat)
    (occurrence : molecularSource.AromaticCanonicalOccurrence fuel) :
    AromaticCanonicalOccurrenceSubtreeWitness molecularSource occurrence.1.root
      [] (fuel + 1) (OfficialCIPNode.root occurrence.1.root) occurrence.1 :=
  Classical.choice <| nonempty_aromaticCanonicalOccurrenceSubtreeWitness_of_derived
    molecularSource <| (molecularSource.mem_aromaticCanonicalOccurrences_iff
      fuel occurrence.1).mp occurrence.2

noncomputable def mapAromaticCanonicalOccurrence
    (molecularSource : AuthoritativeChemicalInput) (fuel : Nat)
    (atomPermutation : Equiv.Perm molecularSource.AromaticCanonicalAtom)
    (constitution : molecularSource.AromaticCanonicalConstitutionAutomorphism atomPermutation)
    (noEdges : molecularSource.molecule.aromaticPairEdges = [])
    (childrenNodup : ∀ candidate,
      (molecularSource.molecule.aromaticCanonicalOfficialCIPChildrenAt
        molecularSource.molecule.atomCount candidate).Nodup)
    (occurrence : molecularSource.AromaticCanonicalOccurrence fuel) :
    molecularSource.AromaticCanonicalOccurrence fuel := by
  let mappedFrame : molecularSource.AromaticCanonicalOccurrenceFrame :=
    { root := atomPermutation occurrence.1.root
      address := mapAromaticCanonicalOccurrenceAddressFromNode molecularSource atomPermutation
        (OfficialCIPNode.root occurrence.1.root) occurrence.1.address
      node := mapAromaticCanonicalOfficialCIPNode atomPermutation occurrence.1.node
      remaining := occurrence.1.remaining }
  refine ⟨mappedFrame, ?_⟩
  rw [molecularSource.mem_aromaticCanonicalOccurrences_iff]
  change molecularSource.DeclarativeAromaticCanonicalOccurrenceSubtree
    mappedFrame.root [] (fuel + 1) (OfficialCIPNode.root mappedFrame.root) mappedFrame
  have mappedDerived := mapped_declarativeAromaticCanonicalOccurrenceSubtree_of_witness
    molecularSource atomPermutation constitution noEdges childrenNodup
      (aromaticCanonicalOccurrenceSubtreeWitnessOfCarrier molecularSource fuel occurrence) []
  simpa [mappedFrame, mapAromaticCanonicalOfficialCIPNode, OfficialCIPNode.root] using
    mappedDerived

theorem mapAromaticCanonicalOccurrence_involutive
    (molecularSource : AuthoritativeChemicalInput) (fuel : Nat)
    (atomPermutation : Equiv.Perm molecularSource.AromaticCanonicalAtom)
    (constitution : molecularSource.AromaticCanonicalConstitutionAutomorphism atomPermutation)
    (involutive : Function.Involutive atomPermutation)
    (noEdges : molecularSource.molecule.aromaticPairEdges = [])
    (childrenNodup : ∀ candidate,
      (molecularSource.molecule.aromaticCanonicalOfficialCIPChildrenAt
        molecularSource.molecule.atomCount candidate).Nodup) :
    Function.Involutive (mapAromaticCanonicalOccurrence molecularSource fuel atomPermutation
      constitution noEdges childrenNodup) := by
  intro occurrence
  apply Subtype.ext
  simp only [mapAromaticCanonicalOccurrence]
  congr 1
  · exact involutive occurrence.1.root
  · have addressInvolutive :=
      mapAromaticCanonicalOccurrenceAddressFromNode_involutive_of_witness
        molecularSource atomPermutation constitution involutive noEdges childrenNodup
          (aromaticCanonicalOccurrenceSubtreeWitnessOfCarrier molecularSource fuel occurrence)
    simpa [mapAromaticCanonicalOccurrence, mapAromaticCanonicalOfficialCIPNode,
      OfficialCIPNode.root] using addressInvolutive
  · exact mapAromaticCanonicalOfficialCIPNode_involutive
      atomPermutation involutive occurrence.1.node

noncomputable def aromaticCanonicalOccurrencePermutationOfInvolution
    (molecularSource : AuthoritativeChemicalInput) (fuel : Nat)
    (atomPermutation : Equiv.Perm molecularSource.AromaticCanonicalAtom)
    (constitution : molecularSource.AromaticCanonicalConstitutionAutomorphism atomPermutation)
    (involutive : Function.Involutive atomPermutation)
    (noEdges : molecularSource.molecule.aromaticPairEdges = [])
    (childrenNodup : ∀ candidate,
      (molecularSource.molecule.aromaticCanonicalOfficialCIPChildrenAt
        molecularSource.molecule.atomCount candidate).Nodup) :
    Equiv.Perm (molecularSource.AromaticCanonicalOccurrence fuel) where
  toFun := mapAromaticCanonicalOccurrence molecularSource fuel atomPermutation
    constitution noEdges childrenNodup
  invFun := mapAromaticCanonicalOccurrence molecularSource fuel atomPermutation
    constitution noEdges childrenNodup
  left_inv := mapAromaticCanonicalOccurrence_involutive molecularSource fuel atomPermutation
    constitution involutive noEdges childrenNodup
  right_inv := mapAromaticCanonicalOccurrence_involutive molecularSource fuel atomPermutation
    constitution involutive noEdges childrenNodup

@[simp] theorem mapAromaticCanonicalOccurrence_root
    (molecularSource : AuthoritativeChemicalInput) (fuel : Nat)
    (atomPermutation : Equiv.Perm molecularSource.AromaticCanonicalAtom)
    (constitution : molecularSource.AromaticCanonicalConstitutionAutomorphism atomPermutation)
    (noEdges : molecularSource.molecule.aromaticPairEdges = [])
    (childrenNodup : ∀ candidate,
      (molecularSource.molecule.aromaticCanonicalOfficialCIPChildrenAt
        molecularSource.molecule.atomCount candidate).Nodup)
    (occurrence : molecularSource.AromaticCanonicalOccurrence fuel) :
    (mapAromaticCanonicalOccurrence molecularSource fuel atomPermutation constitution
      noEdges childrenNodup occurrence).1.root = atomPermutation occurrence.1.root := by
  rfl

@[simp] theorem mapAromaticCanonicalOccurrence_remaining
    (molecularSource : AuthoritativeChemicalInput) (fuel : Nat)
    (atomPermutation : Equiv.Perm molecularSource.AromaticCanonicalAtom)
    (constitution : molecularSource.AromaticCanonicalConstitutionAutomorphism atomPermutation)
    (noEdges : molecularSource.molecule.aromaticPairEdges = [])
    (childrenNodup : ∀ candidate,
      (molecularSource.molecule.aromaticCanonicalOfficialCIPChildrenAt
        molecularSource.molecule.atomCount candidate).Nodup)
    (occurrence : molecularSource.AromaticCanonicalOccurrence fuel) :
    (mapAromaticCanonicalOccurrence molecularSource fuel atomPermutation constitution
      noEdges childrenNodup occurrence).1.remaining = occurrence.1.remaining := by
  rfl

theorem mapAromaticCanonicalOccurrence_address_length
    (molecularSource : AuthoritativeChemicalInput) (fuel : Nat)
    (atomPermutation : Equiv.Perm molecularSource.AromaticCanonicalAtom)
    (constitution : molecularSource.AromaticCanonicalConstitutionAutomorphism atomPermutation)
    (noEdges : molecularSource.molecule.aromaticPairEdges = [])
    (childrenNodup : ∀ candidate,
      (molecularSource.molecule.aromaticCanonicalOfficialCIPChildrenAt
        molecularSource.molecule.atomCount candidate).Nodup)
    (occurrence : molecularSource.AromaticCanonicalOccurrence fuel) :
    (mapAromaticCanonicalOccurrence molecularSource fuel atomPermutation constitution
      noEdges childrenNodup occurrence).1.address.length = occurrence.1.address.length := by
  have mappedGrade := molecularSource.aromaticCanonicalOccurrence_depthGrade
    (mapAromaticCanonicalOccurrence molecularSource fuel atomPermutation constitution
      noEdges childrenNodup occurrence)
  have sourceGrade := molecularSource.aromaticCanonicalOccurrence_depthGrade occurrence
  have remainingEq := mapAromaticCanonicalOccurrence_remaining molecularSource fuel
    atomPermutation constitution noEdges childrenNodup occurrence
  omega

theorem aromaticCanonicalDepthDependency_map_iff
    (molecularSource : AuthoritativeChemicalInput) (fuel : Nat)
    (atomPermutation : Equiv.Perm molecularSource.AromaticCanonicalAtom)
    (constitution : molecularSource.AromaticCanonicalConstitutionAutomorphism atomPermutation)
    (noEdges : molecularSource.molecule.aromaticPairEdges = [])
    (childrenNodup : ∀ candidate,
      (molecularSource.molecule.aromaticCanonicalOfficialCIPChildrenAt
        molecularSource.molecule.atomCount candidate).Nodup)
    (dependency target : molecularSource.AromaticCanonicalOccurrence fuel) :
    molecularSource.AromaticCanonicalDepthDependency
        (mapAromaticCanonicalOccurrence molecularSource fuel atomPermutation constitution
          noEdges childrenNodup dependency)
        (mapAromaticCanonicalOccurrence molecularSource fuel atomPermutation constitution
          noEdges childrenNodup target) ↔
      molecularSource.AromaticCanonicalDepthDependency dependency target := by
  unfold AuthoritativeChemicalInput.AromaticCanonicalDepthDependency
  rw [mapAromaticCanonicalOccurrence_root, mapAromaticCanonicalOccurrence_root,
    mapAromaticCanonicalOccurrence_address_length,
    mapAromaticCanonicalOccurrence_address_length]
  simp only [atomPermutation.injective.eq_iff]

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
