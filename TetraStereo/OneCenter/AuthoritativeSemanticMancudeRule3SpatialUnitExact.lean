import TetraStereo.OneCenter.AuthoritativeSemanticMancudeRule3SpatialUnit

set_option autoImplicit false

namespace TetraStereo.OneCenter

noncomputable section

namespace ExactOfficialRuleMajorKey

variable {V : Type*} [Fintype V] [DecidableEq V]

/-!
# Exact source-canonical Rule-3 spatial-unit semantics

This module removes the last recursive constitutional compiler and endpoint-selector equations
from the source Rule-3 spatial-unit boundary.  It first gives the partial exact-key insertion and
sort an independent stable structural relation on complete keys.  It then characterizes the
complete recursive provenance-tree compiler, the aligned substituent compiler, and the strict
senior-reference selector in both directions.  Source coordinate lookup and rational Rule-3
geometry already have exact `iff` theorems, so the final result is an exact relational account of
the entire spatial-unit leaf.
-/

/-- On complete keys the safe comparator returns the total exact Rules-1a--2 comparison. -/
theorem compare?_eq_some_compare_of_complete
    (m : MoleculeGraph V) (left right : ExactOfficialRuleMajorKey V)
    (leftComplete : left.complete = true) (rightComplete : right.complete = true) :
    compare? m left right = some (compare m left right) := by
  have present := compare?_isSome_of_complete m left right leftComplete rightComplete
  cases computed : compare? m left right with
  | none => simp [computed] at present
  | some outcome =>
      have exact := compare_eq_of_compare?_eq_some m left right outcome computed
      simp [exact]

/-- Independent stable insertion of one complete exact constitutional key. -/
inductive DeclarativeInsertComplete
    (m : MoleculeGraph V) (key : ExactOfficialRuleMajorKey V) :
    List (ExactOfficialRuleMajorKey V) → List (ExactOfficialRuleMajorKey V) → Prop
  | nil : DeclarativeInsertComplete m key [] [key]
  | beforeEq {head tail}
      (compared : compare m key head = .eq) :
      DeclarativeInsertComplete m key (head :: tail) (key :: head :: tail)
  | beforeGt {head tail}
      (compared : compare m key head = .gt) :
      DeclarativeInsertComplete m key (head :: tail) (key :: head :: tail)
  | afterLt {head tail inserted}
      (compared : compare m key head = .lt)
      (tailDerived : DeclarativeInsertComplete m key tail inserted) :
      DeclarativeInsertComplete m key (head :: tail) (head :: inserted)

theorem DeclarativeInsertComplete.perm
    (m : MoleculeGraph V) (key : ExactOfficialRuleMajorKey V)
    {keys result : List (ExactOfficialRuleMajorKey V)}
    (derived : DeclarativeInsertComplete m key keys result) :
    result.Perm (key :: keys) := by
  induction derived with
  | nil => exact .refl _
  | beforeEq => exact .refl _
  | beforeGt => exact .refl _
  | @afterLt head tail inserted compared tailDerived ih =>
      exact (List.Perm.cons head ih).trans (List.Perm.swap key head tail)

/-- Partial executable insertion is exactly stable insertion on complete inputs. -/
theorem insert?_eq_some_iff_declarativeComplete
    (m : MoleculeGraph V) (key : ExactOfficialRuleMajorKey V)
    (keyComplete : key.complete = true) :
    ∀ (keys result : List (ExactOfficialRuleMajorKey V)),
      (∀ child, child ∈ keys → child.complete = true) →
      (insert? m key keys = some result ↔
        DeclarativeInsertComplete m key keys result)
  | [], result => by
      intro _
      constructor
      · intro computed
        simp [insert?] at computed
        subst result
        exact .nil
      · intro derived
        cases derived
        rfl
  | head :: tail, result => by
      intro allComplete
      have headComplete := allComplete head (by simp)
      have tailComplete : ∀ child, child ∈ tail → child.complete = true := by
        intro child present
        exact allComplete child (by simp [present])
      have safe := compare?_eq_some_compare_of_complete
        m key head keyComplete headComplete
      cases comparison : compare m key head with
      | eq =>
          rw [comparison] at safe
          constructor
          · intro computed
            simp [insert?, safe] at computed
            subst result
            exact .beforeEq comparison
          · intro derived
            cases derived with
            | beforeEq compared => simp [insert?, safe]
            | beforeGt compared => simp [comparison] at compared
            | afterLt compared _ => simp [comparison] at compared
      | gt =>
          rw [comparison] at safe
          constructor
          · intro computed
            simp [insert?, safe] at computed
            subst result
            exact .beforeGt comparison
          · intro derived
            cases derived with
            | beforeEq compared => simp [comparison] at compared
            | beforeGt compared => simp [insert?, safe]
            | afterLt compared _ => simp [comparison] at compared
      | lt =>
          rw [comparison] at safe
          constructor
          · intro computed
            simp only [insert?, safe, Option.map_eq_some_iff] at computed
            rcases computed with ⟨inserted, insertedComputed, rfl⟩
            exact .afterLt comparison
              ((insert?_eq_some_iff_declarativeComplete
                m key keyComplete tail inserted tailComplete).mp insertedComputed)
          · intro derived
            cases derived with
            | beforeEq compared => simp [comparison] at compared
            | beforeGt compared => simp [comparison] at compared
            | afterLt compared tailDerived =>
                simp only [insert?, safe, Option.map_eq_some_iff]
                exact ⟨_,
                  (insert?_eq_some_iff_declarativeComplete
                    m key keyComplete tail _ tailComplete).mpr tailDerived, rfl⟩

/-- Independent stable sort of complete exact constitutional keys. -/
inductive DeclarativeSortComplete (m : MoleculeGraph V) :
    List (ExactOfficialRuleMajorKey V) → List (ExactOfficialRuleMajorKey V) → Prop
  | nil : DeclarativeSortComplete m [] []
  | cons {key keys sortedTail result}
      (tail : DeclarativeSortComplete m keys sortedTail)
      (inserted : DeclarativeInsertComplete m key sortedTail result) :
      DeclarativeSortComplete m (key :: keys) result

theorem DeclarativeSortComplete.perm
    (m : MoleculeGraph V) {keys result : List (ExactOfficialRuleMajorKey V)}
    (derived : DeclarativeSortComplete m keys result) : result.Perm keys := by
  induction derived with
  | nil => exact .refl _
  | @cons key keys sortedTail result tail inserted ih =>
      exact (inserted.perm.trans (List.Perm.cons key ih))

/-- Partial executable sorting is exactly stable sorting on complete inputs. -/
theorem sort?_eq_some_iff_declarativeComplete
    (m : MoleculeGraph V) :
    ∀ (keys result : List (ExactOfficialRuleMajorKey V)),
      (∀ key, key ∈ keys → key.complete = true) →
      (sort? m keys = some result ↔ DeclarativeSortComplete m keys result)
  | [], result => by
      intro _
      constructor
      · intro computed
        simp [sort?] at computed
        subst result
        exact .nil
      · intro derived
        cases derived
        rfl
  | key :: keys, result => by
      intro allComplete
      have keyComplete := allComplete key (by simp)
      have tailComplete : ∀ child, child ∈ keys → child.complete = true := by
        intro child present
        exact allComplete child (by simp [present])
      constructor
      · intro computed
        unfold sort? at computed
        cases tailComputed : sort? m keys with
        | none => simp [tailComputed] at computed
        | some sortedTail =>
            have tailDerived :=
              (sort?_eq_some_iff_declarativeComplete
                m keys sortedTail tailComplete).mp tailComputed
            have sortedComplete :
                ∀ child, child ∈ sortedTail → child.complete = true := by
              intro child present
              exact tailComplete child
                ((tailDerived.perm.mem_iff).mp present)
            exact .cons tailDerived
              ((insert?_eq_some_iff_declarativeComplete
                m key keyComplete sortedTail result sortedComplete).mp (by
                  simpa [tailComputed] using computed))
      · intro derived
        cases derived with
        | @cons _ _ sortedTail _ tailDerived inserted =>
            have tailComputed :=
              (sort?_eq_some_iff_declarativeComplete
                m keys sortedTail tailComplete).mpr tailDerived
            have sortedComplete :
                ∀ child, child ∈ sortedTail → child.complete = true := by
              intro child present
              exact tailComplete child
                ((tailDerived.perm.mem_iff).mp present)
            have insertedComputed :=
              (insert?_eq_some_iff_declarativeComplete
                m key keyComplete sortedTail result sortedComplete).mpr inserted
            simp [sort?, tailComputed, insertedComputed]

end ExactOfficialRuleMajorKey

namespace MoleculeGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

mutual
  /-- Canonical structural derivation of a complete exact Rules-1a--2 provenance key. -/
  inductive CanonicalCompleteExactOfficialRuleMajorKey
      (m : MoleculeGraph V)
      (children : OfficialCIPNode V → List (OfficialCIPNode V)) :
      Nat → OfficialCIPNode V → ExactOfficialRuleMajorKey V → Prop
    | terminal {fuel node}
        (empty : children node = []) :
        CanonicalCompleteExactOfficialRuleMajorKey m children fuel node
          (exactOfficialRuleMajorRootKey node true)
    | branch {fuel node childKeys sorted}
        (nonempty : children node ≠ [])
        (childrenDerived : CanonicalCompleteExactOfficialRuleMajorKeyList
          m children fuel (children node) childKeys)
        (sortedDerived : ExactOfficialRuleMajorKey.DeclarativeSortComplete
          m childKeys sorted)
        (sortedComplete : ∀ childKey, childKey ∈ sorted →
          childKey.complete = true) :
        CanonicalCompleteExactOfficialRuleMajorKey m children (fuel + 1) node
          (ExactOfficialRuleMajorKey.assemble
            (exactOfficialRuleMajorRootKey node false) sorted)

  /-- Pointwise canonical derivation for an aligned child-key list. -/
  inductive CanonicalCompleteExactOfficialRuleMajorKeyList
      (m : MoleculeGraph V)
      (children : OfficialCIPNode V → List (OfficialCIPNode V)) :
      Nat → List (OfficialCIPNode V) → List (ExactOfficialRuleMajorKey V) → Prop
    | nil {fuel} : CanonicalCompleteExactOfficialRuleMajorKeyList
        m children fuel [] []
    | cons {fuel node nodes key keys}
        (head : CanonicalCompleteExactOfficialRuleMajorKey
          m children fuel node key)
        (tail : CanonicalCompleteExactOfficialRuleMajorKeyList
          m children fuel nodes keys) :
        CanonicalCompleteExactOfficialRuleMajorKeyList
          m children fuel (node :: nodes) (key :: keys)
end

theorem CanonicalCompleteExactOfficialRuleMajorKeyList.iff_forall₂
    (m : MoleculeGraph V)
    (children : OfficialCIPNode V → List (OfficialCIPNode V))
    (fuel : Nat) (nodes : List (OfficialCIPNode V))
    (keys : List (ExactOfficialRuleMajorKey V)) :
    CanonicalCompleteExactOfficialRuleMajorKeyList
        m children fuel nodes keys ↔
      List.Forall₂
        (CanonicalCompleteExactOfficialRuleMajorKey m children fuel)
        nodes keys := by
  constructor
  · intro derived
    induction nodes generalizing keys with
    | nil =>
        cases derived
        exact .nil
    | cons node nodes ih =>
        cases derived with
        | cons head tail => exact .cons head (ih _ tail)
  · intro derived
    induction derived with
    | nil => exact .nil
    | cons head tail ih => exact .cons head ih

/-- Every structurally derived complete key is marked complete. -/
theorem CanonicalCompleteExactOfficialRuleMajorKey.complete
    (m : MoleculeGraph V)
    (children : OfficialCIPNode V → List (OfficialCIPNode V)) :
    ∀ {fuel node key},
      CanonicalCompleteExactOfficialRuleMajorKey m children fuel node key →
        key.complete = true := by
  intro fuel node key derived
  cases derived with
  | terminal empty => rfl
  | @branch fuel node childKeys sorted nonempty childrenDerived sortedDerived
      sortedComplete =>
      change sorted.all ExactOfficialRuleMajorKey.complete = true
      exact List.all_eq_true.mpr sortedComplete

private theorem forall₂_right_property
    {α β : Type*} {R : α → β → Prop} {Q : β → Prop} :
    ∀ (left : List α) (right : List β),
      List.Forall₂ R left right →
      (∀ x y, R x y → Q y) →
      ∀ y, y ∈ right → Q y
  | [], [], .nil, _ => by simp
  | x :: xs, y :: ys, .cons head tail, sound => by
      intro observed present
      rcases List.mem_cons.mp present with rfl | tailPresent
      · exact sound x observed head
      · exact forall₂_right_property xs ys tail sound observed tailPresent

private theorem mapM_eq_some_iff_forall₂_of_mem
    {α β : Type*} (f : α → Option β) (P : α → β → Prop) :
    ∀ (inputs : List α) (outputs : List β),
      (∀ input, input ∈ inputs → ∀ output, f input = some output ↔ P input output) →
      (inputs.mapM f = some outputs ↔ List.Forall₂ P inputs outputs)
  | [], outputs => by
      intro _
      constructor
      · intro computed
        simp at computed
        subst outputs
        exact .nil
      · intro derived
        cases derived
        rfl
  | input :: inputs, outputs => by
      intro exactAt
      constructor
      · intro computed
        rw [List.mapM_cons] at computed
        cases headComputed : f input with
        | none => simp [headComputed] at computed
        | some head =>
            cases tailComputed : inputs.mapM f with
            | none => simp [headComputed, tailComputed] at computed
            | some tail =>
                simp [headComputed, tailComputed] at computed
                subst outputs
                exact .cons
                  ((exactAt input (by simp) head).mp headComputed)
                  ((mapM_eq_some_iff_forall₂_of_mem f P inputs tail (by
                    intro tailInput tailPresent output
                    exact exactAt tailInput (by simp [tailPresent]) output)).mp
                      tailComputed)
      · intro derived
        cases derived with
        | cons headDerived tailDerived =>
            rw [List.mapM_cons]
            rw [(exactAt input (by simp) _).mpr headDerived]
            rw [(mapM_eq_some_iff_forall₂_of_mem f P inputs _ (by
              intro tailInput tailPresent output
              exact exactAt tailInput (by simp [tailPresent]) output)).mpr tailDerived]
            rfl

/-- At an exhaustive depth bound, the recursive exact-key compiler is exactly its canonical
structural derivation. -/
theorem buildExactOfficialRuleMajorKey_eq_some_iff_canonicalComplete
    (m : MoleculeGraph V)
    (children : OfficialCIPNode V → List (OfficialCIPNode V)) :
    ∀ (fuel : Nat) (node : OfficialCIPNode V) (key : ExactOfficialRuleMajorKey V),
      OfficialExpansionCompleteWithin children fuel node →
      (m.buildExactOfficialRuleMajorKey children fuel node = some key ↔
        CanonicalCompleteExactOfficialRuleMajorKey m children fuel node key)
  | 0, node, key, complete => by
      change children node = [] at complete
      constructor
      · intro computed
        simp [buildExactOfficialRuleMajorKey, complete] at computed
        subst key
        exact .terminal complete
      · intro derived
        cases derived with
        | terminal empty => simp [buildExactOfficialRuleMajorKey, empty]
  | fuel + 1, node, key, complete => by
      by_cases terminal : children node = []
      · constructor
        · intro computed
          simp [buildExactOfficialRuleMajorKey, terminal] at computed
          subst key
          exact .terminal terminal
        · intro derived
          cases derived with
          | terminal empty => simp [buildExactOfficialRuleMajorKey, empty]
          | branch nonempty _ _ _ => exact (nonempty terminal).elim
      · constructor
        · intro computed
          unfold buildExactOfficialRuleMajorKey at computed
          rw [if_neg (by simpa using terminal)] at computed
          cases childrenComputed : (children node).mapM
              (m.buildExactOfficialRuleMajorKey children fuel) with
          | none => simp [childrenComputed] at computed
          | some childKeys =>
              cases sortedComputed : ExactOfficialRuleMajorKey.sort? m childKeys with
              | none => simp [childrenComputed, sortedComputed] at computed
              | some sorted =>
                  simp [childrenComputed, sortedComputed] at computed
                  subst key
                  have childrenDerived :
                      CanonicalCompleteExactOfficialRuleMajorKeyList
                        m children fuel (children node) childKeys :=
                    (CanonicalCompleteExactOfficialRuleMajorKeyList.iff_forall₂
                      m children fuel (children node) childKeys).mpr
                      ((mapM_eq_some_iff_forall₂_of_mem
                        (m.buildExactOfficialRuleMajorKey children fuel)
                        (CanonicalCompleteExactOfficialRuleMajorKey m children fuel)
                        (children node) childKeys (by
                          intro child present childKey
                          exact buildExactOfficialRuleMajorKey_eq_some_iff_canonicalComplete
                            m children fuel child childKey (complete child present))).mp
                        childrenComputed)
                  have childComplete : ∀ childKey, childKey ∈ childKeys →
                      childKey.complete = true := by
                    have pointwise :=
                      (CanonicalCompleteExactOfficialRuleMajorKeyList.iff_forall₂
                        m children fuel (children node) childKeys).mp childrenDerived
                    exact forall₂_right_property (children node) childKeys pointwise
                      (fun _ _ derived => derived.complete)
                  have sortedDerived :=
                    (ExactOfficialRuleMajorKey.sort?_eq_some_iff_declarativeComplete
                      m childKeys sorted childComplete).mp sortedComputed
                  have sortedComplete : ∀ childKey, childKey ∈ sorted →
                      childKey.complete = true := by
                    intro childKey present
                    exact childComplete childKey
                      ((sortedDerived.perm.mem_iff).mp present)
                  exact .branch terminal childrenDerived sortedDerived sortedComplete
        · intro derived
          cases derived with
          | terminal empty => exact (terminal empty).elim
          | @branch _ _ childKeys sorted nonempty childrenDerived sortedDerived
              storedSortedComplete =>
              have childrenComputed :=
                (mapM_eq_some_iff_forall₂_of_mem
                  (m.buildExactOfficialRuleMajorKey children fuel)
                  (CanonicalCompleteExactOfficialRuleMajorKey m children fuel)
                  (children node) childKeys (by
                    intro child present childKey
                    exact buildExactOfficialRuleMajorKey_eq_some_iff_canonicalComplete
                      m children fuel child childKey (complete child present))).mpr
                  ((CanonicalCompleteExactOfficialRuleMajorKeyList.iff_forall₂
                    m children fuel (children node) childKeys).mp childrenDerived)
              have childComplete : ∀ childKey, childKey ∈ childKeys →
                  childKey.complete = true := by
                have pointwise :=
                  (CanonicalCompleteExactOfficialRuleMajorKeyList.iff_forall₂
                    m children fuel (children node) childKeys).mp childrenDerived
                exact forall₂_right_property (children node) childKeys pointwise
                  (fun _ _ derived => derived.complete)
              have sortedComputed :=
                (ExactOfficialRuleMajorKey.sort?_eq_some_iff_declarativeComplete
                  m childKeys sorted childComplete).mpr sortedDerived
              simp [buildExactOfficialRuleMajorKey, terminal,
                childrenComputed, sortedComputed]

end MoleculeGraph

namespace AuthoritativeChemicalInput

/-- Exact structural meaning of one complete source-canonical Rules-1a--2 branch key. -/
def CanonicalAromaticCanonicalRule3BranchKey
    (source : AuthoritativeChemicalInput)
    (endpoint reference : source.AromaticCanonicalAtom)
    (key : ExactOfficialRuleMajorKey source.AromaticCanonicalAtom) : Prop :=
  MoleculeGraph.CanonicalCompleteExactOfficialRuleMajorKey
    source.molecule.toLocalizedMoleculeGraph
    (source.molecule.aromaticCanonicalOfficialCIPChildrenAt source.molecule.atomCount)
    (source.molecule.atomCount + 1)
    (OfficialCIPNode.rootFromEdge endpoint reference) key

/-- The source branch-key compiler is exact on every represented endpoint substituent. -/
theorem buildAromaticCanonicalRule3BranchKey?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput)
    (endpoint partner reference : source.AromaticCanonicalAtom)
    (present : reference ∈ source.aromaticCanonicalRule3Substituents endpoint partner)
    (key : ExactOfficialRuleMajorKey source.AromaticCanonicalAtom) :
    source.buildAromaticCanonicalRule3BranchKey? endpoint reference = some key ↔
      source.CanonicalAromaticCanonicalRule3BranchKey endpoint reference key := by
  unfold buildAromaticCanonicalRule3BranchKey?
  rw [source.molecule.toLocalizedMoleculeGraph
    |>.buildObservedExactOfficialRuleMajorKey_eq_exact
      source.molecule.semanticExactOfficialRule1aObservation
      source.molecule.semanticExactOfficialRule1aObservation_eq_independent]
  exact source.molecule.toLocalizedMoleculeGraph
    |>.buildExactOfficialRuleMajorKey_eq_some_iff_canonicalComplete
      (source.molecule.aromaticCanonicalOfficialCIPChildrenAt source.molecule.atomCount)
      (source.molecule.atomCount + 1)
      (OfficialCIPNode.rootFromEdge endpoint reference) key
      (source.molecule.aromaticCanonicalExpansionCompleteWithin_rootFromEdge_default
        (source.aromaticCanonicalRule3Substituent_ne_endpoint
          endpoint partner reference present))

/-- Exact pointwise meaning of one represented and constitutionally compiled substituent. -/
def CanonicalAromaticCanonicalRule3RankedSubstituent
    (source : AuthoritativeChemicalInput)
    (endpoint reference : source.AromaticCanonicalAtom)
    (ranked : source.AromaticCanonicalRule3RankedSubstituent) : Prop :=
  ranked.atom = reference ∧
    source.CanonicalAromaticCanonicalRule3BranchKey
      endpoint reference ranked.key

/-- One represented substituent compiles exactly to its canonical structural branch. -/
theorem buildAromaticCanonicalRule3RankedSubstituent?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput)
    (endpoint partner reference : source.AromaticCanonicalAtom)
    (present : reference ∈ source.aromaticCanonicalRule3Substituents endpoint partner)
    (ranked : source.AromaticCanonicalRule3RankedSubstituent) :
    source.buildAromaticCanonicalRule3RankedSubstituent? endpoint reference = some ranked ↔
      source.CanonicalAromaticCanonicalRule3RankedSubstituent
        endpoint reference ranked := by
  constructor
  · intro computed
    unfold buildAromaticCanonicalRule3RankedSubstituent? at computed
    cases keyComputed : source.buildAromaticCanonicalRule3BranchKey?
        endpoint reference with
    | none => simp [keyComputed] at computed
    | some key =>
        simp [keyComputed] at computed
        subst ranked
        exact ⟨rfl,
          (source.buildAromaticCanonicalRule3BranchKey?_eq_some_iff_canonical
            endpoint partner reference present key).mp keyComputed⟩
  · rintro ⟨atomEq, keyDerived⟩
    have keyComputed :=
      (source.buildAromaticCanonicalRule3BranchKey?_eq_some_iff_canonical
        endpoint partner reference present ranked.key).mpr keyDerived
    unfold buildAromaticCanonicalRule3RankedSubstituent?
    rw [keyComputed]
    cases ranked
    simp_all

/-- Pointwise compilation of any represented substituent sublist is exact. -/
theorem mapM_buildAromaticCanonicalRule3RankedSubstituent?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom) :
    ∀ (candidates : List source.AromaticCanonicalAtom)
      (ranked : List source.AromaticCanonicalRule3RankedSubstituent),
      (∀ reference, reference ∈ candidates →
        reference ∈ source.aromaticCanonicalRule3Substituents endpoint partner) →
      (candidates.mapM
          (source.buildAromaticCanonicalRule3RankedSubstituent? endpoint) = some ranked ↔
        List.Forall₂
          (source.CanonicalAromaticCanonicalRule3RankedSubstituent endpoint)
          candidates ranked)
  | [], ranked => by
      intro _
      constructor
      · intro computed
        simp at computed
        subst ranked
        exact .nil
      · intro derived
        cases derived
        rfl
  | reference :: candidates, ranked => by
      intro sublist
      constructor
      · intro computed
        rw [List.mapM_cons] at computed
        cases headComputed : source.buildAromaticCanonicalRule3RankedSubstituent?
            endpoint reference with
        | none => simp [headComputed] at computed
        | some head =>
            cases tailComputed : candidates.mapM
                (source.buildAromaticCanonicalRule3RankedSubstituent? endpoint) with
            | none => simp [headComputed, tailComputed] at computed
            | some tail =>
                simp [headComputed, tailComputed] at computed
                subst ranked
                exact .cons
                  ((source.buildAromaticCanonicalRule3RankedSubstituent?_eq_some_iff_canonical
                    endpoint partner reference (sublist reference (by simp)) head).mp
                    headComputed)
                  ((source.mapM_buildAromaticCanonicalRule3RankedSubstituent?_eq_some_iff_canonical
                    endpoint partner candidates tail (by
                      intro candidate present
                      exact sublist candidate (by simp [present]))).mp tailComputed)
      · intro derived
        cases derived with
        | cons headDerived tailDerived =>
            rw [List.mapM_cons]
            rw [(source.buildAromaticCanonicalRule3RankedSubstituent?_eq_some_iff_canonical
              endpoint partner reference (sublist reference (by simp)) _).mpr headDerived]
            rw [(source.mapM_buildAromaticCanonicalRule3RankedSubstituent?_eq_some_iff_canonical
              endpoint partner candidates _ (by
                intro candidate present
                exact sublist candidate (by simp [present]))).mpr tailDerived]
            rfl

/-- Exact source meaning of the selected strict constitutional senior reference. -/
def CanonicalAromaticCanonicalRule3ConstitutionalSeniorReference
    (source : AuthoritativeChemicalInput)
    (endpoint partner reference : source.AromaticCanonicalAtom) : Prop :=
  ∃ ranked senior,
    List.Forall₂
      (source.CanonicalAromaticCanonicalRule3RankedSubstituent endpoint)
      (source.aromaticCanonicalRule3Substituents endpoint partner) ranked ∧
    source.DeclarativeAromaticCanonicalRule3StrictlySenior ranked senior ∧
    senior.atom = reference

/-- Two strict maxima of the same ranked list must name the same represented atom. -/
theorem DeclarativeAromaticCanonicalRule3StrictlySenior.atom_eq
    (source : AuthoritativeChemicalInput)
    (ranked : List source.AromaticCanonicalRule3RankedSubstituent)
    (left right : source.AromaticCanonicalRule3RankedSubstituent)
    (leftSenior : source.DeclarativeAromaticCanonicalRule3StrictlySenior ranked left)
    (rightSenior : source.DeclarativeAromaticCanonicalRule3StrictlySenior ranked right) :
    left.atom = right.atom := by
  by_contra different
  have leftOverRight := leftSenior.2 right rightSenior.1 (Ne.symm different)
  have rightOverLeft := rightSenior.2 left leftSenior.1 different
  letI : Std.TransCmp
      (ExactOfficialRuleMajorKey.compare source.molecule.toLocalizedMoleculeGraph) :=
    ExactOfficialRuleMajorKey.compare_transCmp
      source.molecule.toLocalizedMoleculeGraph
  have reverse := leftOverRight
  rw [Std.OrientedCmp.gt_iff_lt] at reverse
  simp [rightOverLeft] at reverse

/-- The endpoint senior-reference selector succeeds exactly on the canonical strict maximum. -/
theorem aromaticCanonicalRule3ConstitutionalSeniorReference?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput)
    (endpoint partner reference : source.AromaticCanonicalAtom) :
    source.aromaticCanonicalRule3ConstitutionalSeniorReference?
        endpoint partner = some reference ↔
      source.CanonicalAromaticCanonicalRule3ConstitutionalSeniorReference
        endpoint partner reference := by
  classical
  let candidates := source.aromaticCanonicalRule3Substituents endpoint partner
  constructor
  · intro computed
    unfold aromaticCanonicalRule3ConstitutionalSeniorReference? at computed
    cases rankedComputed : candidates.mapM
        (source.buildAromaticCanonicalRule3RankedSubstituent? endpoint) with
    | none => simp [candidates, rankedComputed] at computed
    | some ranked =>
        cases seniorComputed : ranked.find? fun candidate =>
            source.aromaticCanonicalRule3StrictlyOutranksAll candidate ranked with
        | none => simp [candidates, rankedComputed, seniorComputed] at computed
        | some senior =>
            simp [candidates, rankedComputed, seniorComputed] at computed
            subst reference
            have checked :
                source.aromaticCanonicalRule3StrictlyOutranksAll senior ranked = true :=
              @List.find?_some _
                (fun candidate =>
                  source.aromaticCanonicalRule3StrictlyOutranksAll candidate ranked)
                senior ranked seniorComputed
            have present : senior ∈ ranked := by
              rcases (List.find?_eq_some_iff_append.mp seniorComputed).2 with
                ⟨before, after, identity, _⟩
              rw [identity]
              simp
            refine ⟨ranked, senior, ?_, ⟨present, ?_⟩, rfl⟩
            · exact
                (source.mapM_buildAromaticCanonicalRule3RankedSubstituent?_eq_some_iff_canonical
                  endpoint partner candidates ranked (by
                    intro candidate candidatePresent
                    exact candidatePresent)).mp rankedComputed
            · exact
                (source.aromaticCanonicalRule3StrictlyOutranksAll_eq_true_iff
                  senior ranked).mp checked
  · rintro ⟨ranked, senior, rankedDerived, seniorStrict, seniorAtom⟩
    have rankedComputed :=
      (source.mapM_buildAromaticCanonicalRule3RankedSubstituent?_eq_some_iff_canonical
        endpoint partner candidates ranked (by
          intro candidate candidatePresent
          exact candidatePresent)).mpr rankedDerived
    have seniorChecked :
        source.aromaticCanonicalRule3StrictlyOutranksAll senior ranked = true :=
      (source.aromaticCanonicalRule3StrictlyOutranksAll_eq_true_iff
        senior ranked).mpr seniorStrict.2
    have foundExists :
        (ranked.find? fun candidate =>
          source.aromaticCanonicalRule3StrictlyOutranksAll candidate ranked).isSome = true := by
      rw [List.find?_isSome]
      exact ⟨senior, seniorStrict.1, seniorChecked⟩
    cases foundComputed : ranked.find? fun candidate =>
        source.aromaticCanonicalRule3StrictlyOutranksAll candidate ranked with
    | none => simp [foundComputed] at foundExists
    | some found =>
        have foundChecked :
            source.aromaticCanonicalRule3StrictlyOutranksAll found ranked = true :=
          @List.find?_some _
            (fun candidate =>
              source.aromaticCanonicalRule3StrictlyOutranksAll candidate ranked)
            found ranked foundComputed
        have foundPresent : found ∈ ranked := by
          rcases (List.find?_eq_some_iff_append.mp foundComputed).2 with
            ⟨before, after, identity, _⟩
          rw [identity]
          simp
        have foundStrict :
            source.DeclarativeAromaticCanonicalRule3StrictlySenior ranked found :=
          ⟨foundPresent,
            (source.aromaticCanonicalRule3StrictlyOutranksAll_eq_true_iff
              found ranked).mp foundChecked⟩
        have foundAtom : found.atom = senior.atom :=
          DeclarativeAromaticCanonicalRule3StrictlySenior.atom_eq
            source ranked found senior foundStrict seniorStrict
        have foundReference : found.atom = reference := foundAtom.trans seniorAtom
        unfold aromaticCanonicalRule3ConstitutionalSeniorReference?
        simp [candidates, rankedComputed, foundComputed, foundReference]

/-- Fully relational exact meaning of a positive source Rule-3 spatial unit. -/
def CanonicalAromaticCanonicalRule3SpatialUnit
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalAtom)
    (result : source.AromaticCanonicalRule3SpatialUnitResult) : Prop :=
  source.AromaticCanonicalOrdinaryDoubleBond left right ∧
    source.CanonicalAromaticCanonicalRule3ConstitutionalSeniorReference
      left right result.leftReference ∧
    source.CanonicalAromaticCanonicalRule3ConstitutionalSeniorReference
      right left result.rightReference ∧
    ∃ leftPoint rightPoint leftReferencePoint rightReferencePoint,
      source.SemanticAromaticCanonicalSpatialPointAt left leftPoint ∧
      source.SemanticAromaticCanonicalSpatialPointAt right rightPoint ∧
      source.SemanticAromaticCanonicalSpatialPointAt
        result.leftReference leftReferencePoint ∧
      source.SemanticAromaticCanonicalSpatialPointAt
        result.rightReference rightReferencePoint ∧
      RationalRule3SpatialGeometry leftPoint rightPoint
        leftReferencePoint rightReferencePoint result.geometry

/-- The complete source Rule-3 spatial-unit evaluator succeeds exactly on the canonical
constitutional-reference and rational-spatial relation. -/
theorem aromaticCanonicalRule3SpatialUnit?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalAtom)
    (result : source.AromaticCanonicalRule3SpatialUnitResult) :
    source.aromaticCanonicalRule3SpatialUnit? left right = some result ↔
      source.CanonicalAromaticCanonicalRule3SpatialUnit left right result := by
  classical
  constructor
  · intro computed
    unfold aromaticCanonicalRule3SpatialUnit? at computed
    by_cases ordinary : source.AromaticCanonicalOrdinaryDoubleBond left right
    · rw [if_pos ordinary] at computed
      cases leftReferenceComputed :
          source.aromaticCanonicalRule3ConstitutionalSeniorReference? left right with
      | none => simp [leftReferenceComputed] at computed
      | some leftReference =>
          cases rightReferenceComputed :
              source.aromaticCanonicalRule3ConstitutionalSeniorReference? right left with
          | none => simp [leftReferenceComputed, rightReferenceComputed] at computed
          | some rightReference =>
              cases leftPointComputed : source.aromaticCanonicalSpatialPointAt? left with
              | none =>
                  simp [leftReferenceComputed, rightReferenceComputed,
                    leftPointComputed] at computed
              | some leftPoint =>
                  cases rightPointComputed : source.aromaticCanonicalSpatialPointAt? right with
                  | none =>
                      simp [leftReferenceComputed, rightReferenceComputed,
                        leftPointComputed, rightPointComputed] at computed
                  | some rightPoint =>
                      cases leftReferencePointComputed :
                          source.aromaticCanonicalSpatialPointAt? leftReference with
                      | none =>
                          simp [leftReferenceComputed, rightReferenceComputed,
                            leftPointComputed, rightPointComputed,
                            leftReferencePointComputed] at computed
                      | some leftReferencePoint =>
                          cases rightReferencePointComputed :
                              source.aromaticCanonicalSpatialPointAt? rightReference with
                          | none =>
                              simp [leftReferenceComputed, rightReferenceComputed,
                                leftPointComputed, rightPointComputed,
                                rightReferencePointComputed] at computed
                          | some rightReferencePoint =>
                              cases geometryComputed : rule3GeometryOfSpatialReferences?
                                  leftPoint rightPoint leftReferencePoint rightReferencePoint with
                              | none =>
                                  simp [leftReferenceComputed, rightReferenceComputed,
                                    leftPointComputed, rightPointComputed,
                                    leftReferencePointComputed, rightReferencePointComputed,
                                    geometryComputed] at computed
                              | some geometry =>
                                  simp [leftReferenceComputed, rightReferenceComputed,
                                    leftPointComputed, rightPointComputed,
                                    leftReferencePointComputed, rightReferencePointComputed,
                                    geometryComputed] at computed
                                  subst result
                                  refine ⟨ordinary, ?_, ?_, leftPoint, rightPoint,
                                    leftReferencePoint, rightReferencePoint, ?_, ?_, ?_, ?_, ?_⟩
                                  · exact
                                      (source.aromaticCanonicalRule3ConstitutionalSeniorReference?_eq_some_iff_canonical
                                        left right leftReference).mp leftReferenceComputed
                                  · exact
                                      (source.aromaticCanonicalRule3ConstitutionalSeniorReference?_eq_some_iff_canonical
                                        right left rightReference).mp rightReferenceComputed
                                  · exact (source.aromaticCanonicalSpatialPointAt?_eq_some_iff
                                      left leftPoint).mp leftPointComputed
                                  · exact (source.aromaticCanonicalSpatialPointAt?_eq_some_iff
                                      right rightPoint).mp rightPointComputed
                                  · exact (source.aromaticCanonicalSpatialPointAt?_eq_some_iff
                                      leftReference leftReferencePoint).mp
                                        leftReferencePointComputed
                                  · exact (source.aromaticCanonicalSpatialPointAt?_eq_some_iff
                                      rightReference rightReferencePoint).mp
                                        rightReferencePointComputed
                                  · exact (rule3GeometryOfSpatialReferences?_eq_some_iff
                                      leftPoint rightPoint leftReferencePoint
                                        rightReferencePoint geometry).mp geometryComputed
    · simp [ordinary] at computed
  · rintro ⟨ordinary, leftReferenceDerived, rightReferenceDerived,
      leftPoint, rightPoint, leftReferencePoint, rightReferencePoint,
      leftPointDerived, rightPointDerived, leftReferencePointDerived,
      rightReferencePointDerived, geometryDerived⟩
    have leftReferenceComputed :=
      (source.aromaticCanonicalRule3ConstitutionalSeniorReference?_eq_some_iff_canonical
        left right result.leftReference).mpr leftReferenceDerived
    have rightReferenceComputed :=
      (source.aromaticCanonicalRule3ConstitutionalSeniorReference?_eq_some_iff_canonical
        right left result.rightReference).mpr rightReferenceDerived
    have leftPointComputed :=
      (source.aromaticCanonicalSpatialPointAt?_eq_some_iff
        left leftPoint).mpr leftPointDerived
    have rightPointComputed :=
      (source.aromaticCanonicalSpatialPointAt?_eq_some_iff
        right rightPoint).mpr rightPointDerived
    have leftReferencePointComputed :=
      (source.aromaticCanonicalSpatialPointAt?_eq_some_iff
        result.leftReference leftReferencePoint).mpr leftReferencePointDerived
    have rightReferencePointComputed :=
      (source.aromaticCanonicalSpatialPointAt?_eq_some_iff
        result.rightReference rightReferencePoint).mpr rightReferencePointDerived
    have geometryComputed :=
      (rule3GeometryOfSpatialReferences?_eq_some_iff
        leftPoint rightPoint leftReferencePoint rightReferencePoint
          result.geometry).mpr geometryDerived
    unfold aromaticCanonicalRule3SpatialUnit?
    simp [ordinary, leftReferenceComputed, rightReferenceComputed,
      leftPointComputed, rightPointComputed, leftReferencePointComputed,
      rightReferencePointComputed, geometryComputed]

/-- Canonical Rule-3 spatial-unit meaning refines the earlier broad declarative semantics. -/
theorem CanonicalAromaticCanonicalRule3SpatialUnit.sound
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalAtom)
    (result : source.AromaticCanonicalRule3SpatialUnitResult)
    (canonical : source.CanonicalAromaticCanonicalRule3SpatialUnit left right result) :
    source.DeclarativeAromaticCanonicalRule3SpatialUnit left right result := by
  exact source.aromaticCanonicalRule3SpatialUnit?_sound left right result
    ((source.aromaticCanonicalRule3SpatialUnit?_eq_some_iff_canonical
      left right result).mpr canonical)

/-- Spatial-unit refusal is exactly absence of a canonical positive derivation. -/
theorem aromaticCanonicalRule3SpatialUnit?_eq_none_iff_no_canonical
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalAtom) :
    source.aromaticCanonicalRule3SpatialUnit? left right = none ↔
      ¬ ∃ result, source.CanonicalAromaticCanonicalRule3SpatialUnit
        left right result := by
  cases computed : source.aromaticCanonicalRule3SpatialUnit? left right with
  | none =>
      simp only [true_iff]
      rintro ⟨result, derived⟩
      have positive :=
        (source.aromaticCanonicalRule3SpatialUnit?_eq_some_iff_canonical
          left right result).mpr derived
      rw [computed] at positive
      contradiction
  | some result =>
      simp only [reduceCtorEq, false_iff]
      intro absent
      exact absent ⟨result,
        (source.aromaticCanonicalRule3SpatialUnit?_eq_some_iff_canonical
          left right result).mp computed⟩

end AuthoritativeChemicalInput

end

end TetraStereo.OneCenter
