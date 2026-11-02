import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3Through6Backend

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# One source-canonical initial partition for Rule 6

This module compiles the four Rules-1a--5 root keys under the same physical-unit exclusion set
later consumed by the strengthened Rule-6 backend.  Its sort is total because the cumulative key
comparator is lawful; equality is retained as an equivalence class rather than treated as failure.
-/

structure AromaticCanonicalRule3Through5RootKeyFrame
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat) where
  rule3Frame : source.AromaticCanonicalRule3CanonicalKeyFrame
  rootsLength : Nat
  rootsLength_eq_four : rootsLength = 4
  keys : List source.AromaticCanonicalOccurrenceRule3Through5Key
  keysLength : keys.length = 4

def AromaticCanonicalRule3Through5RootKeyFrame.keyAt
    {source : AuthoritativeChemicalInput} {carrierFuel : Nat}
    (frame : source.AromaticCanonicalRule3Through5RootKeyFrame carrierFuel)
    (index : Fin 4) : source.AromaticCanonicalOccurrenceRule3Through5Key :=
  frame.keys.get (Fin.cast frame.keysLength.symm index)

noncomputable def buildAromaticCanonicalRule3Through5RootKeyFrame?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel)) :
    Option (source.AromaticCanonicalRule3Through5RootKeyFrame carrierFuel) := do
  if rootsLength : roots.length = 4 then
    let rule3Frame ← source.buildAromaticCanonicalRule3CanonicalKeyFrame? fuel roots
    let keys ← roots.mapM
      (source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?
        rule3Frame.excluded target view fuel)
    if keysLength : keys.length = 4 then
      some
        { rule3Frame
          rootsLength := roots.length
          rootsLength_eq_four := rootsLength
          keys
          keysLength }
    else none
  else none

def DeclarativeAromaticCanonicalRule3Through5RootKeyFrame
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (frame : source.AromaticCanonicalRule3Through5RootKeyFrame carrierFuel) : Prop :=
  roots.length = 4 ∧ frame.rootsLength = roots.length ∧
    source.DeclarativeAromaticCanonicalRule3CanonicalKeyFrame
      fuel roots frame.rule3Frame ∧
    List.Forall₂
      (source.DeclarativeAromaticCanonicalOccurrenceRule3Through5KeyExcept
        frame.rule3Frame.excluded target view fuel) roots frame.keys ∧
    frame.keys.length = 4

private theorem mapM_buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?_sound_for_rootFrame
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) :
    ∀ roots keys,
      roots.mapM (source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?
        excluded target view fuel) = some keys →
      List.Forall₂
        (source.DeclarativeAromaticCanonicalOccurrenceRule3Through5KeyExcept
          excluded target view fuel) roots keys
  | [], keys, computed => by
      simp at computed
      subst keys
      exact .nil
  | root :: roots, keys, computed => by
      rw [List.mapM_cons] at computed
      cases headComputed :
          source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?
            excluded target view fuel root with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : roots.mapM
              (source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?
                excluded target view fuel) with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst keys
              exact .cons
                (source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?_sound
                  excluded target view fuel root head headComputed)
                (mapM_buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?_sound_for_rootFrame
                  source excluded target view fuel roots tail tailComputed)

theorem buildAromaticCanonicalRule3Through5RootKeyFrame?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (frame : source.AromaticCanonicalRule3Through5RootKeyFrame carrierFuel)
    (computed : source.buildAromaticCanonicalRule3Through5RootKeyFrame?
      target view fuel roots = some frame) :
    source.DeclarativeAromaticCanonicalRule3Through5RootKeyFrame
      target view fuel roots frame := by
  unfold buildAromaticCanonicalRule3Through5RootKeyFrame? at computed
  by_cases rootsLength : roots.length = 4
  · cases rule3Computed : source.buildAromaticCanonicalRule3CanonicalKeyFrame?
        fuel roots with
    | none => simp [rootsLength, rule3Computed] at computed
    | some rule3Frame =>
        cases keysComputed : roots.mapM
            (source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?
              rule3Frame.excluded target view fuel) with
        | none => simp [rootsLength, rule3Computed, keysComputed] at computed
        | some keys =>
            by_cases keysLength : keys.length = 4
            · simp [rootsLength, rule3Computed, keysComputed, keysLength] at computed
              subst frame
              exact ⟨rootsLength, rootsLength.symm,
                source.buildAromaticCanonicalRule3CanonicalKeyFrame?_sound
                  fuel roots rule3Frame rule3Computed,
                mapM_buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?_sound_for_rootFrame
                  source rule3Frame.excluded target view fuel roots keys keysComputed,
                keysLength⟩
            · simp [rootsLength, rule3Computed, keysComputed, keysLength] at computed
  · simp [rootsLength] at computed

noncomputable def compareAromaticCanonicalRule3Through5RootPositions
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalRule3Through5RootKeyFrame carrierFuel)
    (left right : Fin 4) : Ordering :=
  source.compareAromaticCanonicalOccurrenceRule3Through5Keys
    (frame.keyAt left) (frame.keyAt right)

theorem compareAromaticCanonicalRule3Through5RootPositions_transCmp
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalRule3Through5RootKeyFrame carrierFuel) :
    Std.TransCmp (source.compareAromaticCanonicalRule3Through5RootPositions frame) := by
  letI : Std.TransCmp source.compareAromaticCanonicalOccurrenceRule3Through5Keys :=
    source.compareAromaticCanonicalOccurrenceRule3Through5Keys_transCmp
  change Std.TransCmp (Ordering.byKey frame.keyAt
    source.compareAromaticCanonicalOccurrenceRule3Through5Keys)
  infer_instance

def insertAromaticCanonicalRule3Through5RootPosition
    (compare : Fin 4 → Fin 4 → Ordering)
    (candidate : Fin 4) : List (Fin 4) → List (Fin 4)
  | [] => [candidate]
  | head :: tail =>
      match compare candidate head with
      | .lt => head :: insertAromaticCanonicalRule3Through5RootPosition
          compare candidate tail
      | .eq | .gt => candidate :: head :: tail

def sortAromaticCanonicalRule3Through5RootPositions
    (compare : Fin 4 → Fin 4 → Ordering) :
    List (Fin 4) → List (Fin 4)
  | [] => []
  | position :: positions =>
      insertAromaticCanonicalRule3Through5RootPosition compare position
        (sortAromaticCanonicalRule3Through5RootPositions compare positions)

theorem insertAromaticCanonicalRule3Through5RootPosition_perm
    (compare : Fin 4 → Fin 4 → Ordering) (candidate : Fin 4) :
    ∀ positions,
      (insertAromaticCanonicalRule3Through5RootPosition
        compare candidate positions).Perm (candidate :: positions)
  | [] => List.Perm.refl _
  | head :: tail => by
      unfold insertAromaticCanonicalRule3Through5RootPosition
      cases comparison : compare candidate head with
      | eq => exact List.Perm.refl _
      | gt => exact List.Perm.refl _
      | lt =>
          exact (List.Perm.cons head
            (insertAromaticCanonicalRule3Through5RootPosition_perm
              compare candidate tail)).trans
                (List.Perm.swap candidate head tail)

theorem sortAromaticCanonicalRule3Through5RootPositions_perm
    (compare : Fin 4 → Fin 4 → Ordering) :
    ∀ positions,
      (sortAromaticCanonicalRule3Through5RootPositions compare positions).Perm positions
  | [] => List.Perm.refl []
  | position :: positions =>
      (insertAromaticCanonicalRule3Through5RootPosition_perm compare position
        (sortAromaticCanonicalRule3Through5RootPositions compare positions)).trans
          (List.Perm.cons position
            (sortAromaticCanonicalRule3Through5RootPositions_perm compare positions))

def AromaticCanonicalRule3Through5RootPositionsDescending
    (compare : Fin 4 → Fin 4 → Ordering) (positions : List (Fin 4)) : Prop :=
  positions.Pairwise fun left right => compare left right ≠ Ordering.lt

theorem insertAromaticCanonicalRule3Through5RootPosition_descending
    (compare : Fin 4 → Fin 4 → Ordering) [Std.TransCmp compare]
    (candidate : Fin 4) :
    ∀ positions,
      AromaticCanonicalRule3Through5RootPositionsDescending compare positions →
      AromaticCanonicalRule3Through5RootPositionsDescending compare
        (insertAromaticCanonicalRule3Through5RootPosition compare candidate positions)
  | [], _ => by
      simp [insertAromaticCanonicalRule3Through5RootPosition,
        AromaticCanonicalRule3Through5RootPositionsDescending]
  | head :: tail, sorted => by
      have headOverTail : ∀ observed ∈ tail,
          compare head observed ≠ Ordering.lt := (List.pairwise_cons.mp sorted).1
      have tailSorted :
          AromaticCanonicalRule3Through5RootPositionsDescending compare tail :=
        (List.pairwise_cons.mp sorted).2
      unfold insertAromaticCanonicalRule3Through5RootPosition
      cases comparison : compare candidate head with
      | gt =>
          rw [AromaticCanonicalRule3Through5RootPositionsDescending, List.pairwise_cons]
          constructor
          · intro observed present
            rcases List.mem_cons.mp present with rfl | tailPresent
            · simp [comparison]
            · exact Std.TransCmp.ge_trans (by simp [comparison])
                (headOverTail observed tailPresent)
          · exact sorted
      | eq =>
          rw [AromaticCanonicalRule3Through5RootPositionsDescending, List.pairwise_cons]
          constructor
          · intro observed present
            rcases List.mem_cons.mp present with rfl | tailPresent
            · simp [comparison]
            · exact Std.TransCmp.ge_trans (by simp [comparison])
                (headOverTail observed tailPresent)
          · exact sorted
      | lt =>
          have insertedSorted :=
            insertAromaticCanonicalRule3Through5RootPosition_descending
              compare candidate tail tailSorted
          rw [AromaticCanonicalRule3Through5RootPositionsDescending, List.pairwise_cons]
          constructor
          · intro observed present
            have permutation :=
              insertAromaticCanonicalRule3Through5RootPosition_perm
                compare candidate tail
            have sourcePresent : observed ∈ candidate :: tail :=
              (permutation.mem_iff).mp present
            rcases List.mem_cons.mp sourcePresent with same | tailPresent
            · subst observed
              have reverse : compare head candidate = Ordering.gt := by
                rw [Std.OrientedCmp.gt_iff_lt]
                exact comparison
              simp [reverse]
            · exact headOverTail observed tailPresent
          · exact insertedSorted

theorem sortAromaticCanonicalRule3Through5RootPositions_descending
    (compare : Fin 4 → Fin 4 → Ordering) [Std.TransCmp compare] :
    ∀ positions,
      AromaticCanonicalRule3Through5RootPositionsDescending compare
        (sortAromaticCanonicalRule3Through5RootPositions compare positions)
  | [] => by
      simp [sortAromaticCanonicalRule3Through5RootPositions,
        AromaticCanonicalRule3Through5RootPositionsDescending]
  | position :: positions =>
      insertAromaticCanonicalRule3Through5RootPosition_descending
        compare position
        (sortAromaticCanonicalRule3Through5RootPositions compare positions)
        (sortAromaticCanonicalRule3Through5RootPositions_descending compare positions)

def aromaticCanonicalRule3Through5RootAdjacent
    (compare : Fin 4 → Fin 4 → Ordering) :
    List (Fin 4) → List Ordering
  | [] | [_] => []
  | left :: right :: remaining =>
      compare left right ::
        aromaticCanonicalRule3Through5RootAdjacent compare (right :: remaining)

theorem aromaticCanonicalRule3Through5RootAdjacent_length
    (compare : Fin 4 → Fin 4 → Ordering) :
    ∀ positions,
      (aromaticCanonicalRule3Through5RootAdjacent compare positions).length =
        positions.length - 1
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: remaining => by
      simp [aromaticCanonicalRule3Through5RootAdjacent,
        aromaticCanonicalRule3Through5RootAdjacent_length compare (_ :: remaining)]

theorem aromaticCanonicalRule3Through5RootAdjacent_ne_lt_of_descending
    (compare : Fin 4 → Fin 4 → Ordering) :
    ∀ positions,
      AromaticCanonicalRule3Through5RootPositionsDescending compare positions →
      Ordering.lt ∉ aromaticCanonicalRule3Through5RootAdjacent compare positions
  | [], _ => by simp [aromaticCanonicalRule3Through5RootAdjacent]
  | [_], _ => by simp [aromaticCanonicalRule3Through5RootAdjacent]
  | left :: right :: remaining, descending => by
      have headNe : compare left right ≠ Ordering.lt :=
        (List.pairwise_cons.mp descending).1 right (by simp)
      have headNotMember : ¬ Ordering.lt = compare left right := by
        intro equal
        exact headNe equal.symm
      have tailDescending :
          AromaticCanonicalRule3Through5RootPositionsDescending
            compare (right :: remaining) :=
        (List.pairwise_cons.mp descending).2
      simp [aromaticCanonicalRule3Through5RootAdjacent, headNotMember,
        aromaticCanonicalRule3Through5RootAdjacent_ne_lt_of_descending
          compare (right :: remaining) tailDescending]

structure AromaticCanonicalRule3Through5InitialPartition
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat) where
  frame : source.AromaticCanonicalRule3Through5RootKeyFrame carrierFuel
  sorted : List (Fin 4)
  adjacent : List Ordering

noncomputable def buildAromaticCanonicalRule3Through5InitialPartition?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel)) :
    Option (source.AromaticCanonicalRule3Through5InitialPartition carrierFuel) := do
  let frame ← source.buildAromaticCanonicalRule3Through5RootKeyFrame?
    target view fuel roots
  let compare := source.compareAromaticCanonicalRule3Through5RootPositions frame
  let sorted := sortAromaticCanonicalRule3Through5RootPositions compare (List.finRange 4)
  let adjacent := aromaticCanonicalRule3Through5RootAdjacent compare sorted
  some { frame, sorted, adjacent }

def DeclarativeAromaticCanonicalRule3Through5InitialPartition
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (partition : source.AromaticCanonicalRule3Through5InitialPartition carrierFuel) : Prop :=
  source.DeclarativeAromaticCanonicalRule3Through5RootKeyFrame
      target view fuel roots partition.frame ∧
    partition.sorted.Perm (List.finRange 4) ∧
    AromaticCanonicalRule3Through5RootPositionsDescending
      (source.compareAromaticCanonicalRule3Through5RootPositions partition.frame)
      partition.sorted ∧
    partition.adjacent = aromaticCanonicalRule3Through5RootAdjacent
      (source.compareAromaticCanonicalRule3Through5RootPositions partition.frame)
      partition.sorted

theorem buildAromaticCanonicalRule3Through5InitialPartition?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (partition : source.AromaticCanonicalRule3Through5InitialPartition carrierFuel)
    (computed : source.buildAromaticCanonicalRule3Through5InitialPartition?
      target view fuel roots = some partition) :
    source.DeclarativeAromaticCanonicalRule3Through5InitialPartition
      target view fuel roots partition := by
  unfold buildAromaticCanonicalRule3Through5InitialPartition? at computed
  cases frameComputed : source.buildAromaticCanonicalRule3Through5RootKeyFrame?
      target view fuel roots with
  | none => simp [frameComputed] at computed
  | some frame =>
      simp [frameComputed] at computed
      subst partition
      let compare := source.compareAromaticCanonicalRule3Through5RootPositions frame
      letI : Std.TransCmp compare :=
        source.compareAromaticCanonicalRule3Through5RootPositions_transCmp frame
      exact ⟨
        source.buildAromaticCanonicalRule3Through5RootKeyFrame?_sound
          target view fuel roots frame frameComputed,
        sortAromaticCanonicalRule3Through5RootPositions_perm compare (List.finRange 4),
        sortAromaticCanonicalRule3Through5RootPositions_descending
          compare (List.finRange 4),
        rfl⟩

def AromaticCanonicalRule3Through5InitialPartition.sortedPositions
    {source : AuthoritativeChemicalInput} {carrierFuel : Nat}
    (partition : source.AromaticCanonicalRule3Through5InitialPartition carrierFuel) :
    List Nat := partition.sorted.map Fin.val

def AromaticCanonicalRule3Through5InitialPartition.adjacentOptions
    {source : AuthoritativeChemicalInput} {carrierFuel : Nat}
    (partition : source.AromaticCanonicalRule3Through5InitialPartition carrierFuel) :
    List (Option Ordering) := partition.adjacent.map some

theorem DeclarativeAromaticCanonicalRule3Through5InitialPartition.sortedPositions_perm
    {source : AuthoritativeChemicalInput} {carrierFuel fuel : Nat}
    {target : source.AromaticCanonicalOccurrence carrierFuel}
    {view : source.AromaticCanonicalDependencyView target}
    {roots : List (source.AromaticCanonicalRerootCursor carrierFuel)}
    {partition : source.AromaticCanonicalRule3Through5InitialPartition carrierFuel}
    (derived : source.DeclarativeAromaticCanonicalRule3Through5InitialPartition
      target view fuel roots partition) :
    partition.sortedPositions.Perm (List.range 4) := by
  have mapped := derived.2.1.map Fin.val
  simpa [AromaticCanonicalRule3Through5InitialPartition.sortedPositions,
    List.finRange] using mapped

theorem DeclarativeAromaticCanonicalRule3Through5InitialPartition.adjacent_length
    {source : AuthoritativeChemicalInput} {carrierFuel fuel : Nat}
    {target : source.AromaticCanonicalOccurrence carrierFuel}
    {view : source.AromaticCanonicalDependencyView target}
    {roots : List (source.AromaticCanonicalRerootCursor carrierFuel)}
    {partition : source.AromaticCanonicalRule3Through5InitialPartition carrierFuel}
    (derived : source.DeclarativeAromaticCanonicalRule3Through5InitialPartition
      target view fuel roots partition) :
    partition.adjacent.length = 3 := by
  rw [derived.2.2.2,
    aromaticCanonicalRule3Through5RootAdjacent_length]
  have sortedLength := derived.2.1.length_eq
  simpa using sortedLength

theorem DeclarativeAromaticCanonicalRule3Through5InitialPartition.adjacent_ne_lt
    {source : AuthoritativeChemicalInput} {carrierFuel fuel : Nat}
    {target : source.AromaticCanonicalOccurrence carrierFuel}
    {view : source.AromaticCanonicalDependencyView target}
    {roots : List (source.AromaticCanonicalRerootCursor carrierFuel)}
    {partition : source.AromaticCanonicalRule3Through5InitialPartition carrierFuel}
    (derived : source.DeclarativeAromaticCanonicalRule3Through5InitialPartition
      target view fuel roots partition) :
    Ordering.lt ∉ partition.adjacent := by
  rw [derived.2.2.2]
  exact aromaticCanonicalRule3Through5RootAdjacent_ne_lt_of_descending
    _ partition.sorted derived.2.2.1

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
