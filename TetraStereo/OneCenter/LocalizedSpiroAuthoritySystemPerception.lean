import TetraStereo.OneCenter.LocalizedSpiroCenterPerception
import TetraStereo.OneCenter.LocalizedSimpleCycleOrderedWitness
import TetraStereo.OneCenter.IUPACP93SpiroAuthorityCarrier
import TetraStereo.OneCenter.OrganicStereoCyclicCarrierTransport
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

/-!
# Automatic structural spiro authority-system inventory

`LocalizedSpiroCenterPerception` recognizes the graph-theoretic two-simple-cycle spiro topology and
returns the complete unordered pair of rings through a center.  The P-93 authority carrier
`P93AuthoritySpiroSystem` instead consumes an ordered pair of internal ring traversals over the raw
semantic source indices.  This module connects those two layers:

* `localizedAdj_iff_p93AuthorityBinaryBond` proves that, on the exact localized closed-shell input
  domain, positive `MoleculeGraph` adjacency is the raw-source `P93AuthorityBinaryBond` relation.
  The two sides are *not* assumed to agree: the equation is derived from the definitional graph
  construction `SemanticMolecule.toLocalizedMoleculeGraph`, the record extraction
  `SemanticMolecule.localizedCovalentRecords`, and the `LocalizedCovalentPairsOnly` clause of
  `graphReady`.
* `LocalizedSpiroAuthoritySystemMatches` records the exact relation between a perceived carrier and
  a produced authority system: same center, and the same two physical ring vertex sets.
* `localizedSpiroAuthoritySystemAt?` turns one perceived center into the authority system, obtaining
  each internal traversal from the dependency selector `localizedSimpleCycleInternalPath?` and
  mapping atoms through `Fin.val`.  It is deliberately noncomputable: center perception itself uses
  classical reachability, and `Finset.toList` is an implementation-chosen enumeration, not a
  numerical or stereochemical orientation.
* `localizedSpiroAuthoritySystemAt?_complete` constructs a system for *every* perceived carrier and
  proves it mechanically valid for the actual certified source and matching that carrier, with no
  ordered ring list, path validity or output-success hypothesis.
* `localizedSpiroAuthoritySystemAt?_sound` conversely derives a perceived carrier, mechanical
  validity and matching from any successful output.
* `localizedSpiroAuthoritySystems` inventories every perceived spiro center of the input; every
  inventoried system is mechanically valid for the actual source, and the number of systems centered
  on an atom is one exactly when the declarative two-ring predicate holds there.

Scope: exactly the simple two-induced-cycle spiro topology on `CertifiedLocalizedCIPInput`.  Nothing
here claims descriptor assignment, ligand-pattern ranking (`Xabcd`/`Xabab`/`Xaabb`), geometry, or
completeness for general polycyclic / P-93 spiro chemistry.
-/

/-! ## Raw-source binary bonds from graph adjacency

The bridge is derived, not postulated.  Forward: a positive graph bond is a positive order in
`localizedCovalentRecords`, which by `List.mem_filterMap` comes from an actual source interaction.
On a graph-ready molecule that interaction is a positive localized covalent pair, so its extracted
record is determined and must agree with the observed one.  Reverse: every `P93AuthorityBinaryBond`
witness is again a positive localized covalent pair, hence contributes its record. -/

/-- Unordered edge keys determine the endpoint pair up to orientation. -/
theorem semanticEdgeKey_eq_endpoints {left right first second : ℕ}
    (same : semanticEdgeKey left right = semanticEdgeKey first second) :
    (left = first ∧ right = second) ∨ (left = second ∧ right = first) := by
  simp only [semanticEdgeKey, Prod.mk.injEq] at same
  obtain ⟨minSame, maxSame⟩ := same
  rcases le_total left right with ordered | ordered
  · have leftEq : left = min first second := (min_eq_left ordered).symm.trans minSame
    have rightEq : right = max first second := (max_eq_right ordered).symm.trans maxSame
    rcases le_total first second with forward | backward
    · exact Or.inl ⟨leftEq.trans (min_eq_left forward),
        rightEq.trans (max_eq_right forward)⟩
    · exact Or.inr ⟨leftEq.trans (min_eq_right backward),
        rightEq.trans (max_eq_left backward)⟩
  · have leftEq : left = max first second := (max_eq_left ordered).symm.trans maxSame
    have rightEq : right = min first second := (min_eq_right ordered).symm.trans minSame
    rcases le_total first second with forward | backward
    · exact Or.inr ⟨leftEq.trans (max_eq_right forward),
        rightEq.trans (min_eq_left forward)⟩
    · exact Or.inl ⟨leftEq.trans (max_eq_left backward),
        rightEq.trans (min_eq_right backward)⟩

/-- A positive localized covalent pair is extracted at exactly its own record. -/
theorem localizedCovalentRecord?_eq_some_of_pair
    (interaction : SemanticInteraction) {first second order : ℕ}
    (participants : interaction.participants = [first, second])
    (kind : interaction.kind = .covalent order)
    (positive : 0 < order) :
    interaction.localizedCovalentRecord? = some (semanticEdgeKey first second, order) := by
  obtain ⟨actualParticipants, actualKind⟩ := interaction
  dsimp only at participants kind
  subst actualParticipants
  subst actualKind
  simp [SemanticInteraction.localizedCovalentRecord?, positive]

/-- **Exact source bridge.**  On a certified localized input, the positive constitutional graph
edge relation is the raw semantic-source binary bond relation on the same atom indices.  Both
directions are derived from the actual source interactions; no graph/source agreement is assumed. -/
theorem localizedAdj_iff_p93AuthorityBinaryBond
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom) :
    input.moleculeGraph.Adj left right ↔
      P93AuthorityBinaryBond input.certified.input left.val right.val := by
  constructor
  · intro adjacent
    have distinct : left ≠ right := by
      intro sameValue
      rw [sameValue, MoleculeGraph.Adj, input.moleculeGraph.bond_self] at adjacent
      exact Nat.lt_irrefl 0 adjacent
    obtain ⟨order, present, _⟩ :=
      (input.certified.input.molecule.toLocalizedMoleculeGraph_adj_iff_record
        input.graphReady left right distinct).mp adjacent
    rw [SemanticMolecule.localizedCovalentRecords, List.mem_filterMap] at present
    obtain ⟨interaction, interactionMem, extracted⟩ := present
    obtain ⟨first, second, pairOrder, participantsEq, kindEq, pairPositive⟩ :=
      input.graphReady.2.2.2.1 interaction interactionMem
    rw [localizedCovalentRecord?_eq_some_of_pair interaction participantsEq kindEq
      pairPositive] at extracted
    simp only [Option.some.injEq, Prod.mk.injEq] at extracted
    obtain ⟨keyEq, _⟩ := extracted
    refine ⟨?_, interaction, interactionMem, ?_, ?_⟩
    · exact fun sameValue => distinct (Fin.ext sameValue)
    · rw [kindEq]
      exact trivial
    · rcases semanticEdgeKey_eq_endpoints keyEq with aligned | flipped
      · obtain ⟨firstEq, secondEq⟩ := aligned
        rw [participantsEq, firstEq, secondEq]
        exact Or.inl rfl
      · obtain ⟨firstEq, secondEq⟩ := flipped
        rw [participantsEq, firstEq, secondEq]
        exact Or.inr rfl
  · rintro ⟨distinctValues, interaction, interactionMem, _, participants⟩
    have distinct : left ≠ right := fun sameValue => distinctValues (congrArg Fin.val sameValue)
    obtain ⟨first, second, order, participantsEq, kindEq, positive⟩ :=
      input.graphReady.2.2.2.1 interaction interactionMem
    have keyEq : semanticEdgeKey first second = semanticEdgeKey left.val right.val := by
      rcases participants with forward | backward
      · have combined : [first, second] = [left.val, right.val] :=
          participantsEq.symm.trans forward
        simp at combined
        obtain ⟨firstEq, secondEq⟩ := combined
        rw [firstEq, secondEq]
      · have combined : [first, second] = [right.val, left.val] :=
          participantsEq.symm.trans backward
        simp at combined
        obtain ⟨firstEq, secondEq⟩ := combined
        rw [firstEq, secondEq, semanticEdgeKey_comm]
    have extracted : interaction.localizedCovalentRecord? =
        some (semanticEdgeKey left.val right.val, order) := by
      rw [localizedCovalentRecord?_eq_some_of_pair interaction participantsEq kindEq positive,
        keyEq]
    refine (input.certified.input.molecule.toLocalizedMoleculeGraph_adj_iff_record
      input.graphReady left right distinct).mpr ⟨order, ?_, positive⟩
    rw [SemanticMolecule.localizedCovalentRecords, List.mem_filterMap]
    exact ⟨interaction, interactionMem, extracted⟩

/-! ## Carrier/system correspondence -/

/-- A produced authority system describes exactly one perceived spiro carrier: it is centered on the
same atom and its two closed rings are exactly the two physical ring vertex sets of the carrier,
read through the atom embedding `Fin.val`. -/
def LocalizedSpiroAuthoritySystemMatches
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (carrier : input.LocalizedSpiroCenter center) (system : P93AuthoritySpiroSystem) : Prop :=
  system.center = center.val ∧
    {system.firstRing.toFinset, system.secondRing.toFinset} =
      carrier.rings.image (fun ring => ring.image Fin.val)

theorem LocalizedSpiroAuthoritySystemMatches.center_eq
    {input : CertifiedLocalizedCIPInput} {center : input.Atom}
    {carrier : input.LocalizedSpiroCenter center} {system : P93AuthoritySpiroSystem}
    (matched : input.LocalizedSpiroAuthoritySystemMatches center carrier system) :
    system.center = center.val := matched.1

theorem LocalizedSpiroAuthoritySystemMatches.rings_eq
    {input : CertifiedLocalizedCIPInput} {center : input.Atom}
    {carrier : input.LocalizedSpiroCenter center} {system : P93AuthoritySpiroSystem}
    (matched : input.LocalizedSpiroAuthoritySystemMatches center carrier system) :
    {system.firstRing.toFinset, system.secondRing.toFinset} =
      carrier.rings.image (fun ring => ring.image Fin.val) := matched.2

/-! ## Assembling an authority system from a perceived ring pair -/

/-- The authority system assembled from one perceived center and the ordered internal traversals of
its two rings.  Ring atoms are read through the embedding `Fin.val`, so the resulting system lives
on the raw source atom indices consumed by the P-93 spiro carrier. -/
def localizedSpiroAuthoritySystemOf
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (firstInternal secondInternal : List input.Atom) : P93AuthoritySpiroSystem where
  center := center.val
  firstRingInternal := firstInternal.map Fin.val
  secondRingInternal := secondInternal.map Fin.val

@[simp] theorem localizedSpiroAuthoritySystemOf_center
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (firstInternal secondInternal : List input.Atom) :
    (localizedSpiroAuthoritySystemOf input center firstInternal secondInternal).center =
      center.val := rfl

@[simp] theorem localizedSpiroAuthoritySystemOf_firstInternal
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (firstInternal secondInternal : List input.Atom) :
    (localizedSpiroAuthoritySystemOf input center firstInternal secondInternal).firstRingInternal =
      firstInternal.map Fin.val := rfl

@[simp] theorem localizedSpiroAuthoritySystemOf_secondInternal
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (firstInternal secondInternal : List input.Atom) :
    (localizedSpiroAuthoritySystemOf input center firstInternal secondInternal).secondRingInternal =
      secondInternal.map Fin.val := rfl

/-- The atom embedding `Fin.val` commutes with finite-set extraction. -/
theorem list_toFinset_map_val (input : CertifiedLocalizedCIPInput) (atoms : List input.Atom) :
    (atoms.map Fin.val).toFinset = atoms.toFinset.image Fin.val := by
  ext atom
  simp

/-- A closed ring list extracts to the image of its vertex set. -/
theorem toFinset_cons_map_val (input : CertifiedLocalizedCIPInput)
    (center : input.Atom) (internal : List input.Atom) :
    (center.val :: internal.map Fin.val).toFinset =
      (center :: internal).toFinset.image Fin.val := by
  rw [List.toFinset_cons, list_toFinset_map_val, List.toFinset_cons, Finset.image_insert]

/-- **Mechanical validity of the assembled system, derived from the perceived ring pair.**  The two
dependency traversals supply the two closed adjacency chains, the ring intersection condition of the
perceived carrier supplies the shared-center-only intersection, and `Fin.val` is injective, so the
combined atom list is duplicate-free and bounded.  No path, ordering or validity hypothesis is
supplied by the caller. -/
theorem mechanicallyValidFor_localizedSpiroAuthoritySystemOf
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedSpiroCenter center carrier)
    (first second : Finset input.Atom)
    (ringsEq : carrier.rings = {first, second})
    (firstInternal secondInternal : List input.Atom)
    (firstSpec : input.LocalizedSimpleCycleInternalPathSpec first center firstInternal)
    (secondSpec : input.LocalizedSimpleCycleInternalPathSpec second center secondInternal) :
    (localizedSpiroAuthoritySystemOf input center firstInternal secondInternal).MechanicallyValidFor
      input.certified.input := by
  classical
  have different : first ≠ second := by
    rintro rfl
    have cardOne : carrier.rings.card = 1 := by
      rw [ringsEq]
      simp
    have cardTwo : carrier.rings.card = 2 := judged.2.1
    omega
  have firstMember : first ∈ carrier.rings := by
    rw [ringsEq]
    simp
  have secondMember : second ∈ carrier.rings := by
    rw [ringsEq]
    simp
  have intersection : first ∩ second = {center} :=
    judged.2.2 first firstMember second secondMember different
  have centerNotFirst : center ∉ firstInternal := (List.nodup_cons.mp firstSpec.1).1
  have firstNodup : firstInternal.Nodup := (List.nodup_cons.mp firstSpec.1).2
  have centerNotSecond : center ∉ secondInternal := (List.nodup_cons.mp secondSpec.1).1
  have secondNodup : secondInternal.Nodup := (List.nodup_cons.mp secondSpec.1).2
  have firstMembership : ∀ atom, atom ∈ firstInternal → atom ∈ first := by
    intro atom member
    rw [← firstSpec.2.1, List.mem_toFinset]
    exact List.mem_cons_of_mem center member
  have secondMembership : ∀ atom, atom ∈ secondInternal → atom ∈ second := by
    intro atom member
    rw [← secondSpec.2.1, List.mem_toFinset]
    exact List.mem_cons_of_mem center member
  have disjointInternal : ∀ atom, atom ∈ firstInternal → atom ∈ secondInternal → False := by
    intro atom inFirst inSecond
    have both : atom ∈ first ∩ second :=
      Finset.mem_inter.mpr ⟨firstMembership atom inFirst, secondMembership atom inSecond⟩
    rw [intersection, Finset.mem_singleton] at both
    exact centerNotFirst (both ▸ inFirst)
  have disjointMapped : List.Disjoint (firstInternal.map Fin.val) (secondInternal.map Fin.val) := by
    intro atom inFirstMapped inSecondMapped
    rw [List.mem_map] at inFirstMapped inSecondMapped
    obtain ⟨firstAtom, firstAtomMember, firstAtomEq⟩ := inFirstMapped
    obtain ⟨secondAtom, secondAtomMember, secondAtomEq⟩ := inSecondMapped
    have atomEq : secondAtom = firstAtom := Fin.ext (secondAtomEq.trans firstAtomEq.symm)
    exact disjointInternal firstAtom firstAtomMember (atomEq ▸ secondAtomMember)
  have mappedFirstNodup : (firstInternal.map Fin.val).Nodup :=
    firstNodup.map (fun left right same => Fin.ext same)
  have mappedSecondNodup : (secondInternal.map Fin.val).Nodup :=
    secondNodup.map (fun left right same => Fin.ext same)
  have appendNodup : (firstInternal.map Fin.val ++ secondInternal.map Fin.val).Nodup :=
    List.Nodup.append mappedFirstNodup mappedSecondNodup disjointMapped
  have centerNotMappedFirst : center.val ∉ firstInternal.map Fin.val := by
    intro member
    rw [List.mem_map] at member
    obtain ⟨atom, atomMember, atomEq⟩ := member
    exact centerNotFirst (Fin.ext atomEq ▸ atomMember)
  have centerNotMappedSecond : center.val ∉ secondInternal.map Fin.val := by
    intro member
    rw [List.mem_map] at member
    obtain ⟨atom, atomMember, atomEq⟩ := member
    exact centerNotSecond (Fin.ext atomEq ▸ atomMember)
  have nodupAtoms :
      (center.val :: (firstInternal.map Fin.val ++ secondInternal.map Fin.val)).Nodup := by
    rw [List.nodup_cons]
    refine ⟨?_, appendNodup⟩
    intro member
    rcases List.mem_append.mp member with inFirst | inSecond
    · exact centerNotMappedFirst inFirst
    · exact centerNotMappedSecond inSecond
  have bounded : P93AuthorityAtomsBounded input.certified.input
      (center.val :: (firstInternal.map Fin.val ++ secondInternal.map Fin.val)) := by
    intro atom member
    simp only [List.mem_cons, List.mem_append, List.mem_map] at member
    rcases member with same | ⟨inner, _, same⟩ | ⟨inner, _, same⟩
    · rw [same]
      exact center.isLt
    · rw [← same]
      exact inner.isLt
    · rw [← same]
      exact inner.isLt
  have firstChain : P93AuthorityConnectedPath input.certified.input
      (center.val :: (firstInternal.map Fin.val ++ [center.val])) := by
    refine (P93AuthorityConnectedPath.isChain_iff input.certified.input _).mpr ?_
    have transported :
        ((((center :: firstInternal) ++ [center]).map Fin.val)).IsChain
          (P93AuthorityBinaryBond input.certified.input) :=
      List.isChain_map_of_isChain Fin.val
        (fun left right adjacent =>
          (localizedAdj_iff_p93AuthorityBinaryBond input left right).mp adjacent)
        firstSpec.2.2.2
    simpa [List.map_append] using transported
  have secondChain : P93AuthorityConnectedPath input.certified.input
      (center.val :: (secondInternal.map Fin.val ++ [center.val])) := by
    refine (P93AuthorityConnectedPath.isChain_iff input.certified.input _).mpr ?_
    have transported :
        ((((center :: secondInternal) ++ [center]).map Fin.val)).IsChain
          (P93AuthorityBinaryBond input.certified.input) :=
      List.isChain_map_of_isChain Fin.val
        (fun left right adjacent =>
          (localizedAdj_iff_p93AuthorityBinaryBond input left right).mp adjacent)
        secondSpec.2.2.2
    simpa [List.map_append] using transported
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (center.val :: (firstInternal.map Fin.val ++ secondInternal.map Fin.val)).Nodup
    exact nodupAtoms
  · show P93AuthorityAtomsBounded input.certified.input
      (center.val :: (firstInternal.map Fin.val ++ secondInternal.map Fin.val))
    exact bounded
  · show 2 ≤ (firstInternal.map Fin.val).length
    rw [List.length_map]
    exact firstSpec.2.2.1
  · show 2 ≤ (secondInternal.map Fin.val).length
    rw [List.length_map]
    exact secondSpec.2.2.1
  · show P93AuthorityConnectedPath input.certified.input
      (center.val :: (firstInternal.map Fin.val ++ [center.val]))
    exact firstChain
  · show P93AuthorityConnectedPath input.certified.input
      (center.val :: (secondInternal.map Fin.val ++ [center.val]))
    exact secondChain

/-- The assembled system matches the carrier it was built from: same center and the same two
physical ring vertex sets. -/
theorem localizedSpiroAuthoritySystemMatches_of_specs
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (carrier : input.LocalizedSpiroCenter center)
    (first second : Finset input.Atom)
    (ringsEq : carrier.rings = {first, second})
    (firstInternal secondInternal : List input.Atom)
    (firstSpec : input.LocalizedSimpleCycleInternalPathSpec first center firstInternal)
    (secondSpec : input.LocalizedSimpleCycleInternalPathSpec second center secondInternal) :
    input.LocalizedSpiroAuthoritySystemMatches center carrier
      (localizedSpiroAuthoritySystemOf input center firstInternal secondInternal) := by
  constructor
  · exact localizedSpiroAuthoritySystemOf_center input center firstInternal secondInternal
  · have firstToFinset : (center.val :: firstInternal.map Fin.val).toFinset =
        first.image Fin.val := by
      rw [toFinset_cons_map_val, firstSpec.2.1]
    have secondToFinset : (center.val :: secondInternal.map Fin.val).toFinset =
        second.image Fin.val := by
      rw [toFinset_cons_map_val, secondSpec.2.1]
    simp only [P93AuthoritySpiroSystem.firstRing, P93AuthoritySpiroSystem.secondRing,
      localizedSpiroAuthoritySystemOf_center, localizedSpiroAuthoritySystemOf_firstInternal,
      localizedSpiroAuthoritySystemOf_secondInternal]
    rw [firstToFinset, secondToFinset, ringsEq]
    simp

/-! ## Executable selection from perceived rings -/

/-- The authority system obtained from two concrete rings and the dependency selector.  Both
selectors must succeed; otherwise the result is `none`.  This is a bookkeeping device around the
dependency's executable path selector. -/
noncomputable def localizedSpiroAuthoritySystemForRings?
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (firstRing secondRing : Finset input.Atom) : Option P93AuthoritySpiroSystem :=
  (input.localizedSimpleCycleInternalPath? firstRing center).bind fun firstInternal =>
    (input.localizedSimpleCycleInternalPath? secondRing center).bind fun secondInternal =>
      some (localizedSpiroAuthoritySystemOf input center firstInternal secondInternal)

theorem localizedSpiroAuthoritySystemForRings?_eq_some_iff
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (firstRing secondRing : Finset input.Atom) (system : P93AuthoritySpiroSystem) :
    input.localizedSpiroAuthoritySystemForRings? center firstRing secondRing = some system ↔
      ∃ firstInternal secondInternal,
        input.localizedSimpleCycleInternalPath? firstRing center = some firstInternal ∧
          input.localizedSimpleCycleInternalPath? secondRing center = some secondInternal ∧
            system =
              localizedSpiroAuthoritySystemOf input center firstInternal secondInternal := by
  unfold localizedSpiroAuthoritySystemForRings?
  rw [Option.bind_eq_some_iff]
  constructor
  · rintro ⟨firstInternal, firstComputed, rest⟩
    rw [Option.bind_eq_some_iff] at rest
    obtain ⟨secondInternal, secondComputed, outcome⟩ := rest
    simp only [Option.some.injEq] at outcome
    exact ⟨firstInternal, secondInternal, firstComputed, secondComputed, outcome.symm⟩
  · rintro ⟨firstInternal, secondInternal, firstComputed, secondComputed, same⟩
    refine ⟨firstInternal, firstComputed, ?_⟩
    rw [Option.bind_eq_some_iff]
    exact ⟨secondInternal, secondComputed, by simpa using same.symm⟩

/-- Ordered authority system for one already-perceived carrier.  The two rings are read off the
`Finset.toList` enumeration, an implementation-chosen order carrying no atom-index or
stereochemical meaning; nothing else is assumed about the rings. -/
noncomputable def localizedSpiroAuthoritySystemForCarrier?
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (carrier : input.LocalizedSpiroCenter center) : Option P93AuthoritySpiroSystem :=
  match carrier.rings.toList with
  | [firstRing, secondRing] =>
      input.localizedSpiroAuthoritySystemForRings? center firstRing secondRing
  | _ => none

theorem localizedSpiroAuthoritySystemForCarrier?_eq_some_iff
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (carrier : input.LocalizedSpiroCenter center) (system : P93AuthoritySpiroSystem) :
    input.localizedSpiroAuthoritySystemForCarrier? center carrier = some system ↔
      ∃ firstRing secondRing,
        carrier.rings.toList = [firstRing, secondRing] ∧
          input.localizedSpiroAuthoritySystemForRings? center firstRing secondRing =
            some system := by
  unfold localizedSpiroAuthoritySystemForCarrier?
  cases hlist : carrier.rings.toList with
  | nil => simp
  | cons headRing rest =>
      cases rest with
      | nil => simp
      | cons tailRing remaining =>
          cases remaining with
          | cons third rest' => simp
          | nil =>
              constructor
              · intro computed
                exact ⟨headRing, tailRing, rfl, computed⟩
              · rintro ⟨firstRing, secondRing, pairEq, computed⟩
                have pairSplit : headRing = firstRing ∧ tailRing = secondRing := by
                  simpa using pairEq
                obtain ⟨headEq, tailEq⟩ := pairSplit
                rw [headEq, tailEq]
                exact computed

/-- Automatic authority system at one atom.  Center perception itself uses classical reachability;
the two ring traversals are then selected by the dependency's executable path selector.  The result
is `none` exactly when perception fails or a selector fails. -/
noncomputable def localizedSpiroAuthoritySystemAt?
    (input : CertifiedLocalizedCIPInput) (center : input.Atom) :
    Option P93AuthoritySpiroSystem :=
  match input.localizedSpiroCenterAt? center with
  | none => none
  | some carrier => input.localizedSpiroAuthoritySystemForCarrier? center carrier

theorem localizedSpiroAuthoritySystemAt?_eq_some_iff
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (system : P93AuthoritySpiroSystem) :
    input.localizedSpiroAuthoritySystemAt? center = some system ↔
      ∃ carrier,
        input.localizedSpiroCenterAt? center = some carrier ∧
          input.localizedSpiroAuthoritySystemForCarrier? center carrier = some system := by
  unfold localizedSpiroAuthoritySystemAt?
  cases hcenter : input.localizedSpiroCenterAt? center with
  | none => simp
  | some carrier => simp

/-- Every produced system is centered on the atom it was requested for. -/
theorem localizedSpiroAuthoritySystemAt?_center_eq
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (system : P93AuthoritySpiroSystem)
    (computed : input.localizedSpiroAuthoritySystemAt? center = some system) :
    system.center = center.val := by
  obtain ⟨carrier, _, forCarrier⟩ :=
    (input.localizedSpiroAuthoritySystemAt?_eq_some_iff center system).mp computed
  obtain ⟨firstRing, secondRing, _, forRings⟩ :=
    (input.localizedSpiroAuthoritySystemForCarrier?_eq_some_iff center carrier system).mp
      forCarrier
  obtain ⟨firstInternal, secondInternal, _, _, same⟩ :=
    (input.localizedSpiroAuthoritySystemForRings?_eq_some_iff center firstRing secondRing
      system).mp forRings
  rw [same, localizedSpiroAuthoritySystemOf_center]

/-- **Soundness of the automatic selector.**  Every returned system is supported by a perceived
carrier that it matches and is mechanically valid for the actual certified source. -/
theorem localizedSpiroAuthoritySystemAt?_sound
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (system : P93AuthoritySpiroSystem)
    (computed : input.localizedSpiroAuthoritySystemAt? center = some system) :
    ∃ carrier,
      input.DeclarativeLocalizedSpiroCenter center carrier ∧
        system.MechanicallyValidFor input.certified.input ∧
          input.LocalizedSpiroAuthoritySystemMatches center carrier system := by
  obtain ⟨carrier, hcenter, forCarrier⟩ :=
    (input.localizedSpiroAuthoritySystemAt?_eq_some_iff center system).mp computed
  obtain ⟨firstRing, secondRing, hlist, forRings⟩ :=
    (input.localizedSpiroAuthoritySystemForCarrier?_eq_some_iff center carrier system).mp
      forCarrier
  obtain ⟨firstInternal, secondInternal, firstComputed, secondComputed, same⟩ :=
    (input.localizedSpiroAuthoritySystemForRings?_eq_some_iff center firstRing secondRing
      system).mp forRings
  have judged : input.DeclarativeLocalizedSpiroCenter center carrier :=
    (input.localizedSpiroCenterAt?_eq_some_iff center carrier).mp hcenter
  have firstPresent : firstRing ∈ carrier.rings := by
    rw [← Finset.mem_toList, hlist]
    simp
  have secondPresent : secondRing ∈ carrier.rings := by
    rw [← Finset.mem_toList, hlist]
    simp
  have ringsEq : carrier.rings = {firstRing, secondRing} := by
    rw [← Finset.toList_toFinset carrier.rings, hlist]
    simp
  have firstSpec : input.LocalizedSimpleCycleInternalPathSpec firstRing center firstInternal :=
    input.localizedSimpleCycleInternalPath?_sound firstRing center firstInternal firstComputed
  have secondSpec : input.LocalizedSimpleCycleInternalPathSpec secondRing center secondInternal :=
    input.localizedSimpleCycleInternalPath?_sound secondRing center secondInternal secondComputed
  refine ⟨carrier, judged, ?_, ?_⟩
  · rw [same]
    exact mechanicallyValidFor_localizedSpiroAuthoritySystemOf input center carrier judged
      firstRing secondRing ringsEq firstInternal secondInternal firstSpec secondSpec
  · rw [same]
    exact localizedSpiroAuthoritySystemMatches_of_specs input center carrier firstRing secondRing
      ringsEq firstInternal secondInternal firstSpec secondSpec

/-- **Construction succeeds on every perceived carrier, with validity and matching.**  The two rings
of the carrier are read off the `Finset.toList` enumeration; each is a declarative simple cycle
containing the center by `ring_meaning`, so the dependency completeness theorem supplies an internal
traversal for each.  Since the argument is an arbitrary two-element enumeration, the chosen order of
`Finset.toList` never matters: no ring order, ring list, path validity or output-success hypothesis
is supplied. -/
theorem localizedSpiroAuthoritySystemAt?_complete
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedSpiroCenter center carrier) :
    ∃ system,
      input.localizedSpiroAuthoritySystemAt? center = some system ∧
        system.MechanicallyValidFor input.certified.input ∧
          input.LocalizedSpiroAuthoritySystemMatches center carrier system := by
  classical
  have hcenter : input.localizedSpiroCenterAt? center = some carrier :=
    (input.localizedSpiroCenterAt?_eq_some_iff center carrier).mpr judged
  have lengthTwo : carrier.rings.toList.length = 2 := by
    rw [Finset.length_toList]
    exact judged.2.1
  obtain ⟨firstRing, secondRing, hlist⟩ := List.length_eq_two.mp lengthTwo
  have firstPresent : firstRing ∈ carrier.rings := by
    rw [← Finset.mem_toList, hlist]
    simp
  have secondPresent : secondRing ∈ carrier.rings := by
    rw [← Finset.mem_toList, hlist]
    simp
  have ringsEq : carrier.rings = {firstRing, secondRing} := by
    rw [← Finset.toList_toFinset carrier.rings, hlist]
    simp
  have firstMeaning := judged.ring_meaning input center carrier firstRing firstPresent
  have secondMeaning := judged.ring_meaning input center carrier secondRing secondPresent
  obtain ⟨firstInternal, firstComputed, firstSpec⟩ :=
    input.localizedSimpleCycleInternalPath?_complete firstRing center
      firstMeaning.1 firstMeaning.2.2
  obtain ⟨secondInternal, secondComputed, secondSpec⟩ :=
    input.localizedSimpleCycleInternalPath?_complete secondRing center
      secondMeaning.1 secondMeaning.2.2
  refine ⟨localizedSpiroAuthoritySystemOf input center firstInternal secondInternal, ?_, ?_, ?_⟩
  · rw [input.localizedSpiroAuthoritySystemAt?_eq_some_iff]
    refine ⟨carrier, hcenter, ?_⟩
    rw [input.localizedSpiroAuthoritySystemForCarrier?_eq_some_iff]
    refine ⟨firstRing, secondRing, hlist, ?_⟩
    rw [input.localizedSpiroAuthoritySystemForRings?_eq_some_iff]
    exact ⟨firstInternal, secondInternal, firstComputed, secondComputed, rfl⟩
  · exact mechanicallyValidFor_localizedSpiroAuthoritySystemOf input center carrier judged
      firstRing secondRing ringsEq firstInternal secondInternal firstSpec secondSpec
  · exact localizedSpiroAuthoritySystemMatches_of_specs input center carrier firstRing secondRing
      ringsEq firstInternal secondInternal firstSpec secondSpec

/-- Existence form of construction success. -/
theorem localizedSpiroAuthoritySystemAt?_isSome_of_carrier
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedSpiroCenter center carrier) :
    ∃ system, input.localizedSpiroAuthoritySystemAt? center = some system := by
  obtain ⟨system, computed, _, _⟩ :=
    input.localizedSpiroAuthoritySystemAt?_complete center carrier judged
  exact ⟨system, computed⟩

/-- Duplicate-free list with all entries equal to the given value is the singleton list. -/
theorem list_eq_singleton_of_nodup_of_forall_eq {α : Type*} {list : List α} {value : α}
    (nodup : list.Nodup) (present : value ∈ list)
    (allEqual : ∀ other ∈ list, other = value) : list = [value] := by
  induction list with
  | nil => simp at present
  | cons head tail _ =>
      have headEq : head = value := allEqual head (by simp)
      have headAbsent : head ∉ tail := (List.nodup_cons.mp nodup).1
      have tailEmpty : tail = [] := by
        cases tail with
        | nil => rfl
        | cons next rest =>
            have nextEq : next = value :=
              allEqual next (List.mem_cons_of_mem head (by simp))
            have headNext : head = next := headEq.trans nextEq.symm
            exact absurd (by simp [headNext]) headAbsent
      rw [headEq, tailEmpty]

/-! ## Whole-input inventory -/

/-- Every authority system produced by an automatically perceived spiro center of the input. -/
noncomputable def localizedSpiroAuthoritySystems (input : CertifiedLocalizedCIPInput) :
    List P93AuthoritySpiroSystem :=
  input.localizedSpiroCenters.toList.filterMap fun center =>
    input.localizedSpiroAuthoritySystemAt? center

theorem mem_localizedSpiroAuthoritySystems_iff
    (input : CertifiedLocalizedCIPInput) (system : P93AuthoritySpiroSystem) :
    system ∈ input.localizedSpiroAuthoritySystems ↔
      ∃ center,
        center ∈ input.localizedSpiroCenters ∧
          input.localizedSpiroAuthoritySystemAt? center = some system := by
  classical
  simp [localizedSpiroAuthoritySystems, List.mem_filterMap]

theorem localizedSpiroAuthoritySystems_nodup (input : CertifiedLocalizedCIPInput) :
    input.localizedSpiroAuthoritySystems.Nodup := by
  classical
  unfold localizedSpiroAuthoritySystems
  refine List.Nodup.filterMap ?_ input.localizedSpiroCenters_toList_nodup
  intro firstAtom secondAtom system firstPresent secondPresent
  have firstValue : system.center = firstAtom.val :=
    input.localizedSpiroAuthoritySystemAt?_center_eq firstAtom system firstPresent
  have secondValue : system.center = secondAtom.val :=
    input.localizedSpiroAuthoritySystemAt?_center_eq secondAtom system secondPresent
  exact Fin.ext (by rw [← firstValue, secondValue])

/-- Every inventoried system is mechanically valid for the actual certified source. -/
theorem localizedSpiroAuthoritySystems_forall_valid (input : CertifiedLocalizedCIPInput) :
    ∀ system ∈ input.localizedSpiroAuthoritySystems,
      system.MechanicallyValidFor input.certified.input := by
  intro system present
  obtain ⟨center, _, computed⟩ :=
    (input.mem_localizedSpiroAuthoritySystems_iff system).mp present
  obtain ⟨carrier, _, valid, _⟩ := input.localizedSpiroAuthoritySystemAt?_sound center system computed
  exact valid

/-- **No omission at the count level, forward direction.**  A single inventoried system centered on
`center` already proves that a perceived carrier exists there.  Nothing about how the inventory was
enumerated is assumed: the system exposes its own center index. -/
theorem localizedSpiroAuthoritySystems_count_eq_one_imp_exists
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (countOne : (input.localizedSpiroAuthoritySystems.filter
      (fun system => system.center = center.val)).length = 1) :
    ∃ carrier, input.DeclarativeLocalizedSpiroCenter center carrier := by
  classical
  have nonempty : (input.localizedSpiroAuthoritySystems.filter
      (fun system => system.center = center.val)) ≠ [] := by
    intro empty
    rw [empty] at countOne
    simp at countOne
  obtain ⟨system, present⟩ := List.exists_mem_of_ne_nil _ nonempty
  rw [List.mem_filter] at present
  obtain ⟨systemPresent, accepted⟩ := present
  have centerEq : system.center = center.val := of_decide_eq_true accepted
  obtain ⟨someCenter, centersMember, computed⟩ :=
    (input.mem_localizedSpiroAuthoritySystems_iff system).mp systemPresent
  have systemValue : system.center = someCenter.val :=
    input.localizedSpiroAuthoritySystemAt?_center_eq someCenter system computed
  have valueEq : someCenter.val = center.val := by
    rw [← systemValue, centerEq]
  have centerIdentity : someCenter = center := Fin.ext valueEq
  rw [← centerIdentity]
  exact (input.mem_localizedSpiroCenters_iff someCenter).mp centersMember

/-- **No omission at the count level, reverse direction.**  A perceived carrier forces exactly one
centered inventoried system.  The produced system is unique because every inventoried system
exposes its own requested center index, and the selector is a function. -/
theorem localizedSpiroAuthoritySystems_count_eq_one_of_exists
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (existsCarrier : ∃ carrier, input.DeclarativeLocalizedSpiroCenter center carrier) :
    (input.localizedSpiroAuthoritySystems.filter
      (fun system => system.center = center.val)).length = 1 := by
  classical
  obtain ⟨carrier, judged⟩ := existsCarrier
  obtain ⟨system, computed⟩ :=
    input.localizedSpiroAuthoritySystemAt?_isSome_of_carrier center carrier judged
  have systemCenter : system.center = center.val :=
    input.localizedSpiroAuthoritySystemAt?_center_eq center system computed
  have centerPresent : center ∈ input.localizedSpiroCenters :=
    (input.mem_localizedSpiroCenters_iff center).mpr ⟨carrier, judged⟩
  have systemPresent : system ∈ input.localizedSpiroAuthoritySystems :=
    (input.mem_localizedSpiroAuthoritySystems_iff system).mpr
      ⟨center, centerPresent, computed⟩
  have nodupFiltered : (input.localizedSpiroAuthoritySystems.filter
      (fun system => system.center = center.val)).Nodup :=
    List.Nodup.filter (fun system => decide (system.center = center.val))
      input.localizedSpiroAuthoritySystems_nodup
  have presentFiltered : system ∈ input.localizedSpiroAuthoritySystems.filter
      (fun system => system.center = center.val) := by
    rw [List.mem_filter]
    exact ⟨systemPresent, by simp [systemCenter]⟩
  have allEqual : ∀ other ∈ input.localizedSpiroAuthoritySystems.filter
      (fun system => system.center = center.val), other = system := by
    intro other inFilter
    rw [List.mem_filter] at inFilter
    obtain ⟨otherPresent, otherAccepted⟩ := inFilter
    have otherCenter : other.center = center.val := of_decide_eq_true otherAccepted
    obtain ⟨otherCenterAtom, _, otherComputed⟩ :=
      (input.mem_localizedSpiroAuthoritySystems_iff other).mp otherPresent
    have otherValue : other.center = otherCenterAtom.val :=
      input.localizedSpiroAuthoritySystemAt?_center_eq otherCenterAtom other otherComputed
    have atomEq : otherCenterAtom = center := by
      apply Fin.ext
      rw [← otherValue, otherCenter]
    rw [atomEq] at otherComputed
    rw [computed] at otherComputed
    exact (Option.some.inj otherComputed).symm
  have singleton : input.localizedSpiroAuthoritySystems.filter
      (fun system => system.center = center.val) = [system] :=
    list_eq_singleton_of_nodup_of_forall_eq nodupFiltered presentFiltered allEqual
  rw [singleton]
  rfl

/-- **Exact center count.**  The inventory contains exactly one system centered on `center` if and
only if the graph perception predicate finds a complete two-ring spiro carrier there.  No
observation list, traversal, ordering or output-success assumption is supplied. -/
theorem localizedSpiroAuthoritySystems_count_eq_one_iff
    (input : CertifiedLocalizedCIPInput) (center : input.Atom) :
    (input.localizedSpiroAuthoritySystems.filter
      (fun system => system.center = center.val)).length = 1 ↔
      ∃ carrier, input.DeclarativeLocalizedSpiroCenter center carrier :=
  ⟨input.localizedSpiroAuthoritySystems_count_eq_one_imp_exists center,
    input.localizedSpiroAuthoritySystems_count_eq_one_of_exists center⟩

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.semanticEdgeKey_eq_endpoints
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedCovalentRecord?_eq_some_of_pair
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedAdj_iff_p93AuthorityBinaryBond
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedSpiroAuthoritySystemMatches.center_eq
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedSpiroAuthoritySystemMatches.rings_eq
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.list_toFinset_map_val
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.toFinset_cons_map_val
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mechanicallyValidFor_localizedSpiroAuthoritySystemOf
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedSpiroAuthoritySystemMatches_of_specs
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedSpiroAuthoritySystemForRings?_eq_some_iff
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedSpiroAuthoritySystemForCarrier?_eq_some_iff
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedSpiroAuthoritySystemAt?_eq_some_iff
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedSpiroAuthoritySystemAt?_center_eq
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedSpiroAuthoritySystemAt?_sound
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.list_eq_singleton_of_nodup_of_forall_eq
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mem_localizedSpiroAuthoritySystems_iff
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedSpiroAuthoritySystems_nodup
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedSpiroAuthoritySystems_forall_valid
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedSpiroAuthoritySystemAt?_complete
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedSpiroAuthoritySystemAt?_isSome_of_carrier
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedSpiroAuthoritySystems_count_eq_one_imp_exists
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedSpiroAuthoritySystems_count_eq_one_of_exists
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedSpiroAuthoritySystems_count_eq_one_iff
