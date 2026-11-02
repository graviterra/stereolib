import TetraStereo.OneCenter.AuthoritativeCIPGraph
import TetraStereo.OneCenter.IUPACNext54P92DigraphRule1aReviewedSemantics
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Graph-native P-92 semantic representation bridge

This module stays entirely on the authority-input/`MoleculeGraph` side.  An already established
`P92ClassicalConstitutionRepresents` witness forces the semantic source into the exact localized
closed-shell pair-bond domain, and it forces the represented graph data to agree pointwise with
`SemanticMolecule.toLocalizedMoleculeGraph`.  No parser `RawMolecule`, reviewed judgment, caller
policy, or copied reference result is used.  The executable root-bond normalizer is defined here
independently and only then proved equal to the reviewed `P92CanonicalRootBond` specification.

The canonical P/S oxido graph below is consequently defined from that localized semantic graph
itself.  The results are stated on the canonical vertex type `Fin source.molecule.atomCount`;
clients whose observations use a propositionally equal atom-count index still need an explicit
dependent reindexing wrapper.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

private theorem semanticEdgeKey_eq_iff
    {left right first second : Nat} :
    semanticEdgeKey left right = semanticEdgeKey first second ↔
      (left = first ∧ right = second) ∨ (left = second ∧ right = first) := by
  simp only [semanticEdgeKey]
  by_cases leftRight : left ≤ right <;>
    by_cases firstSecond : first ≤ second <;>
      simp [Nat.min_def, Nat.max_def, leftRight, firstSecond] <;> omega

private theorem p92PairInteractionRepresents_symm
    {atomCount : Nat} (molecule : MoleculeGraph (Fin atomCount))
    {left right : Fin atomCount} {interaction : SemanticInteraction}
    (represented : P92PairInteractionRepresents molecule left right interaction) :
    P92PairInteractionRepresents molecule right left interaction := by
  refine ⟨?_, ?_⟩
  · simpa [or_comm] using represented.1
  · simpa [molecule.bond_symm] using represented.2

private theorem p92RootPair_comm {atomCount : Nat}
    (center ligand left right : Fin atomCount) :
    P92RootPair center ligand left right ↔ P92RootPair center ligand right left := by
  simp [P92RootPair, and_comm, or_comm]

private theorem localizedCovalentRecord?_eq_some_of_pair
    {atomCount : Nat} (molecule : MoleculeGraph (Fin atomCount))
    {left right : Fin atomCount} {interaction : SemanticInteraction}
    (positive : 0 < molecule.bond left right)
    (represented : P92PairInteractionRepresents molecule left right interaction) :
    interaction.localizedCovalentRecord? =
      some (semanticEdgeKey left.val right.val, molecule.bond left right) := by
  rcases represented.1 with participants | participants
  · simp [SemanticInteraction.localizedCovalentRecord?, participants, represented.2, positive]
  · simp [SemanticInteraction.localizedCovalentRecord?, participants, represented.2, positive,
      semanticEdgeKey_comm]

private theorem represented_interactions_same_of_key
    {source : AuthoritativeChemicalInput} {atomCount : Nat}
    {molecule : MoleculeGraph (Fin atomCount)}
    (represented : P92ClassicalConstitutionRepresents source molecule)
    {first second : SemanticInteraction}
    (firstMem : first ∈ source.molecule.interactions)
    (secondMem : second ∈ source.molecule.interactions)
    {firstLeft firstRight secondLeft secondRight : Fin atomCount}
    (firstDifferent : firstLeft ≠ firstRight)
    (firstPositive : 0 < molecule.bond firstLeft firstRight)
    (firstPair : P92PairInteractionRepresents molecule firstLeft firstRight first)
    (secondPair : P92PairInteractionRepresents molecule secondLeft secondRight second)
    (sameKey : semanticEdgeKey firstLeft.val firstRight.val =
      semanticEdgeKey secondLeft.val secondRight.val) :
    first = second := by
  rcases semanticEdgeKey_eq_iff.mp sameKey with same | reversed
  · have leftEq : firstLeft = secondLeft := Fin.ext same.1
    have rightEq : firstRight = secondRight := Fin.ext same.2
    subst secondLeft
    subst secondRight
    rcases (represented.bond_exact firstLeft firstRight firstDifferent).mp firstPositive with
      ⟨canonical, canonicalProperty, unique⟩
    exact (unique first ⟨firstMem, firstPair⟩).trans
      (unique second ⟨secondMem, secondPair⟩).symm
  · have leftEq : firstLeft = secondRight := Fin.ext reversed.1
    have rightEq : firstRight = secondLeft := Fin.ext reversed.2
    subst secondRight
    subst secondLeft
    rcases (represented.bond_exact firstLeft firstRight firstDifferent).mp firstPositive with
      ⟨canonical, canonicalProperty, unique⟩
    exact (unique first ⟨firstMem, firstPair⟩).trans
      (unique second ⟨secondMem,
        p92PairInteractionRepresents_symm molecule secondPair⟩).symm

/-- An exact classical constitutional representation forces the authority molecule into the
direct localized semantic-graph domain. -/
theorem p92ClassicalConstitutionRepresents_localizedCIPGraphReady
    (source : AuthoritativeChemicalInput) {atomCount : Nat}
    (molecule : MoleculeGraph (Fin atomCount))
    (represented : P92ClassicalConstitutionRepresents source molecule) :
    source.molecule.LocalizedCIPGraphReady := by
  have structurallyWellFormed : source.molecule.StructurallyWellFormed := by
    rw [SemanticMolecule.StructurallyWellFormed, List.all_eq_true]
    intro interaction interactionMem
    rw [SemanticInteraction.wellFormed?_eq_true_iff]
    rcases represented.interaction_supported interaction interactionMem with
      ⟨left, right, different, positive, pair⟩
    have valueDifferent : left.val ≠ right.val := fun equality => different (Fin.ext equality)
    have reverseValueDifferent : right.val ≠ left.val := Ne.symm valueDifferent
    rcases pair.1 with participants | participants
    · simp [SemanticInteraction.WellFormed, participants, valueDifferent,
        represented.atomCount_exact]
    · simp [SemanticInteraction.WellFormed, participants, reverseValueDifferent,
        represented.atomCount_exact]
  have atomsClosed : source.molecule.ExplicitLocalizedClosedShellAtoms := by
    intro atom atomMem
    obtain ⟨index, indexGet⟩ := List.get_of_mem atomMem
    have lookup := listGet?_eq_some_get source.molecule.atoms index
    let graphIndex : Fin atomCount := Fin.cast represented.atomCount_exact index
    rcases represented.atom_exact graphIndex with ⟨sourceAtom, sourceLookup, atomExact⟩
    have sourceLookupAtIndex : listGet? source.molecule.atoms index.val = some sourceAtom := by
      simpa [graphIndex] using sourceLookup
    have sourceAtomEq : sourceAtom = atom := by
      rw [indexGet] at lookup
      exact Option.some.inj (sourceLookupAtIndex.symm.trans lookup)
    subst sourceAtom
    rcases atomExact with ⟨atomicNumber, mass, massLookup, graphMass, charge, shell, aromatic⟩
    exact ⟨shell, aromatic⟩
  have massesKnown : source.molecule.AllRule2MassesKnown := by
    intro atom atomMem
    obtain ⟨index, indexGet⟩ := List.get_of_mem atomMem
    have lookup := listGet?_eq_some_get source.molecule.atoms index
    let graphIndex : Fin atomCount := Fin.cast represented.atomCount_exact index
    rcases represented.atom_exact graphIndex with ⟨sourceAtom, sourceLookup, atomExact⟩
    have sourceLookupAtIndex : listGet? source.molecule.atoms index.val = some sourceAtom := by
      simpa [graphIndex] using sourceLookup
    have sourceAtomEq : sourceAtom = atom := by
      rw [indexGet] at lookup
      exact Option.some.inj (sourceLookupAtIndex.symm.trans lookup)
    subst sourceAtom
    rcases atomExact with ⟨atomicNumber, mass, massLookup, graphMass, charge, shell, aromatic⟩
    exact ⟨mass, massLookup⟩
  have pairsOnly : source.molecule.LocalizedCovalentPairsOnly := by
    intro interaction interactionMem
    rcases represented.interaction_supported interaction interactionMem with
      ⟨left, right, different, positive, pair⟩
    rcases pair.1 with participants | participants
    · exact ⟨left.val, right.val, molecule.bond left right,
        participants, pair.2, positive⟩
    · exact ⟨right.val, left.val, molecule.bond left right,
        participants, pair.2, positive⟩
  have recordsUnique : source.molecule.LocalizedCovalentRecordsUnique := by
    unfold SemanticMolecule.LocalizedCovalentRecordsUnique
    unfold SemanticMolecule.localizedCovalentKeys SemanticMolecule.localizedCovalentRecords
    have keysNodup : ∀ interactions : List SemanticInteraction,
        (∀ interaction ∈ interactions, interaction ∈ source.molecule.interactions) →
        interactions.Nodup →
        ((interactions.filterMap SemanticInteraction.localizedCovalentRecord?).map
          Prod.fst).Nodup := by
      intro interactions subset nodup
      induction interactions with
      | nil => simp
      | cons head tail inductionHypothesis =>
        have headMem : head ∈ source.molecule.interactions := subset head (by simp)
        rcases represented.interaction_supported head headMem with
          ⟨headLeft, headRight, headDifferent, headPositive, headPair⟩
        have headRecord := localizedCovalentRecord?_eq_some_of_pair molecule
          headPositive headPair
        rw [List.filterMap_cons, headRecord]
        simp only [List.map_cons]
        apply List.nodup_cons.mpr
        constructor
        · intro keyMem
          rw [List.mem_map] at keyMem
          obtain ⟨record, recordMem, recordKey⟩ := keyMem
          rw [List.mem_filterMap] at recordMem
          obtain ⟨other, otherMem, otherRecord⟩ := recordMem
          have otherSourceMem : other ∈ source.molecule.interactions :=
            subset other (by simp [otherMem])
          rcases represented.interaction_supported other otherSourceMem with
            ⟨otherLeft, otherRight, otherDifferent, otherPositive, otherPair⟩
          have otherRecordExact := localizedCovalentRecord?_eq_some_of_pair molecule
            otherPositive otherPair
          rw [otherRecordExact] at otherRecord
          have sameRecord := Option.some.inj otherRecord
          have sameKey : semanticEdgeKey headLeft.val headRight.val =
              semanticEdgeKey otherLeft.val otherRight.val := by
            simpa [recordKey] using congrArg Prod.fst sameRecord.symm
          have sameInteraction : head = other :=
            represented_interactions_same_of_key represented headMem otherSourceMem
              headDifferent headPositive headPair otherPair sameKey
          have headNotTail := (List.nodup_cons.mp nodup).1
          exact headNotTail (sameInteraction ▸ otherMem)
        · apply inductionHypothesis
          · intro interaction interactionMem
            exact subset interaction (List.mem_cons_of_mem head interactionMem)
          · exact (List.nodup_cons.mp nodup).2
    exact keysNodup source.molecule.interactions (by simp)
      represented.interaction_records_nodup
  exact ⟨structurallyWellFormed, atomsClosed, massesKnown, pairsOnly, recordsUnique⟩

/-- The represented graph and the direct localized semantic graph agree on every datum consumed
by P-92.  This pointwise statement avoids hiding the atom-count equality in a dependent cast. -/
theorem p92ClassicalConstitutionRepresents_ext_localizedGraph
    (source : AuthoritativeChemicalInput)
    (molecule : MoleculeGraph (Fin source.molecule.atomCount))
    (represented : P92ClassicalConstitutionRepresents source molecule) :
    (∀ atom, molecule.atomZ atom = source.molecule.toLocalizedMoleculeGraph.atomZ atom) ∧
    (∀ atom, molecule.atomMass atom = source.molecule.toLocalizedMoleculeGraph.atomMass atom) ∧
    (∀ atom, molecule.formalCharge atom =
      source.molecule.toLocalizedMoleculeGraph.formalCharge atom) ∧
    ∀ left right, molecule.bond left right =
      source.molecule.toLocalizedMoleculeGraph.bond left right := by
  have ready := p92ClassicalConstitutionRepresents_localizedCIPGraphReady
    source molecule represented
  have atomData : ∀ atom : Fin source.molecule.atomCount,
      molecule.atomZ atom = source.molecule.toLocalizedMoleculeGraph.atomZ atom ∧
      molecule.atomMass atom = source.molecule.toLocalizedMoleculeGraph.atomMass atom ∧
      molecule.formalCharge atom = source.molecule.toLocalizedMoleculeGraph.formalCharge atom := by
    intro atom
    rcases represented.atom_exact atom with ⟨sourceAtom, sourceLookup, exact⟩
    have lookup := listGet?_eq_some_get source.molecule.atoms atom
    have sourceAtomEq : sourceAtom = source.molecule.atoms.get atom :=
      Option.some.inj (sourceLookup.symm.trans lookup)
    subst sourceAtom
    rcases exact with ⟨atomicNumber, mass, massLookup, productionMass, charge, unpaired, aromatic⟩
    refine ⟨atomicNumber, ?_, charge⟩
    change molecule.atomMass atom =
      (CIPRule2MassData.rule2MassPico?
        (source.molecule.atoms.get atom).element.atomicNumber
        (source.molecule.atoms.get atom).isotopeMassNumber?).getD 0
    rw [massLookup]
    exact productionMass
  refine ⟨fun atom => (atomData atom).1, fun atom => (atomData atom).2.1,
    fun atom => (atomData atom).2.2, ?_⟩
  intro left right
  by_cases same : left = right
  · subst right
    simp [molecule.bond_self]
  · have sourcePositive : 0 < molecule.bond left right ↔
        ∃! interaction, interaction ∈ source.molecule.interactions ∧
          P92PairInteractionRepresents molecule left right interaction :=
      represented.bond_exact left right same
    by_cases positive : 0 < molecule.bond left right
    · rcases sourcePositive.mp positive with ⟨interaction, interactionProperty, unique⟩
      have record := localizedCovalentRecord?_eq_some_of_pair molecule positive interactionProperty.2
      have recordMem : (semanticEdgeKey left.val right.val, molecule.bond left right) ∈
          source.molecule.localizedCovalentRecords := by
        rw [SemanticMolecule.localizedCovalentRecords, List.mem_filterMap]
        exact ⟨interaction, interactionProperty.1, record⟩
      symm
      exact source.molecule.toLocalizedMoleculeGraph_bond_eq_of_record
        left right (molecule.bond left right) ready same recordMem
    · have noRecord : semanticEdgeKey left.val right.val ∉
          source.molecule.localizedCovalentKeys := by
        intro keyMem
        rw [SemanticMolecule.localizedCovalentKeys, List.mem_map] at keyMem
        obtain ⟨record, recordMem, recordKey⟩ := keyMem
        rw [SemanticMolecule.localizedCovalentRecords, List.mem_filterMap] at recordMem
        obtain ⟨interaction, interactionMem, interactionRecord⟩ := recordMem
        rcases represented.interaction_supported interaction interactionMem with
          ⟨first, second, different, interactionPositive, pair⟩
        have exactRecord := localizedCovalentRecord?_eq_some_of_pair molecule
          interactionPositive pair
        rw [exactRecord] at interactionRecord
        have keyEqual : semanticEdgeKey left.val right.val =
            semanticEdgeKey first.val second.val := by
          have recordEqual := Option.some.inj interactionRecord
          simpa [recordKey] using congrArg Prod.fst recordEqual.symm
        rcases semanticEdgeKey_eq_iff.mp keyEqual with aligned | reversed
        · have leftEq : left = first := Fin.ext aligned.1
          have rightEq : right = second := Fin.ext aligned.2
          subst first
          subst second
          exact positive interactionPositive
        · have leftEq : left = second := Fin.ext reversed.1
          have rightEq : right = first := Fin.ext reversed.2
          subst second
          subst first
          exact positive (by simpa [molecule.bond_symm] using interactionPositive)
      have localizedZero := source.molecule.toLocalizedMoleculeGraph_bond_eq_zero_of_no_record
        left right noRecord
      exact Nat.eq_zero_of_not_pos positive |>.trans localizedZero.symm

/-- Executable semantic P/S oxido root normalization.  Its condition is intentionally stated
directly on graph data rather than by calling the reviewed-reference predicate. -/
def semanticP92CanonicalRootBond {atomCount : Nat}
    (molecule : MoleculeGraph (Fin atomCount))
    (center ligand left right : Fin atomCount) : Nat :=
  if left = right then 0
  else if
      (((left = center ∧ right = ligand) ∨ (left = ligand ∧ right = center)) ∧
        ((molecule.atomZ center = 15 ∨ molecule.atomZ center = 16) ∧
          molecule.atomZ ligand = 8 ∧ molecule.bond center ligand = 2)) then
    1
  else molecule.bond left right

/-- The executable semantic normalization implements the independently stated P-92 canonical
root-bond relation exactly. -/
theorem semanticP92CanonicalRootBond_eq_reference {atomCount : Nat}
    (molecule : MoleculeGraph (Fin atomCount))
    (center ligand left right : Fin atomCount) :
    semanticP92CanonicalRootBond molecule center ligand left right =
      P92CanonicalRootBond molecule center ligand left right := by
  by_cases same : left = right
  · simp [semanticP92CanonicalRootBond, P92CanonicalRootBond, same]
  · by_cases rootPair :
        (left = center ∧ right = ligand) ∨ (left = ligand ∧ right = center)
    · by_cases eligible :
          (molecule.atomZ center = 15 ∨ molecule.atomZ center = 16) ∧
            molecule.atomZ ligand = 8 ∧ molecule.bond center ligand = 2
      · simp [semanticP92CanonicalRootBond, P92CanonicalRootBond,
          P92RootPair, P92OxidoRootEligible, same, rootPair, eligible]
      · simp [semanticP92CanonicalRootBond, P92CanonicalRootBond,
          P92RootPair, P92OxidoRootEligible, same, rootPair, eligible]
    · simp [semanticP92CanonicalRootBond, P92CanonicalRootBond,
        P92RootPair, P92OxidoRootEligible, same, rootPair]

/-- Canonical P/S oxido root normalization of the direct localized semantic graph. -/
def p92CanonicalLocalizedMoleculeGraph
    (source : AuthoritativeChemicalInput)
    (center ligand : Fin source.molecule.atomCount) :
    MoleculeGraph (Fin source.molecule.atomCount) where
  atomZ := source.molecule.toLocalizedMoleculeGraph.atomZ
  atomMass := source.molecule.toLocalizedMoleculeGraph.atomMass
  formalCharge := source.molecule.toLocalizedMoleculeGraph.formalCharge
  bond := semanticP92CanonicalRootBond
    source.molecule.toLocalizedMoleculeGraph center ligand
  bond_symm := by
    intro left right
    rw [semanticP92CanonicalRootBond_eq_reference,
      semanticP92CanonicalRootBond_eq_reference]
    by_cases same : left = right
    · subst right
      simp [P92CanonicalRootBond]
    · have reverse : right ≠ left := fun equality => same equality.symm
      by_cases rootPair : P92RootPair center ligand left right
      · have reverseRootPair : P92RootPair center ligand right left :=
          (p92RootPair_comm center ligand left right).mp rootPair
        by_cases eligible :
            P92OxidoRootEligible source.molecule.toLocalizedMoleculeGraph center ligand
        · simp [P92CanonicalRootBond, same, reverse, rootPair, reverseRootPair, eligible]
        · simp only [P92CanonicalRootBond, if_neg same, if_neg reverse, rootPair,
            reverseRootPair, true_and, eligible, if_false]
          exact source.molecule.localizedBondOrder_comm left.val right.val
      · have reverseRootPair : ¬P92RootPair center ligand right left :=
          fun present => rootPair ((p92RootPair_comm center ligand left right).mpr present)
        simp only [P92CanonicalRootBond, if_neg same, if_neg reverse, rootPair,
          reverseRootPair, false_and, if_false]
        exact source.molecule.localizedBondOrder_comm left.val right.val
  bond_self := by
    intro atom
    rw [semanticP92CanonicalRootBond_eq_reference]
    simp [P92CanonicalRootBond]

/-- The graph-native normalization is an exact canonical P-92 constitutional representation. -/
theorem p92CanonicalConstitutionRepresents_canonicalLocalizedMoleculeGraph
    (source : AuthoritativeChemicalInput)
    (molecule : MoleculeGraph (Fin source.molecule.atomCount))
    (represented : P92ClassicalConstitutionRepresents source molecule)
    (center ligand : Fin source.molecule.atomCount) :
    P92CanonicalConstitutionRepresents source center ligand
      (p92CanonicalLocalizedMoleculeGraph source center ligand) := by
  have exactData := p92ClassicalConstitutionRepresents_ext_localizedGraph
    source molecule represented
  have localizedRepresents : P92ClassicalConstitutionRepresents source
      source.molecule.toLocalizedMoleculeGraph := by
    refine
      { atomCount_exact := represented.atomCount_exact
        interaction_records_nodup := represented.interaction_records_nodup
        atom_exact := ?_
        interaction_supported := ?_
        bond_exact := ?_ }
    · intro atom
      rcases represented.atom_exact atom with ⟨sourceAtom, lookup, atomExact⟩
      refine ⟨sourceAtom, lookup, ?_⟩
      rcases atomExact with ⟨z, mass, massLookup, graphMass, charge, shell, aromatic⟩
      exact ⟨(exactData.1 atom).symm.trans z, mass, massLookup,
        (exactData.2.1 atom).symm.trans graphMass,
        (exactData.2.2.1 atom).symm.trans charge, shell, aromatic⟩
    · intro interaction interactionMem
      rcases represented.interaction_supported interaction interactionMem with
        ⟨left, right, different, positive, pair⟩
      refine ⟨left, right, different, ?_, pair.1, ?_⟩
      · simpa [exactData.2.2.2 left right] using positive
      · exact pair.2.trans (congrArg SemanticInteractionKind.covalent
          (exactData.2.2.2 left right))
    · intro left right different
      simpa [P92PairInteractionRepresents, exactData.2.2.2 left right] using
        represented.bond_exact left right different
  exact .intro source.molecule.toLocalizedMoleculeGraph localizedRepresents
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (semanticP92CanonicalRootBond_eq_reference
      source.molecule.toLocalizedMoleculeGraph center ligand)

/-- Every canonical representation carries the authoritative source atom-count equality needed
to reindex an independently supplied observation onto the fixed semantic vertex type. -/
theorem P92CanonicalConstitutionRepresents.atomCount_exact
    {source : AuthoritativeChemicalInput} {atomCount : Nat}
    {center ligand : Fin atomCount} {canonical : MoleculeGraph (Fin atomCount)}
    (represented : P92CanonicalConstitutionRepresents source center ligand canonical) :
    source.molecule.atomCount = atomCount := by
  cases represented with
  | intro _ sourceGraphRepresents _ _ _ _ =>
      exact sourceGraphRepresents.atomCount_exact

/-- Relative to the canonical semantic vertex type, every canonical representation is exactly
the graph-native localized normalization. -/
theorem p92CanonicalConstitutionRepresents_unique
    (source : AuthoritativeChemicalInput)
    (center ligand : Fin source.molecule.atomCount)
    (canonical : MoleculeGraph (Fin source.molecule.atomCount))
    (represented : P92CanonicalConstitutionRepresents source center ligand canonical) :
    (∀ atom, canonical.atomZ atom =
      (p92CanonicalLocalizedMoleculeGraph source center ligand).atomZ atom) ∧
    (∀ atom, canonical.atomMass atom =
      (p92CanonicalLocalizedMoleculeGraph source center ligand).atomMass atom) ∧
    (∀ atom, canonical.formalCharge atom =
      (p92CanonicalLocalizedMoleculeGraph source center ligand).formalCharge atom) ∧
    ∀ left right, canonical.bond left right =
      (p92CanonicalLocalizedMoleculeGraph source center ligand).bond left right := by
  rcases represented with ⟨sourceGraph, sourceRepresents, atomZ, atomMass, charge, bond⟩
  have exactData := p92ClassicalConstitutionRepresents_ext_localizedGraph
    source sourceGraph sourceRepresents
  refine ⟨fun atom => (atomZ atom).trans (exactData.1 atom),
    fun atom => (atomMass atom).trans (exactData.2.1 atom),
    fun atom => (charge atom).trans (exactData.2.2.1 atom), ?_⟩
  intro left right
  rw [bond left right]
  unfold p92CanonicalLocalizedMoleculeGraph
  change P92CanonicalRootBond sourceGraph center ligand left right =
    semanticP92CanonicalRootBond source.molecule.toLocalizedMoleculeGraph
      center ligand left right
  rw [semanticP92CanonicalRootBond_eq_reference]
  unfold P92CanonicalRootBond
  by_cases same : left = right
  · simp [same]
  · simp only [if_neg same]
    have rootEligibility : P92OxidoRootEligible sourceGraph center ligand ↔
        P92OxidoRootEligible source.molecule.toLocalizedMoleculeGraph center ligand := by
      simp only [P92OxidoRootEligible]
      rw [exactData.1 center, exactData.1 ligand, exactData.2.2.2 center ligand]
    by_cases sourceNormalized : P92RootPair center ligand left right ∧
        P92OxidoRootEligible sourceGraph center ligand
    · have localizedNormalized : P92RootPair center ligand left right ∧
          P92OxidoRootEligible source.molecule.toLocalizedMoleculeGraph center ligand :=
        ⟨sourceNormalized.1, rootEligibility.mp sourceNormalized.2⟩
      rw [if_pos sourceNormalized, if_pos localizedNormalized]
    · have localizedNotNormalized : ¬(P92RootPair center ligand left right ∧
          P92OxidoRootEligible source.molecule.toLocalizedMoleculeGraph center ligand) := by
        rintro ⟨rootPair, eligible⟩
        exact sourceNormalized ⟨rootPair, rootEligibility.mpr eligible⟩
      rw [if_neg sourceNormalized, if_neg localizedNotNormalized,
        exactData.2.2.2 left right]

private theorem moleculeGraph_eq_of_pointwise {vertex : Type} [Fintype vertex]
    [DecidableEq vertex]
    (left right : MoleculeGraph vertex)
    (atomZ : ∀ atom, left.atomZ atom = right.atomZ atom)
    (atomMass : ∀ atom, left.atomMass atom = right.atomMass atom)
    (charge : ∀ atom, left.formalCharge atom = right.formalCharge atom)
    (bond : ∀ first second, left.bond first second = right.bond first second) :
    left = right := by
  cases left with
  | mk leftZ leftMass leftCharge leftBond leftSymm leftSelf =>
      cases right with
      | mk rightZ rightMass rightCharge rightBond rightSymm rightSelf =>
          simp only at atomZ atomMass charge bond
          have atomZEq : leftZ = rightZ := funext atomZ
          have atomMassEq : leftMass = rightMass := funext atomMass
          have chargeEq : leftCharge = rightCharge := funext charge
          have bondEq : leftBond = rightBond := funext fun first => funext (bond first)
          subst rightZ
          subst rightMass
          subst rightCharge
          subst rightBond
          rfl

/-- On the canonical source atom index, every exact classical representation is definitionally
the direct executable localized semantic graph.  This is the mancude analogue of the normalized
canonical-graph equality below. -/
theorem p92ClassicalConstitutionRepresents_eq_localizedMoleculeGraph
    (source : AuthoritativeChemicalInput)
    (molecule : MoleculeGraph (Fin source.molecule.atomCount))
    (represented : P92ClassicalConstitutionRepresents source molecule) :
    molecule = source.molecule.toLocalizedMoleculeGraph := by
  rcases p92ClassicalConstitutionRepresents_ext_localizedGraph source molecule represented with
    ⟨atomZ, atomMass, charge, bond⟩
  exact moleculeGraph_eq_of_pointwise molecule source.molecule.toLocalizedMoleculeGraph
    atomZ atomMass charge bond

/-- The canonical constitutional graph is not merely pointwise unique: proof irrelevance and
function extensionality identify it with the fixed executable semantic normalization itself.  This
is the equality needed to substitute the fixed production graph for a reviewed representation
without copying a reviewed hierarchy. -/
theorem p92CanonicalConstitutionRepresents_eq_canonicalLocalizedMoleculeGraph
    (source : AuthoritativeChemicalInput)
    (center ligand : Fin source.molecule.atomCount)
    (canonical : MoleculeGraph (Fin source.molecule.atomCount))
    (represented : P92CanonicalConstitutionRepresents source center ligand canonical) :
    canonical = p92CanonicalLocalizedMoleculeGraph source center ligand := by
  rcases p92CanonicalConstitutionRepresents_unique source center ligand canonical represented with
    ⟨atomZ, atomMass, charge, bond⟩
  exact moleculeGraph_eq_of_pointwise canonical
    (p92CanonicalLocalizedMoleculeGraph source center ligand)
    atomZ atomMass charge bond

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92ClassicalConstitutionRepresents_localizedCIPGraphReady
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92ClassicalConstitutionRepresents_ext_localizedGraph
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.semanticP92CanonicalRootBond_eq_reference
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92CanonicalConstitutionRepresents_canonicalLocalizedMoleculeGraph
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92CanonicalConstitutionRepresents_unique
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92CanonicalConstitutionRepresents_eq_canonicalLocalizedMoleculeGraph
