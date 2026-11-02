import TetraStereo.OneCenter.RawExtendedTetrahedralCarrierFrameDisjointness
import TetraStereo.OneCenter.AuthoritativeSemanticMancudePublicTetrahedralAnalysis
import TetraStereo.OneCenter.P92StereogenicUnitSemantics
import TetraStereo.OneCenter.ProductionCIPRule1aGraphRealization

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Parser-to-semantic ordinary tetrahedral element applicability

The parser and the representation-complete semantic molecule deliberately state their ordinary
connectivity-only tetrahedral element domains independently.  This file proves that the checked
parser-to-semantic conversion preserves and reflects that boundary.  It is a representation
conformance theorem, not a claim that element identity and four neighbours alone establish a
stereogenic centre.
-/

namespace Element

/-- Successful conversion preserves the exact atomic number of every parser element. -/
theorem toPeriodic?_atomicNumber
    (element : Element) (periodic : PeriodicElement)
    (converted : element.toPeriodic? = some periodic) :
    periodic.atomicNumber = element.atomicNumber := by
  cases element <;>
    simp [Element.toPeriodic?, PeriodicElement.ofAtomicNumber?, Element.atomicNumber] at converted
  all_goals
    subst periodic
    rfl

end Element

/-- The independently stated parser predicate and the all-periodic-elements semantic predicate
select exactly the same element after checked conversion. -/
theorem connectivityOnlyTetrahedralElement_toPeriodic_iff
    (element : Element) (periodic : PeriodicElement)
    (converted : element.toPeriodic? = some periodic) :
    AuthoritativeChemicalInput.ConnectivityOnlyTetrahedralPeriodicElement periodic ↔
      BlueBookP92.Perception.ConnectivityOnlyTetrahedralElement element := by
  have atomicNumber := Element.toPeriodic?_atomicNumber element periodic converted
  unfold AuthoritativeChemicalInput.ConnectivityOnlyTetrahedralPeriodicElement
  rw [atomicNumber]
  cases element <;>
    simp [Element.atomicNumber,
      BlueBookP92.Perception.ConnectivityOnlyTetrahedralElement]

/-- Atom conversion preserves and reflects the ordinary tetrahedral element boundary.  Atom
metadata such as isotope, charge, aromatic spelling, and parity cannot change this applicability
decision. -/
theorem connectivityOnlyTetrahedralElement_toSemanticAtom_iff
    (spec : AtomSpec) (atom : SemanticAtom)
    (converted : spec.toSemanticAtom? = some atom) :
    AuthoritativeChemicalInput.ConnectivityOnlyTetrahedralPeriodicElement atom.element ↔
      BlueBookP92.Perception.ConnectivityOnlyTetrahedralElement spec.element := by
  unfold AtomSpec.toSemanticAtom? at converted
  cases periodicObserved : spec.element.toPeriodic? with
  | none => simp [periodicObserved] at converted
  | some periodic =>
      simp only [periodicObserved, Option.bind_eq_bind, Option.bind_some] at converted
      have atomEqual :
          ({ element := periodic
             isotopeMassNumber? := spec.isotope?
             formalCharge := spec.charge
             aromaticInput := spec.aromatic } : SemanticAtom) = atom :=
        Option.some.inj converted
      subst atom
      exact connectivityOnlyTetrahedralElement_toPeriodic_iff
        spec.element periodic periodicObserved

/-! ## Atom-index preservation -/

/-- The same numerical atom index transported across a successful parser-to-semantic conversion.
The atom-count theorem proves that this cast is total; no fallback index is introduced. -/
def RawMolecule.convertedAtomIndex
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (atom : Fin molecule.atomCount) : Fin source.molecule.atomCount :=
  Fin.cast (molecule.toSemanticMolecule?_atomCount source.molecule converted).symm atom

@[simp] theorem RawMolecule.convertedAtomIndex_val
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (atom : Fin molecule.atomCount) :
    (molecule.convertedAtomIndex source converted atom).val = atom.val := by
  rfl

/-- Transporting atom indices through one successful conversion is injective. -/
theorem RawMolecule.convertedAtomIndex_injective
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule) :
    Function.Injective (molecule.convertedAtomIndex source converted) := by
  exact Fin.cast_injective
    (molecule.toSemanticMolecule?_atomCount source.molecule converted).symm

/-- The semantic atom at a transported center satisfies the semantic ordinary-tetrahedral
element boundary exactly when the parser atom at that center satisfies the independent parser
boundary. -/
theorem RawMolecule.convertedCenterAtom_element_iff
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (center : Fin molecule.atomCount) (spec : AtomSpec)
    (atomAt : molecule.atomAt? center.val = some spec) :
    source.ConnectivityOnlyTetrahedralCenterAtom
        (molecule.convertedAtomIndex source converted center) ↔
      BlueBookP92.Perception.ConnectivityOnlyTetrahedralElement spec.element := by
  have indexed := molecule.toSemanticMolecule?_atomAt?
    source.molecule converted center.val
  rw [atomAt] at indexed
  simp only [Option.bind_some] at indexed
  have semanticLookup := listGet?_eq_some_get source.molecule.atoms
    (molecule.convertedAtomIndex source converted center)
  have atomConverted :
      spec.toSemanticAtom? = some
        (source.molecule.atoms.get
          (molecule.convertedAtomIndex source converted center)) := by
    rw [← indexed]
    simpa using semanticLookup
  unfold AuthoritativeChemicalInput.ConnectivityOnlyTetrahedralCenterAtom
  exact connectivityOnlyTetrahedralElement_toSemanticAtom_iff
    spec (source.molecule.atoms.get
      (molecule.convertedAtomIndex source converted center)) atomConverted

/-! ## Constitutional edge preservation -/

/-- Exact single-bond boundary of the parser bridge.  Every resolved parser bond kind crosses as
the same unordered constitutional pair; an unresolved `unspecified` bond remains visible as
`unspecifiedCovalent` and is deliberately refused by the source-normalized pair extractor. -/
@[simp] theorem RawBond.aromaticNormalizedPairKey?_toSemanticInteraction
    (bond : RawBond) :
    SemanticMolecule.aromaticNormalizedPairKey? bond.toSemanticInteraction =
      if bond.kind = .unspecified then none
      else some (semanticEdgeKey bond.source bond.target) := by
  rcases bond with ⟨source, target, kind⟩
  cases kind <;>
    simp [RawBond.toSemanticInteraction,
      SemanticMolecule.aromaticNormalizedPairKey?,
      SemanticMolecule.aromaticPairEdge?,
      SemanticInteraction.localizedCovalentRecord?]

/-- Successful parser-to-semantic molecule conversion has an exact fail-closed constitutional
edge image: precisely unresolved `unspecified` records are omitted from the normalized pair-key
list, and no other bond is dropped or invented. -/
theorem RawMolecule.toSemanticMolecule?_aromaticNormalizedPairKeys
    (molecule : RawMolecule) (semantic : SemanticMolecule)
    (converted : molecule.toSemanticMolecule? = some semantic) :
    semantic.aromaticNormalizedPairKeys =
      molecule.bonds.filterMap fun bond =>
        if bond.kind = .unspecified then none
        else some (semanticEdgeKey bond.source bond.target) := by
  unfold RawMolecule.toSemanticMolecule? at converted
  cases atomsObserved : molecule.semanticAtoms? with
  | none => simp [atomsObserved] at converted
  | some atoms =>
      simp only [atomsObserved, Option.bind_eq_bind, Option.bind_some,
        Option.some.injEq] at converted
      subst semantic
      rw [SemanticMolecule.aromaticNormalizedPairKeys, List.filterMap_map]
      change molecule.bonds.filterMap (fun bond =>
          SemanticMolecule.aromaticNormalizedPairKey? bond.toSemanticInteraction) = _
      induction molecule.bonds with
      | nil => rfl
      | cons bond bonds inductionHypothesis =>
          simp [RawBond.aromaticNormalizedPairKey?_toSemanticInteraction]

/-- Once ordinary normalization has resolved every unspecified bond, conversion preserves the
entire ordered constitutional pair-key list without qualification. -/
theorem RawMolecule.toSemanticMolecule?_aromaticNormalizedPairKeys_of_noUnspecified
    (molecule : RawMolecule) (semantic : SemanticMolecule)
    (converted : molecule.toSemanticMolecule? = some semantic)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified) :
    semantic.aromaticNormalizedPairKeys =
      molecule.bonds.map fun bond => semanticEdgeKey bond.source bond.target := by
  rw [molecule.toSemanticMolecule?_aromaticNormalizedPairKeys semantic converted]
  have filterMapEq : ∀ bonds : List RawBond,
      (∀ bond, bond ∈ bonds → bond.kind ≠ .unspecified) →
        bonds.filterMap (fun bond =>
            if bond.kind = .unspecified then none
            else some (semanticEdgeKey bond.source bond.target)) =
          bonds.map fun bond => semanticEdgeKey bond.source bond.target := by
    intro bonds allResolved
    induction bonds with
    | nil => rfl
    | cons bond bonds inductionHypothesis =>
        have headResolved : bond.kind ≠ .unspecified :=
          allResolved bond (by simp)
        have tailResolved : ∀ item, item ∈ bonds → item.kind ≠ .unspecified := by
          intro item present
          exact allResolved item (by simp [present])
        simp [headResolved, inductionHypothesis tailResolved]
  exact filterMapEq molecule.bonds resolved

-- Keep `distinct` explicit for source-compatible named applications of this public theorem.
set_option linter.unusedVariables false in
/-- Equality of unordered endpoint keys is exactly undirected raw-bond incidence when the queried
endpoints are distinct. -/
theorem RawBond.semanticEdgeKey_eq_iff_connects
    (bond : RawBond) (left right : Nat) (distinct : left ≠ right) :
    semanticEdgeKey bond.source bond.target = semanticEdgeKey left right ↔
      bond.connects left right = true := by
  rcases bond with ⟨source, target, kind⟩
  simp only [semanticEdgeKey, RawBond.connects, Bool.or_eq_true,
    Bool.and_eq_true, beq_iff_eq]
  by_cases sourceTarget : source ≤ target <;>
    by_cases leftRight : left ≤ right <;>
      simp [Nat.min_def, Nat.max_def, sourceTarget, leftRight] <;> omega

/-- Raw constitutional pair-key membership is exactly existence of an incident bond record. -/
theorem RawMolecule.semanticEdgeKey_mem_bondKeyList_iff
    (molecule : RawMolecule) (left right : Nat) (distinct : left ≠ right) :
    semanticEdgeKey left right ∈
        molecule.bonds.map (fun bond => semanticEdgeKey bond.source bond.target) ↔
      ∃ bond ∈ molecule.bonds, bond.connects left right = true := by
  rw [List.mem_map]
  constructor
  · rintro ⟨bond, present, keyEqual⟩
    exact ⟨bond, present,
      (bond.semanticEdgeKey_eq_iff_connects left right distinct).mp keyEqual⟩
  · rintro ⟨bond, present, connects⟩
    exact ⟨bond, present,
      (bond.semanticEdgeKey_eq_iff_connects left right distinct).mpr connects⟩

/-- Full constitutional perception bridge at every real atom pair.  Under written-neighbour
exactness and resolved bond kinds, parser written-neighbour membership is equivalent to membership
of the same unordered edge in the semantic source-normalized graph. -/
theorem RawMolecule.writtenNeighbor_mem_iff_semanticAromaticNormalizedPairKey_mem
    (molecule : RawMolecule) (semantic : SemanticMolecule)
    (converted : molecule.toSemanticMolecule? = some semantic)
    (writtenExact : molecule.WrittenNeighborExact)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (center neighbor : Fin molecule.atomCount) (distinct : center ≠ neighbor) :
    neighbor.val ∈ molecule.writtenNeighbors center.val ↔
      semanticEdgeKey center.val neighbor.val ∈ semantic.aromaticNormalizedPairKeys := by
  have indexDistinct : center.val ≠ neighbor.val := by
    intro equal
    exact distinct (Fin.ext equal)
  have keysEqual :=
    molecule.toSemanticMolecule?_aromaticNormalizedPairKeys_of_noUnspecified
      semantic converted resolved
  calc
    neighbor.val ∈ molecule.writtenNeighbors center.val ↔
        0 < molecule.bondOrder center.val neighbor.val :=
      (RawMolecule.WrittenNeighborExact.at molecule writtenExact center).2.2 neighbor
    _ ↔ ∃ bond ∈ molecule.bonds, bond.connects center.val neighbor.val = true :=
      RawMolecule.bondOrder_pos_iff_exists_bond molecule indexDistinct
    _ ↔ semanticEdgeKey center.val neighbor.val ∈
          molecule.bonds.map (fun bond => semanticEdgeKey bond.source bond.target) :=
      (molecule.semanticEdgeKey_mem_bondKeyList_iff
        center.val neighbor.val indexDistinct).symm
    _ ↔ semanticEdgeKey center.val neighbor.val ∈
          semantic.aromaticNormalizedPairKeys := by rw [keysEqual]

/-- Exact adjacency preservation after transporting both endpoint indices.  Unlike the lower-level
pair-key theorem, this statement needs no distinctness premise: written-neighbour exactness proves
that a listed neighbor cannot be the center itself, while semantic adjacency carries distinctness
as part of its definition. -/
theorem RawMolecule.writtenNeighbor_mem_iff_convertedAromaticCanonicalAdjacent
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (writtenExact : molecule.WrittenNeighborExact)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (center neighbor : Fin molecule.atomCount) :
    neighbor.val ∈ molecule.writtenNeighbors center.val ↔
      source.AromaticCanonicalAdjacent
        (molecule.convertedAtomIndex source converted center)
        (molecule.convertedAtomIndex source converted neighbor) := by
  constructor
  · intro present
    have positive : 0 < molecule.bondOrder center.val neighbor.val :=
      ((RawMolecule.WrittenNeighborExact.at molecule writtenExact center).2.2 neighbor).mp present
    have distinct : center ≠ neighbor := by
      intro equal
      subst neighbor
      rw [molecule.bondOrder_self center.val] at positive
      exact (Nat.not_lt_zero 0) positive
    have keyPresent :=
      (molecule.writtenNeighbor_mem_iff_semanticAromaticNormalizedPairKey_mem
        source.molecule converted writtenExact resolved center neighbor distinct).mp present
    refine ⟨?_, ?_⟩
    · intro semanticEqual
      exact distinct
        ((molecule.convertedAtomIndex_injective source converted) semanticEqual)
    simpa using keyPresent
  · rintro ⟨semanticDistinct, keyPresent⟩
    have distinct : center ≠ neighbor := by
      intro equal
      apply semanticDistinct
      exact congrArg (molecule.convertedAtomIndex source converted) equal
    apply (molecule.writtenNeighbor_mem_iff_semanticAromaticNormalizedPairKey_mem
      source.molecule converted writtenExact resolved center neighbor distinct).mpr
    simpa using keyPresent

/-! ## Complete four-neighbor frame preservation -/

/-- Parser-side graph-only ordinary tetrahedral frame.  The element domain and exactly four
materialized neighbors are stated independently of the semantic center detector.  Exclusion of an
extended-tetrahedral parity carrier is kept as a separate parser annotation condition below. -/
def RawMolecule.ConnectivityOnlyTetrahedralGraphFrameAt
    (molecule : RawMolecule) (center : Fin molecule.atomCount) : Prop :=
  ∃ spec,
    molecule.atomAt? center.val = some spec ∧
      BlueBookP92.Perception.ConnectivityOnlyTetrahedralElement spec.element ∧
      (molecule.writtenNeighbors center.val).length = 4

/-- Full parser-side ordinary frame, including the explicit exclusion of an extended-tetrahedral
parity carrier used by production perception. -/
def RawMolecule.OrdinaryConnectivityOnlyTetrahedralFrameAt
    (molecule : RawMolecule) (center : Fin molecule.atomCount) : Prop :=
  molecule.ConnectivityOnlyTetrahedralGraphFrameAt center ∧
    molecule.isExtendedTetrahedralParityCarrier center.val = false

/-- For a four-neighbor graph frame the production extended-carrier exclusion is automatic, so
the graph-only and full ordinary parser predicates are extensionally equal. -/
theorem RawMolecule.connectivityOnlyTetrahedralGraphFrameAt_iff_ordinaryFrameAt
    (molecule : RawMolecule) (center : Fin molecule.atomCount) :
    molecule.ConnectivityOnlyTetrahedralGraphFrameAt center ↔
      molecule.OrdinaryConnectivityOnlyTetrahedralFrameAt center := by
  constructor
  · intro frame
    refine ⟨frame, ?_⟩
    rcases frame with ⟨_spec, _atomAt, _elementEligible, four⟩
    exact molecule.isExtendedTetrahedralParityCarrier_eq_false_of_writtenNeighbors_length_eq_four
      center.val four
  · exact And.left

/-- The local `Fin`-indexed full ordinary frame is exactly the independent production-perception
predicate when both are applied to the same parsed molecule. -/
theorem RawMolecule.ordinaryConnectivityOnlyTetrahedralFrameAt_iff_blueBookFrame
    (molecule : RawMolecule) (result : ChemistryNormalizationResult)
    (parsed : result.parsed = molecule) (center : Fin molecule.atomCount) :
    molecule.OrdinaryConnectivityOnlyTetrahedralFrameAt center ↔
      BlueBookP92.Perception.ConnectivityOnlyTetrahedralFrame
        result molecule center.val := by
  unfold RawMolecule.OrdinaryConnectivityOnlyTetrahedralFrameAt
    RawMolecule.ConnectivityOnlyTetrahedralGraphFrameAt
    BlueBookP92.Perception.ConnectivityOnlyTetrahedralFrame
  constructor
  · rintro ⟨⟨spec, atomAt, elementEligible, four⟩, notExtended⟩
    refine ⟨spec, ?_, elementEligible, notExtended, four⟩
    simpa [parsed] using atomAt
  · rintro ⟨spec, atomAt, elementEligible, notExtended, four⟩
    refine ⟨⟨spec, ?_, elementEligible, four⟩, notExtended⟩
    simpa [parsed] using atomAt

/-- Exact finite-degree preservation.  The proof constructs a bijection rather than comparing two
Boolean counts: every duplicate-free parser neighbor maps to the same semantic atom index, and
the adjacency equivalence proves both image membership and surjectivity. -/
theorem RawMolecule.writtenNeighbor_length_eq_convertedAromaticCanonicalNeighbor_card
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (writtenExact : molecule.WrittenNeighborExact)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (center : Fin molecule.atomCount) :
    (molecule.writtenNeighbors center.val).length =
      (source.aromaticCanonicalNeighborFinset
        (molecule.convertedAtomIndex source converted center)).card := by
  classical
  let rawNeighbors : Finset ℕ :=
    (molecule.writtenNeighbors center.val).toFinset
  have exactAt := RawMolecule.WrittenNeighborExact.at molecule writtenExact center
  have rawCard : rawNeighbors.card = (molecule.writtenNeighbors center.val).length := by
    simpa [rawNeighbors] using List.toFinset_card_of_nodup exactAt.1
  have cardEqual : rawNeighbors.card =
      (source.aromaticCanonicalNeighborFinset
        (molecule.convertedAtomIndex source converted center)).card := by
    apply Finset.card_bij
      (fun neighbor present =>
        molecule.convertedAtomIndex source converted
          ⟨neighbor, exactAt.2.1 neighbor (by simpa [rawNeighbors] using present)⟩)
    · intro neighbor present
      let rawNeighbor : Fin molecule.atomCount :=
        ⟨neighbor, exactAt.2.1 neighbor (by simpa [rawNeighbors] using present)⟩
      apply (source.mem_aromaticCanonicalNeighborFinset_iff
        (molecule.convertedAtomIndex source converted center) _).mpr
      change source.AromaticCanonicalAdjacent
        (molecule.convertedAtomIndex source converted center)
        (molecule.convertedAtomIndex source converted rawNeighbor)
      apply (molecule.writtenNeighbor_mem_iff_convertedAromaticCanonicalAdjacent
        source converted writtenExact resolved center rawNeighbor).mp
      simpa [rawNeighbors] using present
    · intro left leftPresent right rightPresent equal
      exact congrArg Fin.val equal
    · intro semanticNeighbor semanticPresent
      let rawNeighbor : Fin molecule.atomCount :=
        Fin.cast (molecule.toSemanticMolecule?_atomCount source.molecule converted)
          semanticNeighbor
      have adjacency : source.AromaticCanonicalAdjacent
          (molecule.convertedAtomIndex source converted center) semanticNeighbor :=
        (source.mem_aromaticCanonicalNeighborFinset_iff
          (molecule.convertedAtomIndex source converted center) semanticNeighbor).mp
          semanticPresent
      have returned :
          molecule.convertedAtomIndex source converted rawNeighbor = semanticNeighbor := by
        apply Fin.ext
        rfl
      have written : rawNeighbor.val ∈ molecule.writtenNeighbors center.val :=
        (molecule.writtenNeighbor_mem_iff_convertedAromaticCanonicalAdjacent
          source converted writtenExact resolved center rawNeighbor).mpr (by
            simpa [returned] using adjacency)
      have rawPresent : rawNeighbor.val ∈ rawNeighbors := by
        simpa [rawNeighbors] using written
      refine ⟨rawNeighbor.val, rawPresent, ?_⟩
      apply Fin.ext
      rfl
  rw [← cardEqual, rawCard]

/-- Complete parser-to-semantic applicability equivalence for the graph-only ordinary
tetrahedral boundary.  This proves both preservation and reflection: no four-neighbor candidate is
dropped, and no candidate is invented by semantic conversion. -/
theorem RawMolecule.connectivityOnlyTetrahedralGraphFrameAt_iff_convertedCenter_mem
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (writtenExact : molecule.WrittenNeighborExact)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (center : Fin molecule.atomCount) :
    molecule.ConnectivityOnlyTetrahedralGraphFrameAt center ↔
      molecule.convertedAtomIndex source converted center ∈
        source.aromaticCanonicalTetrahedralCenterSet := by
  rw [source.mem_aromaticCanonicalTetrahedralCenterSet_iff]
  constructor
  · rintro ⟨spec, atomAt, elementEligible, four⟩
    refine ⟨(molecule.convertedCenterAtom_element_iff
      source converted center spec atomAt).mpr elementEligible, ?_⟩
    rw [← molecule.writtenNeighbor_length_eq_convertedAromaticCanonicalNeighbor_card
      source converted writtenExact resolved center]
    exact four
  · rintro ⟨elementEligible, four⟩
    obtain ⟨spec, atomAt⟩ := listGet?_exists_of_lt
      molecule.atoms center.val center.isLt
    refine ⟨spec, ?_, ?_, ?_⟩
    · simpa [RawMolecule.atomAt?] using atomAt
    · apply (molecule.convertedCenterAtom_element_iff source converted center spec
        (by simpa [RawMolecule.atomAt?] using atomAt)).mp
      exact elementEligible
    · rw [molecule.writtenNeighbor_length_eq_convertedAromaticCanonicalNeighbor_card
        source converted writtenExact resolved center]
      exact four

/-- End-to-end ordinary-center applicability equivalence across the current parser, production
perception boundary, and representation-complete semantic source detector.  The theorem includes
the extended-carrier exclusion because the recognizer-disjointness theorem proves it is automatic
at a four-neighbor frame. -/
theorem RawMolecule.ordinaryConnectivityOnlyTetrahedralFrameAt_iff_convertedCenter_mem
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (writtenExact : molecule.WrittenNeighborExact)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (center : Fin molecule.atomCount) :
    molecule.OrdinaryConnectivityOnlyTetrahedralFrameAt center ↔
      molecule.convertedAtomIndex source converted center ∈
        source.aromaticCanonicalTetrahedralCenterSet := by
  rw [← molecule.connectivityOnlyTetrahedralGraphFrameAt_iff_ordinaryFrameAt center]
  exact molecule.connectivityOnlyTetrahedralGraphFrameAt_iff_convertedCenter_mem
    source converted writtenExact resolved center

/-! ## Written-order to canonical-frame permutation -/

/-- One of the four parser-written neighbors, transported to the semantic atom-index type without
changing its parser position. -/
noncomputable def RawMolecule.convertedWrittenTetrahedralLigandAtom
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (writtenExact : molecule.WrittenNeighborExact)
    (center : Fin molecule.atomCount)
    (four : (molecule.writtenNeighbors center.val).length = 4)
    (position : Fin 4) : source.AromaticCanonicalAtom :=
  let rawPosition : Fin (molecule.writtenNeighbors center.val).length :=
    Fin.cast four.symm position
  let rawValue := (molecule.writtenNeighbors center.val).get rawPosition
  let rawAtom : Fin molecule.atomCount :=
    ⟨rawValue,
      (RawMolecule.WrittenNeighborExact.at molecule writtenExact center).2.1 rawValue
        (List.get_mem _ rawPosition)⟩
  molecule.convertedAtomIndex source converted rawAtom

@[simp] theorem RawMolecule.convertedWrittenTetrahedralLigandAtom_val
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (writtenExact : molecule.WrittenNeighborExact)
    (center : Fin molecule.atomCount)
    (four : (molecule.writtenNeighbors center.val).length = 4)
    (position : Fin 4) :
    (molecule.convertedWrittenTetrahedralLigandAtom
      source converted writtenExact center four position).val =
      (molecule.writtenNeighbors center.val).get (Fin.cast four.symm position) := by
  rfl

/-- Every transported written-order slot is a semantic source neighbor of the transported center. -/
theorem RawMolecule.convertedWrittenTetrahedralLigandAtom_adjacent
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (writtenExact : molecule.WrittenNeighborExact)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (center : Fin molecule.atomCount)
    (four : (molecule.writtenNeighbors center.val).length = 4)
    (position : Fin 4) :
    source.AromaticCanonicalAdjacent
      (molecule.convertedAtomIndex source converted center)
      (molecule.convertedWrittenTetrahedralLigandAtom
        source converted writtenExact center four position) := by
  let rawPosition : Fin (molecule.writtenNeighbors center.val).length :=
    Fin.cast four.symm position
  let rawValue := (molecule.writtenNeighbors center.val).get rawPosition
  let rawAtom : Fin molecule.atomCount :=
    ⟨rawValue,
      (RawMolecule.WrittenNeighborExact.at molecule writtenExact center).2.1 rawValue
        (List.get_mem _ rawPosition)⟩
  have written : rawAtom.val ∈ molecule.writtenNeighbors center.val := by
    exact List.get_mem _ rawPosition
  have adjacent :=
    (molecule.writtenNeighbor_mem_iff_convertedAromaticCanonicalAdjacent
      source converted writtenExact resolved center rawAtom).mp written
  simpa [RawMolecule.convertedWrittenTetrahedralLigandAtom,
    rawPosition, rawValue, rawAtom] using adjacent

/-- Distinct parser positions denote distinct transported semantic ligands. -/
theorem RawMolecule.convertedWrittenTetrahedralLigandAtom_injective
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (writtenExact : molecule.WrittenNeighborExact)
    (center : Fin molecule.atomCount)
    (four : (molecule.writtenNeighbors center.val).length = 4) :
    Function.Injective (molecule.convertedWrittenTetrahedralLigandAtom
      source converted writtenExact center four) := by
  intro left right atomEqual
  have valueEqual := congrArg Fin.val atomEqual
  simp only [molecule.convertedWrittenTetrahedralLigandAtom_val] at valueEqual
  have rawPositionEqual : Fin.cast four.symm left = Fin.cast four.symm right :=
    (RawMolecule.WrittenNeighborExact.at molecule writtenExact center).1.get_inj_iff.mp
      valueEqual
  exact Fin.cast_injective four.symm rawPositionEqual

/-- The four transported parser slots exhaust all semantic source neighbors at the transported
center. -/
theorem RawMolecule.exists_convertedWrittenTetrahedralLigandAtom_eq_of_adjacent
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (writtenExact : molecule.WrittenNeighborExact)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (center : Fin molecule.atomCount)
    (four : (molecule.writtenNeighbors center.val).length = 4)
    (neighbor : source.AromaticCanonicalAtom)
    (adjacent : source.AromaticCanonicalAdjacent
      (molecule.convertedAtomIndex source converted center) neighbor) :
    ∃ position : Fin 4,
      molecule.convertedWrittenTetrahedralLigandAtom
        source converted writtenExact center four position = neighbor := by
  let rawNeighbor : Fin molecule.atomCount :=
    Fin.cast (molecule.toSemanticMolecule?_atomCount source.molecule converted) neighbor
  have returned : molecule.convertedAtomIndex source converted rawNeighbor = neighbor := by
    apply Fin.ext
    rfl
  have written : rawNeighbor.val ∈ molecule.writtenNeighbors center.val :=
    (molecule.writtenNeighbor_mem_iff_convertedAromaticCanonicalAdjacent
      source converted writtenExact resolved center rawNeighbor).mpr (by
        simpa [returned] using adjacent)
  obtain ⟨rawPosition, valueEqual⟩ := List.mem_iff_get.mp written
  let position : Fin 4 := Fin.cast four rawPosition
  refine ⟨position, ?_⟩
  apply Fin.ext
  simpa [RawMolecule.convertedWrittenTetrahedralLigandAtom, position] using valueEqual

/-- Any transported written-order four-frame and the semantic canonical four-frame differ by one
genuine permutation of `Fin 4`.  The inverse is constructed from the two exhaustiveness theorems;
the two injectivity theorems prove its inverse laws. -/
theorem RawMolecule.exists_convertedWrittenToCanonicalPermutation
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (writtenExact : molecule.WrittenNeighborExact)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (center : Fin molecule.atomCount)
    (four : (molecule.writtenNeighbors center.val).length = 4)
    (semanticCenter : source.AromaticCanonicalTetrahedralCenter)
    (centerEqual : semanticCenter.val =
      molecule.convertedAtomIndex source converted center) :
    ∃ permutation : Equiv.Perm (Fin 4), ∀ position,
      molecule.convertedWrittenTetrahedralLigandAtom
          source converted writtenExact center four position =
        source.aromaticCanonicalLigandAtom semanticCenter (permutation position) := by
  classical
  let writtenLigand : Fin 4 → source.AromaticCanonicalAtom :=
    molecule.convertedWrittenTetrahedralLigandAtom
      source converted writtenExact center four
  let canonicalLigand : Fin 4 → source.AromaticCanonicalAtom :=
    source.aromaticCanonicalLigandAtom semanticCenter
  have writtenAdjacent : ∀ position,
      source.AromaticCanonicalAdjacent semanticCenter.val (writtenLigand position) := by
    intro position
    simpa [writtenLigand, centerEqual] using
      molecule.convertedWrittenTetrahedralLigandAtom_adjacent
        source converted writtenExact resolved center four position
  have canonicalAdjacent : ∀ position,
      source.AromaticCanonicalAdjacent semanticCenter.val (canonicalLigand position) := by
    intro position
    exact source.aromaticCanonicalLigandAtom_adjacent semanticCenter position
  let toFun : Fin 4 → Fin 4 := fun position =>
    Classical.choose
      (source.exists_aromaticCanonicalLigandAtom_eq_of_adjacent
        semanticCenter (writtenLigand position) (writtenAdjacent position))
  have toFun_spec : ∀ position, canonicalLigand (toFun position) = writtenLigand position := by
    intro position
    exact Classical.choose_spec
      (source.exists_aromaticCanonicalLigandAtom_eq_of_adjacent
        semanticCenter (writtenLigand position) (writtenAdjacent position))
  let invFun : Fin 4 → Fin 4 := fun position =>
    Classical.choose
      (molecule.exists_convertedWrittenTetrahedralLigandAtom_eq_of_adjacent
        source converted writtenExact resolved center four
        (canonicalLigand position) (by
          simpa [← centerEqual] using canonicalAdjacent position))
  have invFun_spec : ∀ position, writtenLigand (invFun position) = canonicalLigand position := by
    intro position
    exact Classical.choose_spec
      (molecule.exists_convertedWrittenTetrahedralLigandAtom_eq_of_adjacent
        source converted writtenExact resolved center four
        (canonicalLigand position) (by
          simpa [← centerEqual] using canonicalAdjacent position))
  let permutation : Equiv.Perm (Fin 4) :=
    { toFun := toFun
      invFun := invFun
      left_inv := by
        intro position
        apply molecule.convertedWrittenTetrahedralLigandAtom_injective
          source converted writtenExact center four
        exact (invFun_spec (toFun position)).trans (toFun_spec position)
      right_inv := by
        intro position
        apply source.aromaticCanonicalLigandAtom_injective semanticCenter
        exact (toFun_spec (invFun position)).trans (invFun_spec position) }
  refine ⟨permutation, ?_⟩
  intro position
  exact (toFun_spec position).symm

/-- End-to-end ordered-frame bridge for every admitted ordinary parser center.  Besides the
genuine `S₄` permutation, the result retains an exact lookup equation showing that slot `i` is the
atom stored at written-neighbor position `i`; the theorem therefore does not silently replace
parser order by sorted semantic order. -/
theorem RawMolecule.ordinaryFrame_exists_writtenToCanonicalPermutation
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (writtenExact : molecule.WrittenNeighborExact)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (center : Fin molecule.atomCount)
    (frame : molecule.OrdinaryConnectivityOnlyTetrahedralFrameAt center) :
    ∃ (semanticCenter : source.AromaticCanonicalTetrahedralCenter)
      (four : (molecule.writtenNeighbors center.val).length = 4)
      (permutation : Equiv.Perm (Fin 4)),
      semanticCenter.val = molecule.convertedAtomIndex source converted center ∧
        (∀ position,
          listGet? (molecule.writtenNeighbors center.val) position.val =
            some (molecule.convertedWrittenTetrahedralLigandAtom
              source converted writtenExact center four position).val) ∧
        ∀ position,
          molecule.convertedWrittenTetrahedralLigandAtom
              source converted writtenExact center four position =
            source.aromaticCanonicalLigandAtom semanticCenter (permutation position) := by
  rcases frame.1 with ⟨_spec, _atomAt, _elementEligible, four⟩
  have centerMember :=
    (molecule.ordinaryConnectivityOnlyTetrahedralFrameAt_iff_convertedCenter_mem
      source converted writtenExact resolved center).mp frame
  let semanticCenter : source.AromaticCanonicalTetrahedralCenter :=
    ⟨molecule.convertedAtomIndex source converted center, centerMember⟩
  obtain ⟨permutation, permutationEq⟩ :=
    molecule.exists_convertedWrittenToCanonicalPermutation
      source converted writtenExact resolved center four semanticCenter rfl
  refine ⟨semanticCenter, four, permutation, rfl, ?_, permutationEq⟩
  intro position
  have lookup := listGet?_eq_some_get
    (molecule.writtenNeighbors center.val) (Fin.cast four.symm position)
  simpa using lookup

end TetraStereo.OneCenter
