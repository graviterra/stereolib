import TetraStereo.OneCenter.AuthoritativeSemanticMancudeDescriptorInvariance
import TetraStereo.OneCenter.AuthoritativeSemanticAromaticKekuleNormalization

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Source-indexed public tetrahedral analysis for aromatic/mancude inputs

An accepted Kekule realization is an implementation witness, not chemical input.  Consequently
center perception, ligand enumeration, coordinate lookup, and the public assignment carrier below
are all defined on the original semantic source.  The selected realization is used only by the
already proved canonical mancude key compiler.

This removes the dependent-type ambiguity that would otherwise arise when two normalized
candidates have propositionally equal atom counts but distinct proof carriers.  More importantly,
it makes the public theorem equality of complete emitted assignment lists indexed by source atom
identity.
-/

namespace AuthoritativeChemicalInput

abbrev AromaticCanonicalAtom (source : AuthoritativeChemicalInput) : Type :=
  Fin source.molecule.atomCount

/-- Source-level constitutional adjacency after replacing each declared aromatic pair by one real
edge.  Bond multiplicity is deliberately irrelevant to center perception. -/
def AromaticCanonicalAdjacent (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalAtom) : Prop :=
  left ≠ right ∧
    semanticEdgeKey left.val right.val ∈ source.molecule.aromaticNormalizedPairKeys

/-- All source-normalized constitutional neighbors of one atom. -/
noncomputable def aromaticCanonicalNeighborFinset (source : AuthoritativeChemicalInput)
    (center : source.AromaticCanonicalAtom) : Finset source.AromaticCanonicalAtom := by
  classical
  exact Finset.univ.filter (source.AromaticCanonicalAdjacent center)

@[simp] theorem mem_aromaticCanonicalNeighborFinset_iff
    (source : AuthoritativeChemicalInput)
    (center neighbor : source.AromaticCanonicalAtom) :
    neighbor ∈ source.aromaticCanonicalNeighborFinset center ↔
      source.AromaticCanonicalAdjacent center neighbor := by
  simp [aromaticCanonicalNeighborFinset]

/-! ## Connectivity-only tetrahedral applicability -/

/-- Periodic-table form of the ordinary connectivity-only tetrahedral element domain.  Using
atomic number makes this boundary independent of the parser's deliberately smaller `Element`
enumeration. -/
def ConnectivityOnlyTetrahedralPeriodicElement (element : PeriodicElement) : Prop :=
  element.atomicNumber ∈ [5, 6, 7, 8, 14, 15, 16, 32, 33, 34, 50, 51, 52, 82, 83]

instance (element : PeriodicElement) :
    Decidable (ConnectivityOnlyTetrahedralPeriodicElement element) := by
  unfold ConnectivityOnlyTetrahedralPeriodicElement
  infer_instance

/-- The exact source atom at a canonical index satisfies the independently enumerated
connectivity-only tetrahedral element boundary. -/
def ConnectivityOnlyTetrahedralCenterAtom (source : AuthoritativeChemicalInput)
    (center : source.AromaticCanonicalAtom) : Prop :=
  ConnectivityOnlyTetrahedralPeriodicElement
    (source.molecule.atoms.get center).element

/-- Source-fixed ordinary tetrahedral candidates: a permitted periodic element with exactly four
materialized canonical neighbours.  Three-coordinate phantom/lone-pair centers require a
separate configuration-evidence route and are intentionally absent here. -/
noncomputable def aromaticCanonicalTetrahedralCenterSet (source : AuthoritativeChemicalInput) :
    Finset source.AromaticCanonicalAtom := by
  classical
  exact Finset.univ.filter fun center =>
    source.ConnectivityOnlyTetrahedralCenterAtom center ∧
      (source.aromaticCanonicalNeighborFinset center).card = 4

@[simp] theorem mem_aromaticCanonicalTetrahedralCenterSet_iff
    (source : AuthoritativeChemicalInput) (center : source.AromaticCanonicalAtom) :
    center ∈ source.aromaticCanonicalTetrahedralCenterSet ↔
      source.ConnectivityOnlyTetrahedralCenterAtom center ∧
        (source.aromaticCanonicalNeighborFinset center).card = 4 := by
  classical
  change center ∈ Finset.univ.filter (fun candidate =>
    source.ConnectivityOnlyTetrahedralCenterAtom candidate ∧
      (source.aromaticCanonicalNeighborFinset candidate).card = 4) ↔ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

abbrev AromaticCanonicalTetrahedralCenter (source : AuthoritativeChemicalInput) : Type :=
  { center : source.AromaticCanonicalAtom //
    center ∈ source.aromaticCanonicalTetrahedralCenterSet }

/-- Deterministic source-index order for every canonical tetrahedral candidate. -/
noncomputable def aromaticCanonicalTetrahedralCenters (source : AuthoritativeChemicalInput) :
    List source.AromaticCanonicalTetrahedralCenter :=
  let sorted := source.aromaticCanonicalTetrahedralCenterSet.sort (· ≤ ·)
  sorted.attach.map fun center =>
    ⟨center.1, (Finset.mem_sort (r := (· ≤ ·))).mp center.2⟩

theorem mem_aromaticCanonicalTetrahedralCenters_iff
    (source : AuthoritativeChemicalInput)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    center ∈ source.aromaticCanonicalTetrahedralCenters ↔
      center.1 ∈ source.aromaticCanonicalTetrahedralCenterSet := by
  constructor
  · intro _present
    exact center.2
  · intro detected
    unfold aromaticCanonicalTetrahedralCenters
    rw [List.mem_map]
    let value : source.AromaticCanonicalAtom := center.1
    have sortedPresent :
        value ∈ source.aromaticCanonicalTetrahedralCenterSet.sort (· ≤ ·) :=
      (Finset.mem_sort (r := (· ≤ ·))).mpr detected
    refine ⟨⟨value, sortedPresent⟩, List.mem_attach _ _, ?_⟩
    exact Subtype.ext rfl

/-- Every public source-canonical tetrahedral center lies in the explicit periodic-element
applicability domain. -/
theorem aromaticCanonicalTetrahedralCenter_element_eligible
    (source : AuthoritativeChemicalInput)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    source.ConnectivityOnlyTetrahedralCenterAtom center.1 := by
  exact (source.mem_aromaticCanonicalTetrahedralCenterSet_iff center.1).mp center.2 |>.1

/-- Canonical ascending source-index ligand list. -/
noncomputable def aromaticCanonicalNeighborList (source : AuthoritativeChemicalInput)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    List source.AromaticCanonicalAtom :=
  (source.aromaticCanonicalNeighborFinset center.1).sort (· ≤ ·)

@[simp] theorem aromaticCanonicalNeighborList_length
    (source : AuthoritativeChemicalInput)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    (source.aromaticCanonicalNeighborList center).length = 4 := by
  rw [aromaticCanonicalNeighborList, Finset.length_sort]
  exact (source.mem_aromaticCanonicalTetrahedralCenterSet_iff center.1).mp center.2 |>.2

/-- The source atom at one of the four canonical ligand positions. -/
noncomputable def aromaticCanonicalLigandAtom (source : AuthoritativeChemicalInput)
    (center : source.AromaticCanonicalTetrahedralCenter) (index : Fin 4) :
    source.AromaticCanonicalAtom :=
  (source.aromaticCanonicalNeighborList center).get
    (Fin.cast (source.aromaticCanonicalNeighborList_length center).symm index)

theorem aromaticCanonicalLigandAtom_adjacent
    (source : AuthoritativeChemicalInput)
    (center : source.AromaticCanonicalTetrahedralCenter) (index : Fin 4) :
    source.AromaticCanonicalAdjacent center.1
      (source.aromaticCanonicalLigandAtom center index) := by
  apply (source.mem_aromaticCanonicalNeighborFinset_iff center.1
    (source.aromaticCanonicalLigandAtom center index)).mp
  apply (Finset.mem_sort (r := (· ≤ ·))).mp
  exact List.get_mem (source.aromaticCanonicalNeighborList center)
    (Fin.cast (source.aromaticCanonicalNeighborList_length center).symm index)

theorem aromaticCanonicalLigandAtom_ne_center
    (source : AuthoritativeChemicalInput)
    (center : source.AromaticCanonicalTetrahedralCenter) (index : Fin 4) :
    source.aromaticCanonicalLigandAtom center index ≠ center.1 :=
  (source.aromaticCanonicalLigandAtom_adjacent center index).1.symm

/-- The canonical four-ligand list contains no repeated source atom. -/
theorem aromaticCanonicalNeighborList_nodup
    (source : AuthoritativeChemicalInput)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    (source.aromaticCanonicalNeighborList center).Nodup := by
  exact Finset.sort_nodup _ _

/-- Distinct positions in the four-ligand frame denote distinct materialized source atoms. -/
theorem aromaticCanonicalLigandAtom_injective
    (source : AuthoritativeChemicalInput)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    Function.Injective (source.aromaticCanonicalLigandAtom center) := by
  intro left right atomEqual
  unfold aromaticCanonicalLigandAtom at atomEqual
  have castEqual :=
    (source.aromaticCanonicalNeighborList_nodup center).get_inj_iff.mp atomEqual
  have valuesEqual : left.val = right.val := by
    simpa using congrArg
      (fun index : Fin (source.aromaticCanonicalNeighborList center).length => index.val)
      castEqual
  exact Fin.ext valuesEqual

/-- Every source-normalized constitutional neighbour occurs in the canonical four-ligand frame. -/
theorem exists_aromaticCanonicalLigandAtom_eq_of_adjacent
    (source : AuthoritativeChemicalInput)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (neighbor : source.AromaticCanonicalAtom)
    (adjacent : source.AromaticCanonicalAdjacent center.1 neighbor) :
    ∃ index : Fin 4, source.aromaticCanonicalLigandAtom center index = neighbor := by
  have inFinset : neighbor ∈ source.aromaticCanonicalNeighborFinset center.1 :=
    (source.mem_aromaticCanonicalNeighborFinset_iff center.1 neighbor).mpr adjacent
  have inList : neighbor ∈ source.aromaticCanonicalNeighborList center := by
    exact (Finset.mem_sort (r := (· ≤ ·))).mpr inFinset
  obtain ⟨index, value⟩ := List.mem_iff_get.mp inList
  let position : Fin 4 :=
    Fin.cast (source.aromaticCanonicalNeighborList_length center) index
  refine ⟨position, ?_⟩
  simpa [aromaticCanonicalLigandAtom, position] using value

/-- Extensional finite-frame certificate for an ordinary connectivity-only source centre.  It
states the element boundary and identifies the canonical `Fin 4` frame bijectively with all
materialized source-normalized neighbours. -/
structure ConnectivityOnlyTetrahedralCenterEvidence
    (source : AuthoritativeChemicalInput)
    (center : source.AromaticCanonicalTetrahedralCenter) : Prop where
  elementEligible : source.ConnectivityOnlyTetrahedralCenterAtom center.1
  adjacent : ∀ index, source.AromaticCanonicalAdjacent center.1
    (source.aromaticCanonicalLigandAtom center index)
  ligandInjective : Function.Injective (source.aromaticCanonicalLigandAtom center)
  exhaustive : ∀ neighbor, source.AromaticCanonicalAdjacent center.1 neighbor →
    ∃ index, source.aromaticCanonicalLigandAtom center index = neighbor

/-- Every automatically perceived source centre carries the complete finite-frame evidence. -/
theorem aromaticCanonicalTetrahedralCenter_evidence
    (source : AuthoritativeChemicalInput)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    source.ConnectivityOnlyTetrahedralCenterEvidence center := by
  exact
    { elementEligible := source.aromaticCanonicalTetrahedralCenter_element_eligible center
      adjacent := source.aromaticCanonicalLigandAtom_adjacent center
      ligandInjective := source.aromaticCanonicalLigandAtom_injective center
      exhaustive := source.exists_aromaticCanonicalLigandAtom_eq_of_adjacent center }

/-- Source-fixed exact coordinate lookup. -/
def aromaticCanonicalSpatialPointAt? (source : AuthoritativeChemicalInput)
    (atom : source.AromaticCanonicalAtom) : Option CartesianPoint3 := do
  let spatial ← source.spatial?
  spatial.positions[atom.val]?

end AuthoritativeChemicalInput

namespace SemanticMolecule

/-- On any graph-ready semantic molecule, positive graph adjacency is exactly distinctness plus
membership of the unordered source pair key. -/
theorem toLocalizedMoleculeGraph_adj_iff_localizedCovalentKey
    (molecule : SemanticMolecule) (ready : molecule.LocalizedCIPGraphReady)
    (left right : Fin molecule.atomCount) :
    molecule.toLocalizedMoleculeGraph.Adj left right ↔
      left ≠ right ∧
        semanticEdgeKey left.val right.val ∈ molecule.localizedCovalentKeys := by
  constructor
  · intro adjacent
    have distinct : left ≠ right := by
      intro equality
      subst right
      simp [MoleculeGraph.Adj] at adjacent
    obtain ⟨order, recordPresent, _positive⟩ :=
      (molecule.toLocalizedMoleculeGraph_adj_iff_record ready left right distinct).mp adjacent
    refine ⟨distinct, ?_⟩
    rw [localizedCovalentKeys, List.mem_map]
    exact ⟨(semanticEdgeKey left.val right.val, order), recordPresent, rfl⟩
  · rintro ⟨distinct, keyPresent⟩
    rw [localizedCovalentKeys, List.mem_map] at keyPresent
    obtain ⟨record, recordPresent, recordKey⟩ := keyPresent
    rcases record with ⟨key, order⟩
    simp only at recordKey
    subst key
    apply (molecule.toLocalizedMoleculeGraph_adj_iff_record ready left right distinct).mpr
    exact ⟨order, recordPresent,
      molecule.localizedCovalentRecord_order_positive
        (semanticEdgeKey left.val right.val) order recordPresent⟩

/-- Reindex a source atom into a selected realization.  Selection preserves atom count. -/
def aromaticSelectionAtom (source : SemanticMolecule) (selection : List (Nat × Nat))
    (atom : Fin source.atomCount) :
    Fin (source.withAromaticKekuleSelection selection).atomCount :=
  Fin.cast (source.withAromaticKekuleSelection_atomCount selection).symm atom

@[simp] theorem aromaticSelectionAtom_val (source : SemanticMolecule)
    (selection : List (Nat × Nat)) (atom : Fin source.atomCount) :
    (source.aromaticSelectionAtom selection atom).val = atom.val := by
  rfl

end SemanticMolecule

namespace AuthoritativeChemicalInput

/-- Final canonical descriptor at a source-indexed center. -/
noncomputable def aromaticCanonicalSourceTetrahedralDescriptor? (source : AuthoritativeChemicalInput)
    (selection : List (Nat × Nat)) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) : Option RS :=
  source.molecule.aromaticCanonicalTetrahedralDescriptor? selection fuel
    (source.molecule.aromaticSelectionAtom selection center.1)
    (fun index => source.molecule.aromaticSelectionAtom selection
      (source.aromaticCanonicalLigandAtom center index))
    context
    (fun index => source.aromaticCanonicalSpatialPointAt?
      (source.aromaticCanonicalLigandAtom center index))

/-- Source-indexed final descriptors are exactly independent of the selected exact Kekule
realization. -/
theorem aromaticCanonicalSourceTetrahedralDescriptor?_kekule_invariant
    (source : AuthoritativeChemicalInput)
    (leftSelection rightSelection : List (Nat × Nat))
    (leftExact : source.molecule.SemanticAromaticMancudeEdgeSetExact
      (source.molecule.withAromaticKekuleSelection leftSelection))
    (rightExact : source.molecule.SemanticAromaticMancudeEdgeSetExact
      (source.molecule.withAromaticKekuleSelection rightSelection))
    (fuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) :
    source.aromaticCanonicalSourceTetrahedralDescriptor?
        leftSelection fuel center context =
      source.aromaticCanonicalSourceTetrahedralDescriptor?
        rightSelection fuel center context := by
  unfold aromaticCanonicalSourceTetrahedralDescriptor?
  exact source.molecule.aromaticCanonicalTetrahedralDescriptor?_kekule_invariant
    leftSelection rightSelection leftExact rightExact fuel
    (source.molecule.aromaticSelectionAtom leftSelection center.1)
    (fun index => source.molecule.aromaticSelectionAtom leftSelection
      (source.aromaticCanonicalLigandAtom center index))
    context
    (fun index => source.aromaticCanonicalSpatialPointAt?
      (source.aromaticCanonicalLigandAtom center index))

/-- Selection-free declarative meaning of a source-indexed canonical descriptor.  Every exact
realization must exhibit the same strict certificate order, direct source points, and exact
rational handedness judgment. -/
def DeclarativeAromaticCanonicalSourceTetrahedralDescriptor
    (source : AuthoritativeChemicalInput)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (descriptor : RS) : Prop :=
  ∀ selection,
    source.molecule.SemanticAromaticMancudeEdgeSetExact
        (source.molecule.withAromaticKekuleSelection selection) →
      CanonicalMancudeTetrahedral.DeclarativeSpatialDescriptor
        (source.molecule.compareAromaticCanonical? selection
          (source.molecule.atomCount + 1)
          (source.molecule.aromaticSelectionAtom selection center.1)
          (fun index => source.molecule.aromaticSelectionAtom selection
            (source.aromaticCanonicalLigandAtom center index))
          context)
        (fun index => source.aromaticCanonicalSpatialPointAt?
          (source.aromaticCanonicalLigandAtom center index)) descriptor

/-- Any executable descriptor from one exact realization satisfies the selection-free
declarative meaning for all exact realizations. -/
theorem aromaticCanonicalSourceTetrahedralDescriptor?_sound_declarative
    (source : AuthoritativeChemicalInput)
    (selection : List (Nat × Nat))
    (exact : source.molecule.SemanticAromaticMancudeEdgeSetExact
      (source.molecule.withAromaticKekuleSelection selection))
    (center : source.AromaticCanonicalTetrahedralCenter)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (descriptor : RS)
    (emitted : source.aromaticCanonicalSourceTetrahedralDescriptor?
      selection (source.molecule.atomCount + 1) center context = some descriptor) :
    source.DeclarativeAromaticCanonicalSourceTetrahedralDescriptor
      center context descriptor := by
  intro otherSelection otherExact
  have otherEmitted :
      source.aromaticCanonicalSourceTetrahedralDescriptor?
          otherSelection (source.molecule.atomCount + 1) center context = some descriptor := by
    rw [← source.aromaticCanonicalSourceTetrahedralDescriptor?_kekule_invariant
      selection otherSelection exact otherExact
      (source.molecule.atomCount + 1) center context]
    exact emitted
  unfold aromaticCanonicalSourceTetrahedralDescriptor? at otherEmitted
  exact CanonicalMancudeTetrahedral.spatialDescriptor?_sound _ _ descriptor otherEmitted

end AuthoritativeChemicalInput

/-- Public aromatic tetrahedral assignment, indexed only by the original source. -/
structure AromaticCanonicalTetrahedralSpatialAssignment
    (source : AuthoritativeChemicalInput) where
  center : source.AromaticCanonicalTetrahedralCenter
  descriptor : RS
  deriving DecidableEq

namespace CertifiedAuthoritativeSemanticAromaticKekuleNormalization

/-- Exact edge-set evidence restated at the generated selection rather than its bundled
candidate. -/
theorem selection_exact {source : AuthoritativeChemicalInput}
    (normalized : CertifiedAuthoritativeSemanticAromaticKekuleNormalization source) :
    source.molecule.SemanticAromaticMancudeEdgeSetExact
      (source.molecule.withAromaticKekuleSelection
        normalized.choice.selectedDoubleEdges) := by
  rw [← normalized.choice.candidate_eq]
  exact normalized.certificate.valid.2.2.2.1

/-- The selected graph's ordinary adjacency is exactly the source-normalized constitutional
adjacency.  In particular, changing which aromatic pairs are written double cannot create or
remove a perceived tetrahedral neighbor. -/
theorem selection_adj_iff_source_aromaticCanonicalAdjacent
    {source : AuthoritativeChemicalInput}
    (normalized : CertifiedAuthoritativeSemanticAromaticKekuleNormalization source)
    (left right : source.AromaticCanonicalAtom) :
    (source.molecule.withAromaticKekuleSelection
        normalized.choice.selectedDoubleEdges).toLocalizedMoleculeGraph.Adj
      (source.molecule.aromaticSelectionAtom
        normalized.choice.selectedDoubleEdges left)
      (source.molecule.aromaticSelectionAtom
        normalized.choice.selectedDoubleEdges right) ↔
      source.AromaticCanonicalAdjacent left right := by
  have ready :
      (source.molecule.withAromaticKekuleSelection
        normalized.choice.selectedDoubleEdges).LocalizedCIPGraphReady := by
    rw [← normalized.choice.candidate_eq]
    exact normalized.certificate.valid.2.1
  rw [(source.molecule.withAromaticKekuleSelection
      normalized.choice.selectedDoubleEdges
      ).toLocalizedMoleculeGraph_adj_iff_localizedCovalentKey ready]
  simp only [AuthoritativeChemicalInput.AromaticCanonicalAdjacent,
    source.molecule.withAromaticKekuleSelection_localizedCovalentKeys,
    SemanticMolecule.aromaticSelectionAtom_val]
  constructor
  · rintro ⟨different, edge⟩
    exact ⟨fun equality => different (by subst right; rfl), edge⟩
  · rintro ⟨different, edge⟩
    exact ⟨fun equality => different (Fin.ext (congrArg
      (fun atom : Fin (source.molecule.withAromaticKekuleSelection
        normalized.choice.selectedDoubleEdges).atomCount => atom.val) equality)), edge⟩

/-- Public canonical tetrahedral branch.  Perception and coordinates are source-fixed; only the
proved canonical compiler consumes the bundled realization witness. -/
noncomputable def analyzeAromaticCanonicalTetrahedralSpatial
    {source : AuthoritativeChemicalInput}
    (normalized : CertifiedAuthoritativeSemanticAromaticKekuleNormalization source)
    (context : source.AromaticCanonicalTetrahedralCenter → Fin 4 →
      CIPRuleEngine.OfficialLigandRuleContext) :
    List (AromaticCanonicalTetrahedralSpatialAssignment source) :=
  source.aromaticCanonicalTetrahedralCenters.filterMap fun center =>
    (source.aromaticCanonicalSourceTetrahedralDescriptor?
      normalized.choice.selectedDoubleEdges (source.molecule.atomCount + 1)
      center (context center)).map fun descriptor =>
        { center, descriptor }

/-- Exact output membership for the public canonical branch. -/
theorem mem_analyzeAromaticCanonicalTetrahedralSpatial_iff
    {source : AuthoritativeChemicalInput}
    (normalized : CertifiedAuthoritativeSemanticAromaticKekuleNormalization source)
    (context : source.AromaticCanonicalTetrahedralCenter → Fin 4 →
      CIPRuleEngine.OfficialLigandRuleContext)
    (assignment : AromaticCanonicalTetrahedralSpatialAssignment source) :
    assignment ∈ normalized.analyzeAromaticCanonicalTetrahedralSpatial context ↔
      source.aromaticCanonicalSourceTetrahedralDescriptor?
        normalized.choice.selectedDoubleEdges (source.molecule.atomCount + 1)
        assignment.center (context assignment.center) = some assignment.descriptor := by
  constructor
  · intro present
    rw [analyzeAromaticCanonicalTetrahedralSpatial, List.mem_filterMap] at present
    obtain ⟨center, _centerPresent, assignmentObserved⟩ := present
    cases descriptorObserved : source.aromaticCanonicalSourceTetrahedralDescriptor?
        normalized.choice.selectedDoubleEdges (source.molecule.atomCount + 1)
        center (context center) with
    | none => simp [descriptorObserved] at assignmentObserved
    | some descriptor =>
        simp [descriptorObserved] at assignmentObserved
        subst assignment
        exact descriptorObserved
  · intro emitted
    rw [analyzeAromaticCanonicalTetrahedralSpatial, List.mem_filterMap]
    refine ⟨assignment.center, ?_, ?_⟩
    · exact (source.mem_aromaticCanonicalTetrahedralCenters_iff assignment.center).mpr
        assignment.center.2
    · simp [emitted]

/-- Every descriptor in the public canonical aromatic branch has a source-level meaning that is
valid simultaneously for every exact Kekule realization. -/
theorem analyzeAromaticCanonicalTetrahedralSpatial_member_conforms
    {source : AuthoritativeChemicalInput}
    (normalized : CertifiedAuthoritativeSemanticAromaticKekuleNormalization source)
    (context : source.AromaticCanonicalTetrahedralCenter → Fin 4 →
      CIPRuleEngine.OfficialLigandRuleContext)
    (assignment : AromaticCanonicalTetrahedralSpatialAssignment source)
    (present : assignment ∈ normalized.analyzeAromaticCanonicalTetrahedralSpatial context) :
    source.DeclarativeAromaticCanonicalSourceTetrahedralDescriptor
      assignment.center (context assignment.center) assignment.descriptor := by
  apply source.aromaticCanonicalSourceTetrahedralDescriptor?_sound_declarative
    normalized.choice.selectedDoubleEdges normalized.selection_exact
  exact (normalized.mem_analyzeAromaticCanonicalTetrahedralSpatial_iff
    context assignment).mp present

/-- The complete public source-indexed assignment list is identical for any two certified exact
Kekule realizations of the same aromatic source. -/
theorem analyzeAromaticCanonicalTetrahedralSpatial_kekule_invariant
    {source : AuthoritativeChemicalInput}
    (left right : CertifiedAuthoritativeSemanticAromaticKekuleNormalization source)
    (context : source.AromaticCanonicalTetrahedralCenter → Fin 4 →
      CIPRuleEngine.OfficialLigandRuleContext) :
    left.analyzeAromaticCanonicalTetrahedralSpatial context =
      right.analyzeAromaticCanonicalTetrahedralSpatial context := by
  unfold analyzeAromaticCanonicalTetrahedralSpatial
  apply congrArg (fun emit => source.aromaticCanonicalTetrahedralCenters.filterMap emit)
  funext center
  rw [source.aromaticCanonicalSourceTetrahedralDescriptor?_kekule_invariant
    left.choice.selectedDoubleEdges right.choice.selectedDoubleEdges
    left.selection_exact right.selection_exact
    (source.molecule.atomCount + 1) center (context center)]

end CertifiedAuthoritativeSemanticAromaticKekuleNormalization

end TetraStereo.OneCenter
