import TetraStereo.OneCenter.LocalizedTetrahedralChemicalCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Source-record completeness of Rule 3 without localized double bonds

The restriction below is a fact about the actual semantic source records, not a successful
stereochemical computation. It excludes order two and permits order three. Within the already
certified localized graph domain, it makes every Rule-3 occurrence structural, independently of
the target, auxiliary state, expansion depth, or recursive reference frame. The resulting keys
have no geometrical observations, so their coupled topology is unambiguous.

This does not supply chemical admission, a strict ligand order, tetrahedral geometry, auxiliary
Rule-4/5 consensus, or normative source approval. Those boundaries remain separate.
-/

namespace SemanticMolecule

/-- No extracted localized covalent source record has order two. Triple bonds are permitted. -/
def NoLocalizedDoubleBondRecords (molecule : SemanticMolecule) : Prop :=
  ∀ record ∈ molecule.localizedCovalentRecords, record.2 ≠ 2

/-- Executable source-record test, before any occurrence expansion or descriptor evaluation. -/
def noLocalizedDoubleBondRecords? (molecule : SemanticMolecule) : Bool :=
  molecule.localizedCovalentRecords.all fun record => decide (record.2 ≠ 2)

@[simp] theorem noLocalizedDoubleBondRecords?_eq_true_iff
    (molecule : SemanticMolecule) :
    molecule.noLocalizedDoubleBondRecords? = true ↔
      molecule.NoLocalizedDoubleBondRecords := by
  simp [noLocalizedDoubleBondRecords?, NoLocalizedDoubleBondRecords]

/-- First-match source lookup cannot invent order two. No record uniqueness is needed. -/
theorem localizedBondOrderAtKey_ne_two_of_records
    (records : List ((Nat × Nat) × Nat)) (key : Nat × Nat)
    (noDouble : ∀ record ∈ records, record.2 ≠ 2) :
    localizedBondOrderAtKey records key ≠ 2 := by
  induction records with
  | nil => simp [localizedBondOrderAtKey]
  | cons head tail ih =>
      by_cases sameKey : head.1 = key
      · simpa [localizedBondOrderAtKey, sameKey] using noDouble head (by simp)
      · simpa [localizedBondOrderAtKey, sameKey] using
          ih (fun record present => noDouble record (by simp [present]))

/-- The source-record restriction rules out order two at every semantic atom pair. -/
theorem localizedBondOrder_ne_two_of_noDoubleRecords
    (molecule : SemanticMolecule)
    (noDouble : molecule.NoLocalizedDoubleBondRecords) (left right : Nat) :
    molecule.localizedBondOrder left right ≠ 2 := by
  by_cases same : left = right
  · simp [localizedBondOrder, same]
  · simpa [localizedBondOrder, same] using
      localizedBondOrderAtKey_ne_two_of_records molecule.localizedCovalentRecords
        (semanticEdgeKey left right) noDouble

end SemanticMolecule

namespace CertifiedLocalizedCIPInput

/-- Exact source-record restriction transported to the certified constitutional graph. -/
theorem moleculeGraph_bond_ne_two_of_noDoubleRecords
    (input : CertifiedLocalizedCIPInput)
    (noDouble : input.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (left right : input.Atom) :
    input.moleculeGraph.bond left right ≠ 2 := by
  exact input.certified.input.molecule.localizedBondOrder_ne_two_of_noDoubleRecords
    noDouble left.val right.val

/-- Every occurrence is a structural Rule-3 nonunit, including duplicates and rerooted nodes. -/
theorem localizedOccurrence_not_rule3DoubleBondEdge_of_noDoubleRecords
    (input : CertifiedLocalizedCIPInput)
    (noDouble : input.certified.input.molecule.NoLocalizedDoubleBondRecords)
    {carrierFuel : Nat} (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence := by
  rintro ⟨_real, current, parent, _current, _parent, doubleBond⟩
  exact input.moleculeGraph_bond_ne_two_of_noDoubleRecords noDouble parent current doubleBond

/-- Arbitrary-bound chemical classification is derived from source records, rather than assumed
as a premise about the complete recursive evaluator. -/
theorem localizedRule3ChemicalApplicabilityThrough_of_noDoubleRecords
    (input : CertifiedLocalizedCIPInput)
    (noDouble : input.certified.input.molecule.NoLocalizedDoubleBondRecords)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (maximumFuel : Nat) :
    input.LocalizedDescriptorBearingRule3ChemicalApplicabilityThrough
      target view maximumFuel := by
  intro fuel _bounded cursor _valid _covered
  have notEdge := input.localizedOccurrence_not_rule3DoubleBondEdge_of_noDoubleRecords
    noDouble cursor.occurrence
  cases fuel with
  | zero => exact notEdge
  | succ frameFuel =>
      by_cases shallow : frameFuel ≤ 2 * (carrierFuel + 1)
      · exact Or.inl ⟨shallow, .structural notEdge⟩
      · exact Or.inr ⟨by omega, .structural notEdge⟩

/-- All actually reachable descriptor-bearing node queries have derived support. -/
theorem localizedRule3ReachableSupportThrough_of_noDoubleRecords
    (input : CertifiedLocalizedCIPInput)
    (noDouble : input.certified.input.molecule.NoLocalizedDoubleBondRecords)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (maximumFuel : Nat) :
    input.LocalizedDescriptorBearingRule3ReachableSupportThrough target view maximumFuel :=
  (input.localizedRule3ChemicalApplicabilityThrough_of_noDoubleRecords
    noDouble target view maximumFuel).reachableSupport input target view

/-- The existing recursion resolves its outer option at every valid budget-covered query. -/
theorem localizedRule3ReachableResolvedThrough_of_noDoubleRecords
    (input : CertifiedLocalizedCIPInput)
    (noDouble : input.certified.input.molecule.NoLocalizedDoubleBondRecords)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (maximumFuel : Nat) :
    input.LocalizedDescriptorBearingRule3ReachableResolvedThrough target view maximumFuel :=
  (input.localizedRule3ReachableSupportThrough_of_noDoubleRecords
    noDouble target view maximumFuel).resolved input target view

private theorem noDouble_node_observation_eq_none
    (input : CertifiedLocalizedCIPInput)
    (noDouble : input.certified.input.molecule.NoLocalizedDoubleBondRecords)
    {carrierFuel : Nat} {target occurrence : input.LocalizedCIPOccurrence carrierFuel}
    {view : input.LocalizedDependencyView target}
    {meaning : input.LocalizedRule3FrameMeaning carrierFuel}
    {excluded : List input.LocalizedRule3PhysicalUnitId}
    {observation : Option input.LocalizedRule3SpatialNodeResult}
    (derived : input.DeclarativeLocalizedDescriptorBearingRule3NodeWith
      target view meaning excluded occurrence observation) : observation = none := by
  have notEdge := input.localizedOccurrence_not_rule3DoubleBondEdge_of_noDoubleRecords
    noDouble occurrence
  cases derived <;> first
    | rfl
    | exact (notEdge ‹input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence›).elim

private theorem noDouble_foldl_observation_lengths_eq_zero
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (empty : ∀ key ∈ keys, key.observations = []) :
    keys.foldl (fun longest child => max longest child.observations.length) 0 = 0 := by
  induction keys with
  | nil => rfl
  | cons head tail ih =>
      have headEmpty := empty head (by simp)
      simp [headEmpty]
      exact ih (fun key present => empty key (by simp [present]))

private theorem noDouble_merge_observations_eq_nil
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (empty : ∀ key ∈ keys, key.observations = []) :
    input.mergeLocalizedRerootRule3ObservationChildren keys = [] := by
  unfold mergeLocalizedRerootRule3ObservationChildren
  rw [show input.localizedRerootRule3ObservationChildLayerCount keys = 0 by
    exact noDouble_foldl_observation_lengths_eq_zero input keys empty]
  rfl

private theorem noDouble_forall₂_right_property
    {α β : Type*} {R : α → β → Prop} {P : β → Prop}
    (complete : ∀ a b, R a b → P b) {as : List α} {bs : List β}
    (derived : List.Forall₂ R as bs) : ∀ b ∈ bs, P b := by
  induction derived with
  | nil => simp
  | cons head tail ih =>
      intro b present
      rcases List.mem_cons.mp present with rfl | present
      · exact complete _ _ head
      · exact ih b present

/-- Independent recursive key derivations retain no geometric observations on this source domain. -/
theorem declarativeLocalizedDescriptorBearingRule3Key_observations_nil_of_noDoubleRecords
    (input : CertifiedLocalizedCIPInput)
    (noDouble : input.certified.input.molecule.NoLocalizedDoubleBondRecords)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ fuel excluded cursor key,
      input.DeclarativeLocalizedRerootDescriptorBearingRule3Key
        target view fuel excluded cursor key → key.observations = [] := by
  intro fuel
  induction fuel with
  | zero =>
      intro excluded cursor key derived
      rcases derived with ⟨children, _children, _terminal, _notEdge, rfl⟩
      rfl
  | succ fuel ih =>
      intro excluded cursor key derived
      rcases derived with ⟨children, observation, _children, observed, terminal | recursive⟩
      · obtain ⟨_terminal, rfl⟩ := terminal
        have observationEmpty := noDouble_node_observation_eq_none input noDouble observed
        simp [observationEmpty, localizedRule3SpatialRootObservations]
      · rcases recursive with
          ⟨childKeys, sorted, _nonterminal, childrenDerived, permutation, _descending, rfl⟩
        have observationEmpty := noDouble_node_observation_eq_none input noDouble observed
        have childrenEmpty : ∀ child ∈ childKeys, child.observations = [] :=
          noDouble_forall₂_right_property (fun cursor key derivation =>
            ih excluded cursor key derivation) childrenDerived
        have sortedEmpty : ∀ child ∈ sorted, child.observations = [] := by
          intro child present
          exact childrenEmpty child (permutation.mem_iff.mp present)
        simp only [observationEmpty, localizedRule3SpatialRootObservations, List.nil_append]
        exact noDouble_merge_observations_eq_nil input sorted sortedEmpty

/-- Actual successful descriptor-bearing compilation has empty observations, by independent
recursive soundness rather than an assumption about its result. -/
theorem buildLocalizedDescriptorBearingRule3Key_observations_nil_of_noDoubleRecords
    (input : CertifiedLocalizedCIPInput)
    (noDouble : input.certified.input.molecule.NoLocalizedDoubleBondRecords)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (fuel : Nat)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootRecursiveRule3SpatialKey)
    (computed : input.buildLocalizedRerootDescriptorBearingRule3Key?
      target view fuel excluded cursor = some key) : key.observations = [] :=
  input.declarativeLocalizedDescriptorBearingRule3Key_observations_nil_of_noDoubleRecords
    noDouble target view fuel excluded cursor key
    (input.buildLocalizedRerootDescriptorBearingRule3Key?_sound
      target view fuel excluded cursor key computed)

private theorem noDouble_mapM_outputs_property
    {α β : Type*} (f : α → Option β) (P : β → Prop)
    (complete : ∀ a b, f a = some b → P b) :
    ∀ as bs, (as : List α).mapM f = some bs → ∀ b ∈ bs, P b
  | [], bs, computed => by
      simp at computed
      subst bs
      simp
  | a :: as, bs, computed => by
      rw [List.mapM_cons] at computed
      cases headComputed : f a with
      | none => simp [headComputed] at computed
      | some b =>
          cases tailComputed : as.mapM f with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst bs
              intro output present
              rcases List.mem_cons.mp present with rfl | present
              · exact complete a output headComputed
              · exact noDouble_mapM_outputs_property f P complete as tail tailComputed
                  output present

/-- No physical units can occur in the successful raw pass. -/
theorem localizedRule3FramePhysicalUnits_nil_of_noDoubleRecords
    (input : CertifiedLocalizedCIPInput)
    (noDouble : input.certified.input.molecule.NoLocalizedDoubleBondRecords)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (fuel : Nat)
    (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (rawKeys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (computed : cursors.mapM
      (input.buildLocalizedRerootDescriptorBearingRule3Key? target view fuel []) =
        some rawKeys) : input.localizedRule3FramePhysicalUnits rawKeys = [] := by
  have empty : ∀ key ∈ rawKeys, key.observations = [] :=
    noDouble_mapM_outputs_property
      (input.buildLocalizedRerootDescriptorBearingRule3Key? target view fuel [])
      (fun key => key.observations = [])
      (fun cursor key computed =>
        input.buildLocalizedDescriptorBearingRule3Key_observations_nil_of_noDoubleRecords
          noDouble target view fuel [] cursor key computed) cursors rawKeys computed
  have noMembers : ∀ unit, unit ∉ input.localizedRule3FramePhysicalUnits rawKeys := by
    intro unit present
    rcases (input.mem_localizedRule3FramePhysicalUnits_iff rawKeys unit).mp present with
      ⟨key, keyPresent, layer, layerPresent, _entry, _entryPresent, _identity⟩
    rw [empty key keyPresent] at layerPresent
    simp at layerPresent
  cases observed : input.localizedRule3FramePhysicalUnits rawKeys with
  | nil => rfl
  | cons unit units =>
      exact (noMembers unit (by rw [observed]; simp)).elim

/-- Coupled-topology applicability follows from empty actual observations at every positive
frame index. Zero fuel remains a structural refusal of the frame compiler. -/
theorem localizedRule3FrameDeclarativelyUnambiguous_of_noDoubleRecords
    (input : CertifiedLocalizedCIPInput)
    (noDouble : input.certified.input.molecule.NoLocalizedDoubleBondRecords)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (fuel : Nat)
    (positive : 0 < fuel) (cursors : List (input.LocalizedRerootCursor carrierFuel)) :
    input.LocalizedDescriptorBearingRule3FrameDeclarativelyUnambiguous
      target view fuel cursors := by
  cases fuel with
  | zero => omega
  | succ keyFuel =>
      intro rawKeys computed left right leftDerived _rightDerived
      have unitsEmpty := input.localizedRule3FramePhysicalUnits_nil_of_noDoubleRecords
        noDouble target view keyFuel cursors rawKeys computed
      have impossible := leftDerived.1
      rw [unitsEmpty] at impossible
      simp at impossible

/-- The existing conservative descriptor-bearing frame compiler is total on valid cursors;
source records discharge both recursive chemical support and coupled-topology premises. -/
theorem exists_buildLocalizedDescriptorBearingRule3Frame_of_noDoubleRecords
    (input : CertifiedLocalizedCIPInput)
    (noDouble : input.certified.input.molecule.NoLocalizedDoubleBondRecords)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (valid : ∀ cursor ∈ cursors, input.LocalizedRerootCursorValid cursor) :
    ∃ frame, input.buildLocalizedDescriptorBearingRule3Frame? target view
      (localizedDescriptorBearingRule3EvaluationFuel carrierFuel) cursors = some frame := by
  apply input.exists_buildLocalizedDescriptorBearingRule3Frame?_at_conservativeFuel_declarative
    target view
    (input.localizedRule3ReachableResolvedThrough_of_noDoubleRecords noDouble target view _)
    cursors
  · apply input.localizedRule3FrameDeclarativelyUnambiguous_of_noDoubleRecords
      noDouble target view
    unfold localizedDescriptorBearingRule3EvaluationFuel
    positivity
  · exact valid

/-- For an independently meaningful four-ligand frame, the actual cumulative Rules-1a--5
compiler succeeds without separate Rule-3 chemical classification or topology premises. -/
theorem exists_buildLocalizedOccurrenceDescriptorBearingRule3Through5KeyFrame_of_noDoubleRecords
    (input : CertifiedLocalizedCIPInput)
    (noDouble : input.certified.input.molecule.NoLocalizedDoubleBondRecords)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (baseMeaning : input.DeclarativeLocalizedOccurrenceFourLigandFrame target base) :
    ∃ keys, input.buildLocalizedOccurrenceDescriptorBearingRule3Through5KeyFrame?
      target view base = some keys := by
  apply input.exists_buildLocalizedOccurrenceDescriptorBearingRule3Through5KeyFrame_of_chemical
    target view base baseMeaning
  · exact input.localizedRule3ChemicalApplicabilityThrough_of_noDoubleRecords
      noDouble target view _
  · apply input.localizedRule3FrameDeclarativelyUnambiguous_of_noDoubleRecords
      noDouble target view
    unfold localizedDescriptorBearingRule3EvaluationFuel
    positivity

end CertifiedLocalizedCIPInput

namespace LocalizedNoDoubleRule3Examples

/-- Nonunique source records and order three do not compromise the no-order-two lookup fact. -/
theorem repeatedTripleRecord_lookup :
    SemanticMolecule.localizedBondOrderAtKey [((0, 1), 3), ((0, 1), 3)] (0, 1) = 3 := by
  decide

theorem repeatedTripleRecord_noDouble :
    SemanticMolecule.localizedBondOrderAtKey [((0, 1), 3), ((0, 1), 3)] (0, 1) ≠ 2 := by
  decide

theorem actualDoubleRecord_lookup :
    SemanticMolecule.localizedBondOrderAtKey [((0, 1), 2)] (0, 1) = 2 := by
  decide

end LocalizedNoDoubleRule3Examples
end TetraStereo.OneCenter
