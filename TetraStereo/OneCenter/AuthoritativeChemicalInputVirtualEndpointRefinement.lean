import TetraStereo.OneCenter.AuthoritativeChemicalInputVirtualEndpointEvidence

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Refining authoritative endpoint classifications into finite evidence

The finite evidence container should not force each input format to re-prove list bookkeeping.
This module enumerates every directed end of every canonical individual ordinary double bond and
proves that any total, shape-canonical endpoint classifier compiles to an unambiguous, covering
`CertifiedAuthoritativeChemicalInputWithVirtualEndpoints`.

The classifier is the chemical boundary.  A fully materialized representation can classify an
endpoint as `representedOnly`; a representation with an authoritative electron-state annotation
can classify a singleton endpoint as `oneLonePair` or `oneImplicitProtium`.  Shape alone cannot
choose between the latter two, and no theorem here pretends otherwise.
-/

/-- Independent meaning of a directed endpoint owned by an individual ordinary-double-bond
carrier. -/
def AromaticCanonicalIndividualDoubleBondDirectedEndpoint
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom) : Prop :=
  ∃ bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers,
    (endpoint = bond.left ∧ partner = bond.right) ∨
      (endpoint = bond.right ∧ partner = bond.left)

/-- Exhaustive finite directed-endpoint enumeration. -/
noncomputable def aromaticCanonicalIndividualDoubleBondDirectedEndpoints
    (source : AuthoritativeChemicalInput) :
    List (source.AromaticCanonicalAtom × source.AromaticCanonicalAtom) := by
  classical
  exact (source.aromaticCanonicalAtomUniverse ×ˢ source.aromaticCanonicalAtomUniverse).filter
    fun pair => decide
      (source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint pair.1 pair.2)

@[simp] theorem mem_aromaticCanonicalIndividualDoubleBondDirectedEndpoints_iff
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom) :
    (endpoint, partner) ∈ source.aromaticCanonicalIndividualDoubleBondDirectedEndpoints ↔
      source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint endpoint partner := by
  classical
  simp [aromaticCanonicalIndividualDoubleBondDirectedEndpoints]

theorem aromaticCanonicalIndividualDoubleBondDirectedEndpoints_nodup
    (source : AuthoritativeChemicalInput) :
    source.aromaticCanonicalIndividualDoubleBondDirectedEndpoints.Nodup := by
  classical
  exact (source.aromaticCanonicalAtomUniverse_nodup.product
    source.aromaticCanonicalAtomUniverse_nodup).filter _

private theorem aromaticCanonicalOrdinaryDoubleBond_symm
    (source : AuthoritativeChemicalInput)
    {left right : source.AromaticCanonicalAtom}
    (ordinary : source.AromaticCanonicalOrdinaryDoubleBond left right) :
    source.AromaticCanonicalOrdinaryDoubleBond right left := by
  have valuesDifferent : left.val ≠ right.val := by
    intro equal
    exact ordinary.1.1 (Fin.ext equal)
  exact ⟨⟨ordinary.1.1.symm, by
      simpa [semanticEdgeKey_comm] using ordinary.1.2⟩, by
    simpa [SemanticMolecule.aromaticCanonicalBondOrder,
      SemanticMolecule.localizedBondOrder, semanticEdgeKey_comm,
      valuesDifferent, valuesDifferent.symm] using ordinary.2⟩

/-- Every enumerated direction is an actual ordinary-double-bond direction. -/
theorem aromaticCanonicalOrdinaryDoubleBond_of_directedEndpoint
    (source : AuthoritativeChemicalInput)
    {endpoint partner : source.AromaticCanonicalAtom}
    (directed :
      source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint endpoint partner) :
    source.AromaticCanonicalOrdinaryDoubleBond endpoint partner := by
  rcases directed with ⟨bond, _present, forward | reverse⟩
  · rcases forward with ⟨rfl, rfl⟩
    exact bond.ordinary
  · rcases reverse with ⟨rfl, rfl⟩
    exact aromaticCanonicalOrdinaryDoubleBond_symm source bond.ordinary

/-- An authoritative classifier gives one completion for every directed individual-bond endpoint
and proves that the completion accounts for exactly the represented nonpartner positions. -/
structure AromaticCanonicalRule3EndpointClassifier
    (source : AuthoritativeChemicalInput) where
  classify : (endpoint partner : source.AromaticCanonicalAtom) →
    AromaticCanonicalRule3EndpointCompletion
  canonical : ∀ endpoint partner,
    source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint endpoint partner →
      source.CanonicalAromaticCanonicalRule3EndpointCompletion
        endpoint partner (classify endpoint partner)

/-- Compile a total endpoint classifier into the finite evidence format. -/
noncomputable def aromaticCanonicalRule3EndpointCompletionRecordsOfClassifier
    (source : AuthoritativeChemicalInput)
    (classifier : source.AromaticCanonicalRule3EndpointClassifier) :
    List source.AromaticCanonicalRule3EndpointCompletionRecord :=
  source.aromaticCanonicalIndividualDoubleBondDirectedEndpoints.map fun pair =>
    { endpoint := pair.1
      partner := pair.2
      completion := classifier.classify pair.1 pair.2 }

private theorem directedEndpointValueKey_injective
    (source : AuthoritativeChemicalInput) :
    Function.Injective
      (fun pair : source.AromaticCanonicalAtom × source.AromaticCanonicalAtom =>
        (pair.1.val, pair.2.val)) := by
  intro left right equal
  apply Prod.ext
  · apply Fin.ext
    exact congrArg Prod.fst equal
  · apply Fin.ext
    exact congrArg Prod.snd equal

/-- Compilation never creates duplicate directed endpoint keys. -/
theorem aromaticCanonicalRule3EndpointCompletionRecordsOfClassifier_keys_nodup
    (source : AuthoritativeChemicalInput)
    (classifier : source.AromaticCanonicalRule3EndpointClassifier) :
    ((source.aromaticCanonicalRule3EndpointCompletionRecordsOfClassifier classifier).map
      AromaticCanonicalRule3EndpointCompletionRecord.key).Nodup := by
  classical
  unfold aromaticCanonicalRule3EndpointCompletionRecordsOfClassifier
  rw [List.map_map]
  exact source.aromaticCanonicalIndividualDoubleBondDirectedEndpoints_nodup.map
    (directedEndpointValueKey_injective source)

/-- The compiled record list is structurally well formed. -/
theorem aromaticCanonicalRule3EndpointCompletionRecordsOfClassifier_wellFormed
    (source : AuthoritativeChemicalInput)
    (classifier : source.AromaticCanonicalRule3EndpointClassifier) :
    source.AromaticCanonicalRule3EndpointCompletionRecordsWellFormed
      (source.aromaticCanonicalRule3EndpointCompletionRecordsOfClassifier classifier) := by
  refine ⟨source.aromaticCanonicalRule3EndpointCompletionRecordsOfClassifier_keys_nodup
    classifier, ?_⟩
  intro record present
  rcases List.mem_map.mp present with ⟨pair, pairPresent, rfl⟩
  have directed :=
    (source.mem_aromaticCanonicalIndividualDoubleBondDirectedEndpoints_iff
      pair.1 pair.2).mp pairPresent
  exact ⟨source.aromaticCanonicalOrdinaryDoubleBond_of_directedEndpoint directed,
    classifier.canonical pair.1 pair.2 directed⟩

/-- The enriched input generated by a classifier. -/
noncomputable def withVirtualEndpointsOfClassifier
    (source : AuthoritativeChemicalInput)
    (classifier : source.AromaticCanonicalRule3EndpointClassifier) :
    AuthoritativeChemicalInputWithVirtualEndpoints :=
  { source := source
    endpointCompletions :=
      source.aromaticCanonicalRule3EndpointCompletionRecordsOfClassifier classifier }

/-- Its lookup returns exactly the classified completion at every directed endpoint. -/
theorem completionAt?_withVirtualEndpointsOfClassifier_eq_some
    (source : AuthoritativeChemicalInput)
    (classifier : source.AromaticCanonicalRule3EndpointClassifier)
    (endpoint partner : source.AromaticCanonicalAtom)
    (directed :
      source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint endpoint partner) :
    (source.withVirtualEndpointsOfClassifier classifier).completionAt? endpoint partner =
      some (classifier.classify endpoint partner) := by
  apply (source.aromaticCanonicalRule3EndpointCompletionLookup?_eq_some_iff
    (source.aromaticCanonicalRule3EndpointCompletionRecordsOfClassifier classifier)
    (source.aromaticCanonicalRule3EndpointCompletionRecordsOfClassifier_keys_nodup classifier)
    endpoint partner (classifier.classify endpoint partner)).mpr
  let record : source.AromaticCanonicalRule3EndpointCompletionRecord :=
    { endpoint := endpoint
      partner := partner
      completion := classifier.classify endpoint partner }
  refine ⟨record, ?_, rfl, rfl, rfl⟩
  apply List.mem_map.mpr
  exact ⟨(endpoint, partner),
    (source.mem_aromaticCanonicalIndividualDoubleBondDirectedEndpoints_iff
      endpoint partner).mpr directed, rfl⟩

/-- Classifier compilation covers both ends of every canonical individual bond. -/
theorem withVirtualEndpointsOfClassifier_coversCanonicalIndividualDoubleBonds
    (source : AuthoritativeChemicalInput)
    (classifier : source.AromaticCanonicalRule3EndpointClassifier) :
    (source.withVirtualEndpointsOfClassifier classifier).CoversCanonicalIndividualDoubleBonds := by
  intro bond present
  constructor
  · refine ⟨classifier.classify bond.left bond.right, ?_⟩
    apply source.completionAt?_withVirtualEndpointsOfClassifier_eq_some classifier
    exact ⟨bond, present, Or.inl ⟨rfl, rfl⟩⟩
  · refine ⟨classifier.classify bond.right bond.left, ?_⟩
    apply source.completionAt?_withVirtualEndpointsOfClassifier_eq_some classifier
    exact ⟨bond, present, Or.inr ⟨rfl, rfl⟩⟩

/-- The general representation-refinement theorem: a structurally valid source plus a total
canonical endpoint classifier produces the fully certified finite evidence object consumed by the
exact ordinary-double-bond pipeline. -/
noncomputable def certifiedWithVirtualEndpointsOfClassifier
    (source : AuthoritativeChemicalInput)
    (sourceWellFormed : source.StructurallyWellFormed)
    (classifier : source.AromaticCanonicalRule3EndpointClassifier) :
    CertifiedAuthoritativeChemicalInputWithVirtualEndpoints :=
  { input := source.withVirtualEndpointsOfClassifier classifier
    structurallyWellFormed := ⟨sourceWellFormed,
      source.aromaticCanonicalRule3EndpointCompletionRecordsOfClassifier_wellFormed classifier⟩
    coversCanonicalIndividualDoubleBonds :=
      source.withVirtualEndpointsOfClassifier_coversCanonicalIndividualDoubleBonds classifier }

/-! ## Fully materialized endpoint instance -/

/-- Every nonpartner position of every canonical individual ordinary-double-bond endpoint is a
represented atom.  This is the exact postcondition needed from an explicit-hydrogen materializer
on the fully represented alkene domain. -/
def FullyRepresentedCanonicalIndividualDoubleBondEndpoints
    (source : AuthoritativeChemicalInput) : Prop :=
  ∀ endpoint partner,
    source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint endpoint partner →
      (source.aromaticCanonicalRule3Substituents endpoint partner).length = 2

/-- The canonical classifier for a fully materialized endpoint domain. -/
def representedOnlyEndpointClassifier
    (source : AuthoritativeChemicalInput)
    (fullyRepresented : source.FullyRepresentedCanonicalIndividualDoubleBondEndpoints) :
    source.AromaticCanonicalRule3EndpointClassifier where
  classify := fun _endpoint _partner => .representedOnly
  canonical := by
    intro endpoint partner directed
    exact (source.canonicalEndpointCompletion_representedOnly_iff endpoint partner).mpr
      (fullyRepresented endpoint partner directed)

/-- A fully materialized, structurally valid source therefore needs no hand-written endpoint
record list: the certified finite evidence is constructed canonically. -/
noncomputable def certifiedWithRepresentedOnlyEndpoints
    (source : AuthoritativeChemicalInput)
    (sourceWellFormed : source.StructurallyWellFormed)
    (fullyRepresented : source.FullyRepresentedCanonicalIndividualDoubleBondEndpoints) :
    CertifiedAuthoritativeChemicalInputWithVirtualEndpoints :=
  source.certifiedWithVirtualEndpointsOfClassifier sourceWellFormed
    (source.representedOnlyEndpointClassifier fullyRepresented)

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
