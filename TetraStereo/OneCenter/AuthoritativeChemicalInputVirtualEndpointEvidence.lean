import TetraStereo.OneCenter.AuthoritativeSemanticOrdinaryDoubleBondVirtualEndpointExactReadiness

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Enriched authoritative input for omitted endpoint positions

`AuthoritativeChemicalInput` deliberately stores atoms and interactions rather than a
serialization-specific implicit-hydrogen convention.  Consequently its existing fields cannot
distinguish an omitted protium, a lone pair, and an intentionally absent position in a charged or
radical species.

This module adds that missing information as a finite, directed endpoint-evidence layer without
changing the base molecule type.  Structural certification checks that records are unambiguous,
refer to actual canonical ordinary-double-bond endpoints, and account for exactly two nonpartner
positions.  Coverage certification requires both directions of every canonical individual bond.
The chemical choice between implicit H and lone pair remains evidence, just like supplied spatial
coordinates; the kernel checks all consequences and all finite consistency conditions.
-/

namespace AuthoritativeChemicalInput

/-- One directed endpoint-completion assertion. -/
structure AromaticCanonicalRule3EndpointCompletionRecord
    (source : AuthoritativeChemicalInput) where
  endpoint : source.AromaticCanonicalAtom
  partner : source.AromaticCanonicalAtom
  completion : AromaticCanonicalRule3EndpointCompletion
  deriving DecidableEq

namespace AromaticCanonicalRule3EndpointCompletionRecord

def key {source : AuthoritativeChemicalInput}
    (record : source.AromaticCanonicalRule3EndpointCompletionRecord) : ℕ × ℕ :=
  (record.endpoint.val, record.partner.val)

end AromaticCanonicalRule3EndpointCompletionRecord

/-- Exact finite lookup.  The proposition-valued equality test makes the definition
noncomputable, but every returned value is still reduced and checked by the kernel. -/
noncomputable def aromaticCanonicalRule3EndpointCompletionLookup?
    (source : AuthoritativeChemicalInput)
    (records : List source.AromaticCanonicalRule3EndpointCompletionRecord)
    (endpoint partner : source.AromaticCanonicalAtom) :
    Option AromaticCanonicalRule3EndpointCompletion :=
  match records with
  | [] => none
  | record :: rest =>
      if record.endpoint = endpoint ∧ record.partner = partner then
        some record.completion
      else
        source.aromaticCanonicalRule3EndpointCompletionLookup? rest endpoint partner

/-- Lookup succeeds exactly when a matching record occurs in the finite evidence list. -/
theorem aromaticCanonicalRule3EndpointCompletionLookup?_eq_some_iff
    (source : AuthoritativeChemicalInput)
    (records : List source.AromaticCanonicalRule3EndpointCompletionRecord)
    (uniqueKeys :
      (records.map AromaticCanonicalRule3EndpointCompletionRecord.key).Nodup)
    (endpoint partner : source.AromaticCanonicalAtom)
    (completion : AromaticCanonicalRule3EndpointCompletion) :
    source.aromaticCanonicalRule3EndpointCompletionLookup?
        records endpoint partner = some completion ↔
      ∃ record ∈ records,
        record.endpoint = endpoint ∧ record.partner = partner ∧
          record.completion = completion := by
  induction records with
  | nil => simp [aromaticCanonicalRule3EndpointCompletionLookup?]
  | cons record rest inductionHypothesis =>
      simp only [List.map_cons, List.nodup_cons] at uniqueKeys
      obtain ⟨headFresh, tailUnique⟩ := uniqueKeys
      by_cases matched : record.endpoint = endpoint ∧ record.partner = partner
      · rcases matched with ⟨endpointEq, partnerEq⟩
        subst endpoint
        subst partner
        simp only [aromaticCanonicalRule3EndpointCompletionLookup?, and_self,
          ↓reduceIte, Option.some.injEq]
        constructor
        · intro completionEq
          exact ⟨record, List.mem_cons_self, rfl, rfl, completionEq⟩
        · rintro ⟨witness, present, endpointEq, partnerEq, completionEq⟩
          rcases List.mem_cons.mp present with rfl | tailPresent
          · exact completionEq
          · exfalso
            apply headFresh
            exact List.mem_map.mpr ⟨witness, tailPresent, by
              simp [AromaticCanonicalRule3EndpointCompletionRecord.key,
                endpointEq, partnerEq]⟩
      · rw [aromaticCanonicalRule3EndpointCompletionLookup?, if_neg matched,
          inductionHypothesis tailUnique]
        constructor
        · rintro ⟨witness, present, endpointEq, partnerEq, completionEq⟩
          exact ⟨witness, List.mem_cons_of_mem _ present,
            endpointEq, partnerEq, completionEq⟩
        · rintro ⟨witness, present, endpointEq, partnerEq, completionEq⟩
          rcases List.mem_cons.mp present with rfl | tailPresent
          · exact False.elim (matched ⟨endpointEq, partnerEq⟩)
          · exact ⟨witness, tailPresent, endpointEq, partnerEq, completionEq⟩

/-- Structural validity of the finite endpoint evidence. -/
def AromaticCanonicalRule3EndpointCompletionRecordsWellFormed
    (source : AuthoritativeChemicalInput)
    (records : List source.AromaticCanonicalRule3EndpointCompletionRecord) : Prop :=
  (records.map AromaticCanonicalRule3EndpointCompletionRecord.key).Nodup ∧
    ∀ record, record ∈ records →
      source.AromaticCanonicalOrdinaryDoubleBond record.endpoint record.partner ∧
        source.CanonicalAromaticCanonicalRule3EndpointCompletion
          record.endpoint record.partner record.completion

/-- A well-formed record lookup always returns a completion with the exact endpoint shape. -/
theorem aromaticCanonicalRule3EndpointCompletionLookup?_canonical
    (source : AuthoritativeChemicalInput)
    (records : List source.AromaticCanonicalRule3EndpointCompletionRecord)
    (wellFormed : source.AromaticCanonicalRule3EndpointCompletionRecordsWellFormed records)
    (endpoint partner : source.AromaticCanonicalAtom)
    (completion : AromaticCanonicalRule3EndpointCompletion)
    (lookedUp : source.aromaticCanonicalRule3EndpointCompletionLookup?
      records endpoint partner = some completion) :
    source.AromaticCanonicalOrdinaryDoubleBond endpoint partner ∧
      source.CanonicalAromaticCanonicalRule3EndpointCompletion
        endpoint partner completion := by
  obtain ⟨record, present, endpointEq, partnerEq, completionEq⟩ :=
    (source.aromaticCanonicalRule3EndpointCompletionLookup?_eq_some_iff
      records wellFormed.1 endpoint partner completion).mp lookedUp
  subst endpoint
  subst partner
  subst completion
  exact wellFormed.2 record present

end AuthoritativeChemicalInput

/-- Format-neutral chemical input enriched with finite endpoint-position evidence. -/
structure AuthoritativeChemicalInputWithVirtualEndpoints where
  source : AuthoritativeChemicalInput
  endpointCompletions :
    List source.AromaticCanonicalRule3EndpointCompletionRecord

namespace AuthoritativeChemicalInputWithVirtualEndpoints

/-- Structural certification preserves the base source certificate and validates every completion
record and directed key. -/
def StructurallyWellFormed
    (input : AuthoritativeChemicalInputWithVirtualEndpoints) : Prop :=
  input.source.StructurallyWellFormed ∧
    input.source.AromaticCanonicalRule3EndpointCompletionRecordsWellFormed
      input.endpointCompletions

/-- Completion lookup exported in the shape required by the virtual-aware analyzer. -/
noncomputable def completionAt?
    (input : AuthoritativeChemicalInputWithVirtualEndpoints) :
    input.source.AromaticCanonicalRule3EndpointCompletionMap :=
  input.source.aromaticCanonicalRule3EndpointCompletionLookup? input.endpointCompletions

/-- Every canonical individual bond has evidence for both directed endpoints. -/
def CoversCanonicalIndividualDoubleBonds
    (input : AuthoritativeChemicalInputWithVirtualEndpoints) : Prop :=
  ∀ bond ∈ input.source.aromaticCanonicalIndividualDoubleBondCarriers,
    (∃ leftCompletion, input.completionAt? bond.left bond.right = some leftCompletion) ∧
      (∃ rightCompletion, input.completionAt? bond.right bond.left = some rightCompletion)

/-- Lookup from a structurally certified enriched input is shape-canonical. -/
theorem completionAt?_canonical
    (input : AuthoritativeChemicalInputWithVirtualEndpoints)
    (wellFormed : input.StructurallyWellFormed)
    (endpoint partner : input.source.AromaticCanonicalAtom)
    (completion :
      AuthoritativeChemicalInput.AromaticCanonicalRule3EndpointCompletion)
    (lookedUp : input.completionAt? endpoint partner = some completion) :
    input.source.AromaticCanonicalOrdinaryDoubleBond endpoint partner ∧
      input.source.CanonicalAromaticCanonicalRule3EndpointCompletion
        endpoint partner completion := by
  exact input.source.aromaticCanonicalRule3EndpointCompletionLookup?_canonical
    input.endpointCompletions wellFormed.2 endpoint partner completion lookedUp

/-- Coverage produces canonical completion evidence at each end of every retained individual
bond. -/
theorem exists_canonical_completions_of_mem_individualDoubleBond
    (input : AuthoritativeChemicalInputWithVirtualEndpoints)
    (wellFormed : input.StructurallyWellFormed)
    (covered : input.CoversCanonicalIndividualDoubleBonds)
    (bond : input.source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (present : bond ∈ input.source.aromaticCanonicalIndividualDoubleBondCarriers) :
    ∃ leftCompletion rightCompletion,
      input.completionAt? bond.left bond.right = some leftCompletion ∧
      input.completionAt? bond.right bond.left = some rightCompletion ∧
      input.source.CanonicalAromaticCanonicalRule3EndpointCompletion
        bond.left bond.right leftCompletion ∧
      input.source.CanonicalAromaticCanonicalRule3EndpointCompletion
        bond.right bond.left rightCompletion := by
  obtain ⟨⟨leftCompletion, leftObserved⟩, ⟨rightCompletion, rightObserved⟩⟩ :=
    covered bond present
  exact ⟨leftCompletion, rightCompletion, leftObserved, rightObserved,
    (input.completionAt?_canonical wellFormed bond.left bond.right
      leftCompletion leftObserved).2,
    (input.completionAt?_canonical wellFormed bond.right bond.left
      rightCompletion rightObserved).2⟩

end AuthoritativeChemicalInputWithVirtualEndpoints

/-- Kernel-certified enriched source: structural consistency and total individual-bond coverage
are carried as proof fields. -/
structure CertifiedAuthoritativeChemicalInputWithVirtualEndpoints where
  input : AuthoritativeChemicalInputWithVirtualEndpoints
  structurallyWellFormed : input.StructurallyWellFormed
  coversCanonicalIndividualDoubleBonds : input.CoversCanonicalIndividualDoubleBonds

namespace CertifiedAuthoritativeChemicalInputWithVirtualEndpoints

/-- Whole-family analysis specialized to a certified enriched input. -/
noncomputable def analyzeOrdinaryDoubleBonds
    (certified : CertifiedAuthoritativeChemicalInputWithVirtualEndpoints)
    (carrierFuel : Nat)
    (viewAt : (atom : certified.input.source.AromaticCanonicalAtom) →
      certified.input.source.AromaticCanonicalDependencyView
        (certified.input.source.aromaticCanonicalRootOccurrence carrierFuel atom)) :
    List certified.input.source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment :=
  certified.input.source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithVirtualEndpoints
    carrierFuel viewAt certified.input.completionAt?

/-- The certified enriched analyzer has exact virtual-aware membership. -/
theorem mem_analyzeOrdinaryDoubleBonds_iff_canonical
    (certified : CertifiedAuthoritativeChemicalInputWithVirtualEndpoints)
    (carrierFuel : Nat)
    (viewAt : (atom : certified.input.source.AromaticCanonicalAtom) →
      certified.input.source.AromaticCanonicalDependencyView
        (certified.input.source.aromaticCanonicalRootOccurrence carrierFuel atom))
    (assignment :
      certified.input.source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) :
    assignment ∈ certified.analyzeOrdinaryDoubleBonds carrierFuel viewAt ↔
      ∃ bond,
        certified.input.source.AromaticCanonicalOrdinaryDoubleBondAutomaticVirtualCanonicalSpatialJudgment
          carrierFuel certified.input.completionAt? bond
            (viewAt bond.left) (viewAt bond.right) assignment := by
  exact certified.input.source.mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithVirtualEndpoints_iff_canonical
    carrierFuel viewAt certified.input.completionAt? assignment

/-- Every certified canonical individual bond has nonambiguous endpoint evidence and is then
classified by the exact virtual-aware analyzer as one success or one refusal for substantive
ranking/geometry reasons. -/
theorem every_individualDoubleBond_exact_readiness_or_refusal
    (certified : CertifiedAuthoritativeChemicalInputWithVirtualEndpoints)
    (carrierFuel : Nat)
    (viewAt : (atom : certified.input.source.AromaticCanonicalAtom) →
      certified.input.source.AromaticCanonicalDependencyView
        (certified.input.source.aromaticCanonicalRootOccurrence carrierFuel atom)) :
    ∀ bond ∈ certified.input.source.aromaticCanonicalIndividualDoubleBondCarriers,
      (certified.input.source.AromaticCanonicalOrdinaryDoubleBondAutomaticVirtualCanonicalReadiness
          carrierFuel certified.input.completionAt? bond
            (viewAt bond.left) (viewAt bond.right) ∧
        ∃! assignment,
          assignment ∈ certified.analyzeOrdinaryDoubleBonds carrierFuel viewAt ∧
            assignment.bond = bond) ∨
      (¬ certified.input.source.AromaticCanonicalOrdinaryDoubleBondAutomaticVirtualCanonicalReadiness
          carrierFuel certified.input.completionAt? bond
            (viewAt bond.left) (viewAt bond.right) ∧
        certified.input.source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignmentWithVirtualEndpoints?
          carrierFuel certified.input.completionAt? bond
            (viewAt bond.left) (viewAt bond.right) = none) := by
  exact certified.input.source.every_aromaticCanonicalOrdinaryDoubleBond_virtual_exact_readiness_or_refusal
    carrierFuel viewAt certified.input.completionAt?

end CertifiedAuthoritativeChemicalInputWithVirtualEndpoints
end TetraStereo.OneCenter
