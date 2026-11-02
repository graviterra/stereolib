import TetraStereo.OneCenter.AuthoritativeSemanticOrdinaryDoubleBondElectronicInventoryExactReadiness

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Finite atom-keyed electronic-state evidence

One atom has one electronic state even when it is viewed from a directed bond endpoint.  This
module therefore replaces a partner-indexed annotation burden with a finite atom-keyed record
list.  Structural certification proves unique atom keys and validates the same record against
every canonical individual-double-bond direction owned by that atom.  Coverage ensures a record
exists for every such endpoint.  The certified list then compiles to the exact electronic-
inventory analyzer.
-/

namespace AuthoritativeChemicalInput

/-- One atom-level electronic-position annotation. -/
structure AromaticCanonicalAtomElectronicStateRecord
    (source : AuthoritativeChemicalInput) where
  atom : source.AromaticCanonicalAtom
  inventory : AromaticCanonicalRule3EndpointElectronicInventory
  deriving DecidableEq

namespace AromaticCanonicalAtomElectronicStateRecord

def key {source : AuthoritativeChemicalInput}
    (record : source.AromaticCanonicalAtomElectronicStateRecord) : ℕ :=
  record.atom.val

end AromaticCanonicalAtomElectronicStateRecord

/-- Exact finite lookup by atom. -/
noncomputable def aromaticCanonicalAtomElectronicStateLookup?
    (source : AuthoritativeChemicalInput)
    (records : List source.AromaticCanonicalAtomElectronicStateRecord)
    (atom : source.AromaticCanonicalAtom) :
    Option AromaticCanonicalRule3EndpointElectronicInventory :=
  match records with
  | [] => none
  | record :: rest =>
      if record.atom = atom then
        some record.inventory
      else
        source.aromaticCanonicalAtomElectronicStateLookup? rest atom

/-- Atom-state lookup succeeds exactly for the unique matching finite record. -/
theorem aromaticCanonicalAtomElectronicStateLookup?_eq_some_iff
    (source : AuthoritativeChemicalInput)
    (records : List source.AromaticCanonicalAtomElectronicStateRecord)
    (uniqueKeys :
      (records.map AromaticCanonicalAtomElectronicStateRecord.key).Nodup)
    (atom : source.AromaticCanonicalAtom)
    (inventory : AromaticCanonicalRule3EndpointElectronicInventory) :
    source.aromaticCanonicalAtomElectronicStateLookup? records atom = some inventory ↔
      ∃ record ∈ records,
        record.atom = atom ∧ record.inventory = inventory := by
  induction records with
  | nil => simp [aromaticCanonicalAtomElectronicStateLookup?]
  | cons record rest inductionHypothesis =>
      simp only [List.map_cons, List.nodup_cons] at uniqueKeys
      obtain ⟨headFresh, tailUnique⟩ := uniqueKeys
      by_cases matched : record.atom = atom
      · subst atom
        simp only [aromaticCanonicalAtomElectronicStateLookup?, ↓reduceIte,
          Option.some.injEq]
        constructor
        · intro inventoryEq
          exact ⟨record, List.mem_cons_self, rfl, inventoryEq⟩
        · rintro ⟨witness, present, atomEq, inventoryEq⟩
          rcases List.mem_cons.mp present with rfl | tailPresent
          · exact inventoryEq
          · exfalso
            apply headFresh
            exact List.mem_map.mpr ⟨witness, tailPresent, by
              simp [AromaticCanonicalAtomElectronicStateRecord.key, atomEq]⟩
      · rw [aromaticCanonicalAtomElectronicStateLookup?, if_neg matched,
          inductionHypothesis tailUnique]
        constructor
        · rintro ⟨witness, present, atomEq, inventoryEq⟩
          exact ⟨witness, List.mem_cons_of_mem _ present, atomEq, inventoryEq⟩
        · rintro ⟨witness, present, atomEq, inventoryEq⟩
          rcases List.mem_cons.mp present with rfl | tailPresent
          · exact False.elim (matched atomEq)
          · exact ⟨witness, tailPresent, atomEq, inventoryEq⟩

/-- Every atom key is unique, and its single inventory is canonical for every directed individual
ordinary-double-bond endpoint owned by that atom. -/
def AromaticCanonicalAtomElectronicStateRecordsWellFormed
    (source : AuthoritativeChemicalInput)
    (records : List source.AromaticCanonicalAtomElectronicStateRecord) : Prop :=
  (records.map AromaticCanonicalAtomElectronicStateRecord.key).Nodup ∧
    ∀ record, record ∈ records →
      ∀ partner,
        source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint record.atom partner →
          source.CanonicalAromaticCanonicalRule3EndpointElectronicInventory
            record.atom partner record.inventory

/-- A lookup from well-formed records is canonical for any retained directed endpoint. -/
theorem aromaticCanonicalAtomElectronicStateLookup?_canonical
    (source : AuthoritativeChemicalInput)
    (records : List source.AromaticCanonicalAtomElectronicStateRecord)
    (wellFormed : source.AromaticCanonicalAtomElectronicStateRecordsWellFormed records)
    (endpoint partner : source.AromaticCanonicalAtom)
    (inventory : AromaticCanonicalRule3EndpointElectronicInventory)
    (lookedUp : source.aromaticCanonicalAtomElectronicStateLookup?
      records endpoint = some inventory)
    (directed :
      source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint endpoint partner) :
    source.CanonicalAromaticCanonicalRule3EndpointElectronicInventory
      endpoint partner inventory := by
  obtain ⟨record, present, atomEq, inventoryEq⟩ :=
    (source.aromaticCanonicalAtomElectronicStateLookup?_eq_some_iff
      records wellFormed.1 endpoint inventory).mp lookedUp
  subst endpoint
  subst inventory
  exact wellFormed.2 record present partner directed

end AuthoritativeChemicalInput

/-- Format-neutral molecule input enriched by one finite electronic-state record per relevant
atom. -/
structure AuthoritativeChemicalInputWithAtomElectronicStates where
  source : AuthoritativeChemicalInput
  atomElectronicStates :
    List source.AromaticCanonicalAtomElectronicStateRecord

namespace AuthoritativeChemicalInputWithAtomElectronicStates

def StructurallyWellFormed
    (input : AuthoritativeChemicalInputWithAtomElectronicStates) : Prop :=
  input.source.StructurallyWellFormed ∧
    input.source.AromaticCanonicalAtomElectronicStateRecordsWellFormed
      input.atomElectronicStates

/-- Exact atom-state lookup exported by the enriched input. -/
noncomputable def inventoryAt?
    (input : AuthoritativeChemicalInputWithAtomElectronicStates)
    (atom : input.source.AromaticCanonicalAtom) :
    Option AuthoritativeChemicalInput.AromaticCanonicalRule3EndpointElectronicInventory :=
  input.source.aromaticCanonicalAtomElectronicStateLookup? input.atomElectronicStates atom

/-- Every directed endpoint of every retained individual ordinary double bond has an atom-level
electronic-state record. -/
def CoversCanonicalIndividualDoubleBondEndpoints
    (input : AuthoritativeChemicalInputWithAtomElectronicStates) : Prop :=
  ∀ endpoint partner,
    input.source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint endpoint partner →
      ∃ inventory, input.inventoryAt? endpoint = some inventory

theorem inventoryAt?_canonical
    (input : AuthoritativeChemicalInputWithAtomElectronicStates)
    (wellFormed : input.StructurallyWellFormed)
    (endpoint partner : input.source.AromaticCanonicalAtom)
    (inventory :
      AuthoritativeChemicalInput.AromaticCanonicalRule3EndpointElectronicInventory)
    (lookedUp : input.inventoryAt? endpoint = some inventory)
    (directed :
      input.source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint endpoint partner) :
    input.source.CanonicalAromaticCanonicalRule3EndpointElectronicInventory
      endpoint partner inventory := by
  exact input.source.aromaticCanonicalAtomElectronicStateLookup?_canonical
    input.atomElectronicStates wellFormed.2 endpoint partner inventory lookedUp directed

end AuthoritativeChemicalInputWithAtomElectronicStates

/-- Proof-carrying finite atom-electronic-state input. -/
structure CertifiedAuthoritativeChemicalInputWithAtomElectronicStates where
  input : AuthoritativeChemicalInputWithAtomElectronicStates
  structurallyWellFormed : input.StructurallyWellFormed
  coversCanonicalIndividualDoubleBondEndpoints :
    input.CoversCanonicalIndividualDoubleBondEndpoints

namespace CertifiedAuthoritativeChemicalInputWithAtomElectronicStates

private def absentInventory :
    AuthoritativeChemicalInput.AromaticCanonicalRule3EndpointElectronicInventory where
  implicitProtia := 0
  lonePairs := 0
  vacancies := 0
  unpairedElectronPositions := 0

/-- Compile the finite atom-state list into the total function consumed by the ordinary-double-
bond inventory analyzer. The default is unreachable at every covered directed endpoint. -/
noncomputable def inventorySource
    (certified : CertifiedAuthoritativeChemicalInputWithAtomElectronicStates) :
    certified.input.source.AromaticCanonicalRule3EndpointElectronicInventorySource where
  inventory := fun endpoint _partner =>
    (certified.input.inventoryAt? endpoint).getD absentInventory
  canonical := by
    intro endpoint partner directed
    obtain ⟨inventory, found⟩ :=
      certified.coversCanonicalIndividualDoubleBondEndpoints endpoint partner directed
    have canonical := certified.input.inventoryAt?_canonical
      certified.structurallyWellFormed endpoint partner inventory found directed
    simpa [found] using canonical

/-- Every covered directed endpoint uses the literal looked-up atom inventory. -/
theorem inventorySource_eq_of_inventoryAt?_eq_some
    (certified : CertifiedAuthoritativeChemicalInputWithAtomElectronicStates)
    (endpoint partner : certified.input.source.AromaticCanonicalAtom)
    (inventory :
      AuthoritativeChemicalInput.AromaticCanonicalRule3EndpointElectronicInventory)
    (lookedUp : certified.input.inventoryAt? endpoint = some inventory) :
    (certified.inventorySource.inventory endpoint partner) = inventory := by
  simp [inventorySource, lookedUp]

/-- Actual whole-family analyzer driven by certified finite atom electronic states. -/
noncomputable def analyzeOrdinaryDoubleBonds
    (certified : CertifiedAuthoritativeChemicalInputWithAtomElectronicStates)
    (carrierFuel : Nat)
    (viewAt : (atom : certified.input.source.AromaticCanonicalAtom) →
      certified.input.source.AromaticCanonicalDependencyView
        (certified.input.source.aromaticCanonicalRootOccurrence carrierFuel atom)) :
    List certified.input.source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment :=
  certified.input.source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithElectronicInventory
      carrierFuel viewAt certified.inventorySource

/-- Finite-state analyzer membership is exactly the independent inventory-aware canonical
judgment. -/
theorem mem_analyzeOrdinaryDoubleBonds_iff_canonical
    (certified : CertifiedAuthoritativeChemicalInputWithAtomElectronicStates)
    (carrierFuel : Nat)
    (viewAt : (atom : certified.input.source.AromaticCanonicalAtom) →
      certified.input.source.AromaticCanonicalDependencyView
        (certified.input.source.aromaticCanonicalRootOccurrence carrierFuel atom))
    (assignment :
      certified.input.source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) :
    assignment ∈ certified.analyzeOrdinaryDoubleBonds carrierFuel viewAt ↔
      ∃ bond,
        certified.input.source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalSpatialJudgment
            carrierFuel certified.inventorySource bond
              (viewAt bond.left) (viewAt bond.right) assignment := by
  unfold analyzeOrdinaryDoubleBonds
  exact certified.input.source.mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithElectronicInventory_iff_canonical
      carrierFuel viewAt certified.inventorySource assignment

theorem analyzeOrdinaryDoubleBonds_nodup
    (certified : CertifiedAuthoritativeChemicalInputWithAtomElectronicStates)
    (carrierFuel : Nat)
    (viewAt : (atom : certified.input.source.AromaticCanonicalAtom) →
      certified.input.source.AromaticCanonicalDependencyView
        (certified.input.source.aromaticCanonicalRootOccurrence carrierFuel atom)) :
    (certified.analyzeOrdinaryDoubleBonds carrierFuel viewAt).Nodup := by
  unfold analyzeOrdinaryDoubleBonds
  exact certified.input.source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithElectronicInventory_nodup
      carrierFuel viewAt certified.inventorySource

/-- Every canonical individual ordinary double bond is uniquely emitted or receives the exact
base/vacancy/radical/reference-rejection classification. -/
theorem every_individualDoubleBond_exact_success_or_refusal
    (certified : CertifiedAuthoritativeChemicalInputWithAtomElectronicStates)
    (carrierFuel : Nat)
    (viewAt : (atom : certified.input.source.AromaticCanonicalAtom) →
      certified.input.source.AromaticCanonicalDependencyView
        (certified.input.source.aromaticCanonicalRootOccurrence carrierFuel atom)) :
    ∀ bond ∈ certified.input.source.aromaticCanonicalIndividualDoubleBondCarriers,
      (certified.input.source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalReadiness
            carrierFuel certified.inventorySource bond
              (viewAt bond.left) (viewAt bond.right) ∧
        ∃! assignment,
          assignment ∈ certified.analyzeOrdinaryDoubleBonds carrierFuel viewAt ∧
          assignment.bond = bond) ∨
      (certified.input.source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalRefusal
            carrierFuel certified.inventorySource bond
              (viewAt bond.left) (viewAt bond.right) ∧
        certified.input.source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignmentWithElectronicInventory?
            carrierFuel certified.inventorySource bond
              (viewAt bond.left) (viewAt bond.right) = none) := by
  unfold analyzeOrdinaryDoubleBonds
  exact certified.input.source.every_aromaticCanonicalOrdinaryDoubleBond_electronicInventory_exact_success_or_refusal
      carrierFuel viewAt certified.inventorySource

end CertifiedAuthoritativeChemicalInputWithAtomElectronicStates
end TetraStereo.OneCenter
