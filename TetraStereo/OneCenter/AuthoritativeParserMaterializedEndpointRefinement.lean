import TetraStereo.OneCenter.AuthoritativeChemicalInputVirtualEndpointRefinement
import TetraStereo.OneCenter.AuthoritativeSemanticTetrahedralElementApplicability

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Parser/materialized-endpoint refinement

The parser bridge preserves atom indices and constitutional adjacency exactly.  Consequently a
materialized double-bond endpoint with three written neighbours has exactly two represented
nonpartner substituents after semantic ingestion.  This module proves that fact and feeds it into
the generic endpoint-classifier compiler.

The theorem is intentionally conditional on degree three at every directed individual-bond
endpoint.  `withExplicitHydrogens` is responsible for establishing this postcondition on chemical
domains whose missing positions really are hydrogens.  Heteroatom lone-pair cases require a
different authoritative classifier and must not be folded into this represented-only theorem.
-/

namespace RawMolecule

/-- Parser conversion exists whenever no atom slot is the unknown `wildcard` sentinel.
This existential totality does not establish equality to an arbitrary supplied source molecule;
refinement against a fixed source retains the explicit conversion-identity hypothesis. -/
theorem exists_toSemanticMolecule?_of_noWildcard
    (molecule : RawMolecule)
    (noWildcard : ∀ atom, atom ∈ molecule.atoms → atom.element ≠ .wildcard) :
    ∃ semantic : SemanticMolecule, molecule.toSemanticMolecule? = some semantic := by
  have someTrue : molecule.toSemanticMolecule?.isSome = true :=
    (molecule.toSemanticMolecule?_isSome).mpr noWildcard
  cases observed : molecule.toSemanticMolecule? with
  | none =>
      rw [observed] at someTrue
      simp at someTrue
  | some semantic => exact ⟨semantic, rfl⟩

/-- Executable parser-admission check: no atom slot is the nonchemical `wildcard` sentinel.  This is
decidable data computed directly from the parsed atom list, so a caller can admit or refuse a raw
molecule by computation instead of assuming wildcard-freeness. -/
def hasNoWildcardAtom (molecule : RawMolecule) : Bool :=
  molecule.atoms.all fun atom => decide (atom.element ≠ .wildcard)

/-- Soundness and completeness of the executable wildcard check: the computed `Bool` agrees
exactly with the propositional no-wildcard predicate.  The admission condition is therefore a
reflection of real parser data, not an assumed correctness wrapper. -/
theorem hasNoWildcardAtom_eq_true_iff (molecule : RawMolecule) :
    molecule.hasNoWildcardAtom = true ↔
      ∀ atom, atom ∈ molecule.atoms → atom.element ≠ .wildcard := by
  simp [hasNoWildcardAtom, List.all_eq_true]

/-- Parser totality discharged from executable data: a raw molecule whose computed wildcard check
passes has a literal semantic molecule and a successful checked conversion.  The no-wildcard
premise of `exists_toSemanticMolecule?_of_noWildcard` is thereby reduced to a decidable admission
condition over parser input. -/
theorem exists_toSemanticMolecule?_of_hasNoWildcard
    (molecule : RawMolecule) (admitted : molecule.hasNoWildcardAtom = true) :
    ∃ semantic : SemanticMolecule, molecule.toSemanticMolecule? = some semantic :=
  molecule.exists_toSemanticMolecule?_of_noWildcard
    ((molecule.hasNoWildcardAtom_eq_true_iff).mp admitted)

/-- Transport a semantic source atom back to the parser index with the same numerical value. -/
def originalAtomIndex
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (atom : source.AromaticCanonicalAtom) : Fin molecule.atomCount :=
  Fin.cast (molecule.toSemanticMolecule?_atomCount source.molecule converted) atom

@[simp] theorem originalAtomIndex_val
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (atom : source.AromaticCanonicalAtom) :
    (molecule.originalAtomIndex source converted atom).val = atom.val := by
  rfl

@[simp] theorem convertedAtomIndex_originalAtomIndex
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (atom : source.AromaticCanonicalAtom) :
    molecule.convertedAtomIndex source converted
        (molecule.originalAtomIndex source converted atom) = atom := by
  apply Fin.ext
  rfl

/-- Index round-trip in the opposite direction: a raw index transported into the semantic source
and back returns the original raw index.  Together with `convertedAtomIndex_originalAtomIndex` this
makes `originalAtomIndex` a genuine two-sided inverse of `convertedAtomIndex` on the
successful-conversion domain, so endpoint traces cannot silently change identity. -/
theorem originalAtomIndex_convertedAtomIndex
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (atom : Fin molecule.atomCount) :
    molecule.originalAtomIndex source converted
        (molecule.convertedAtomIndex source converted atom) = atom := by
  apply Fin.ext
  rfl

/-- Concrete postcondition for a parser representation in which every nonpartner position of an
individual ordinary-double-bond endpoint has been materialized as an atom. -/
def MaterializedCanonicalIndividualDoubleBondEndpoints
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule) : Prop :=
  ∀ endpoint partner,
    source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint endpoint partner →
      (molecule.writtenNeighbors
        (molecule.originalAtomIndex source converted endpoint).val).length = 3

/-- Exact degree-to-completion bridge: three materialized neighbours at a double-bond endpoint
become exactly two represented nonpartner substituents in the semantic source. -/
theorem fullyRepresentedCanonicalIndividualDoubleBondEndpoints_of_materialized
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (writtenExact : molecule.WrittenNeighborExact)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (materialized :
      molecule.MaterializedCanonicalIndividualDoubleBondEndpoints source converted) :
    source.FullyRepresentedCanonicalIndividualDoubleBondEndpoints := by
  intro endpoint partner directed
  let rawEndpoint := molecule.originalAtomIndex source converted endpoint
  have degreeEqual :=
    molecule.writtenNeighbor_length_eq_convertedAromaticCanonicalNeighbor_card
      source converted writtenExact resolved rawEndpoint
  have rawDegree : (molecule.writtenNeighbors rawEndpoint.val).length = 3 :=
    materialized endpoint partner directed
  have endpointReturned :
      molecule.convertedAtomIndex source converted rawEndpoint = endpoint := by
    apply Fin.ext
    rfl
  rw [rawDegree, endpointReturned] at degreeEqual
  have semanticDegree : (source.aromaticCanonicalNeighborFinset endpoint).card = 3 :=
    degreeEqual.symm
  have ordinary := source.aromaticCanonicalOrdinaryDoubleBond_of_directedEndpoint directed
  have partnerPresent : partner ∈ source.aromaticCanonicalNeighborFinset endpoint :=
    (source.mem_aromaticCanonicalNeighborFinset_iff endpoint partner).mpr ordinary.1
  simp [AuthoritativeChemicalInput.aromaticCanonicalRule3Substituents, Finset.length_sort,
    Finset.card_erase_of_mem partnerPresent, semanticDegree]

/-- Reflection of the materialization bridge: source-level full representation *forces* the parser
raw degree-three postcondition.  This is the converse of
`fullyRepresentedCanonicalIndividualDoubleBondEndpoints_of_materialized`, using the same
cardinality-preserving parser/semantic neighbor bijection in the opposite direction.  It shows the
degree-three hypothesis is neither stronger nor weaker than the semantic fully-represented shape on
the successful-conversion domain. -/
theorem materializedCanonicalIndividualDoubleBondEndpoints_of_fullyRepresented
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (writtenExact : molecule.WrittenNeighborExact)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (fullyRepresented : source.FullyRepresentedCanonicalIndividualDoubleBondEndpoints) :
    molecule.MaterializedCanonicalIndividualDoubleBondEndpoints source converted := by
  intro endpoint partner directed
  let rawEndpoint := molecule.originalAtomIndex source converted endpoint
  have degreeEqual :=
    molecule.writtenNeighbor_length_eq_convertedAromaticCanonicalNeighbor_card
      source converted writtenExact resolved rawEndpoint
  have endpointReturned :
      molecule.convertedAtomIndex source converted rawEndpoint = endpoint := by
    exact molecule.convertedAtomIndex_originalAtomIndex source converted endpoint
  rw [endpointReturned] at degreeEqual
  have ordinary := source.aromaticCanonicalOrdinaryDoubleBond_of_directedEndpoint directed
  have partnerPresent : partner ∈ source.aromaticCanonicalNeighborFinset endpoint :=
    (source.mem_aromaticCanonicalNeighborFinset_iff endpoint partner).mpr ordinary.1
  have eraseCard :
      ((source.aromaticCanonicalNeighborFinset endpoint).erase partner).card = 2 := by
    simpa [AuthoritativeChemicalInput.aromaticCanonicalRule3Substituents, Finset.length_sort] using
      fullyRepresented endpoint partner directed
  have semanticDegree : (source.aromaticCanonicalNeighborFinset endpoint).card = 2 + 1 := by
    have hmem : partner ∈ source.aromaticCanonicalNeighborFinset endpoint := partnerPresent
    have hpos : 1 ≤ (source.aromaticCanonicalNeighborFinset endpoint).card :=
      Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨partner, hmem⟩)
    calc
      (source.aromaticCanonicalNeighborFinset endpoint).card
          = (source.aromaticCanonicalNeighborFinset endpoint).card - 1 + 1 :=
            (Nat.sub_add_cancel hpos).symm
      _ = ((source.aromaticCanonicalNeighborFinset endpoint).erase partner).card + 1 := by
            rw [← Finset.card_erase_of_mem hmem]
      _ = 2 + 1 := by rw [eraseCard]
  rw [semanticDegree] at degreeEqual
  simpa [rawEndpoint] using degreeEqual

/-- Exact representation-preservation equivalence on the successful-conversion domain with exact
written neighbours and resolved bond kinds: the parser raw degree-three materialization
postcondition holds iff the semantic source is fully represented at every directed individual
ordinary-double-bond endpoint.  The forward map is the degree-to-completion bridge; the backward map
is the reflection theorem, so a caller may supply whichever side is directly checkable. -/
theorem materializedCanonicalIndividualDoubleBondEndpoints_iff_fullyRepresented
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (writtenExact : molecule.WrittenNeighborExact)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified) :
    molecule.MaterializedCanonicalIndividualDoubleBondEndpoints source converted ↔
      source.FullyRepresentedCanonicalIndividualDoubleBondEndpoints :=
  ⟨molecule.fullyRepresentedCanonicalIndividualDoubleBondEndpoints_of_materialized
      source converted writtenExact resolved,
    molecule.materializedCanonicalIndividualDoubleBondEndpoints_of_fullyRepresented
      source converted writtenExact resolved⟩

/-- A materialized parser representation therefore supplies the canonical represented-only
classifier required by the generic finite-evidence compiler. -/
def representedOnlyEndpointClassifierOfMaterialized
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (writtenExact : molecule.WrittenNeighborExact)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (materialized :
      molecule.MaterializedCanonicalIndividualDoubleBondEndpoints source converted) :
    source.AromaticCanonicalRule3EndpointClassifier :=
  source.representedOnlyEndpointClassifier
    (molecule.fullyRepresentedCanonicalIndividualDoubleBondEndpoints_of_materialized
      source converted writtenExact resolved materialized)

/-- End-to-end parser refinement on the fully materialized endpoint domain: no endpoint record is
supplied by hand; the certified virtual-aware ordinary-double-bond input is constructed from the
parser/semantic correspondence and the degree-three materialization postcondition. -/
noncomputable def certifiedVirtualEndpointsOfMaterializedParser
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (sourceWellFormed : source.StructurallyWellFormed)
    (writtenExact : molecule.WrittenNeighborExact)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (materialized :
      molecule.MaterializedCanonicalIndividualDoubleBondEndpoints source converted) :
    CertifiedAuthoritativeChemicalInputWithVirtualEndpoints :=
  source.certifiedWithVirtualEndpointsOfClassifier sourceWellFormed
    (molecule.representedOnlyEndpointClassifierOfMaterialized
      source converted writtenExact resolved materialized)

end RawMolecule
end TetraStereo.OneCenter
