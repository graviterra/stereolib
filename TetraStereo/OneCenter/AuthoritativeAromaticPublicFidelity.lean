import TetraStereo.OneCenter.CIPAuthoritativeAromaticKekuleNormalization
import TetraStereo.OneCenter.ChemistrySemantics
import TetraStereo.OneCenter.ExactOfficialRuleMajorKey
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.AuthoritativeAromaticPublicFidelity

open RawMolecule
open AuthoritativeCIPAromaticKekuleNormalization
open AuthoritativeCIPMancudeTotality
open AuthoritativeCIPRule6P92Enumeration
open AuthoritativeCIPMoleculeCursorRanking

/-!
# Public source-faithful aromatic normalization route

`parseAndNormalizeOpenSMILESCertified` in `ChemistrySemantics` calls the plain
`normalizeRawMolecule` pipeline: bond orders marked `unspecified` are localized, but declared
aromatic bonds are left delocalized.  The authoritative aromatic route developed in
`CIPAuthoritativeAromaticKekuleNormalization` instead performs the complete finite maximum-matching
Kekule search and returns a certificate.  This module exposes that route at the public parser
boundary and binds every returned result to the *actual* molecule produced by `parseOpenSMILES`,
without accepting a caller-supplied expected output.

The binding theorems establish:

* the exact parsed molecule and the exact `normalizeAromaticKekule?` candidate that produced the
  returned certificate;
* preservation of atoms, atom count, written-neighbour order, introduction provenance, and the
  constitutional edge-key list, and reflection of adjacency support (`bondOrder > 0`);
* the certified structural, valence, and (under the source parity premise) stereochemical
  contracts, together with the complete P-92 reference-position ranking backend;
* coincidence with the plain route when the parsed molecule carries no declared aromatic bonds.

For Kekule choices of one and the same source, exact Rule-1a observations are compared through the
existing semantic mancude witnesses: `MoleculeGraph.exactMancudeAverage_eq_of_atomZ_eq_of_localizedMancudeEdge_iff`
and `MoleculeGraph.exactOfficialRule1aObservation_eq_of_atomZ_eq_of_localizedMancudeEdge_iff`.
Those theorems are exactly the equivalence used by
`AuthoritativeSemanticAromaticKekuleNormalization`.  Their remaining premise is equality of the
independent `LocalizedMancudeEdge` relation; that premise is not derivable from the raw candidate
acceptance predicate alone, so it is kept explicit as `SameLocalizedMancudeRelation` and is
reported as residual work rather than assumed.
-/

/-- Public parser-facing authoritative aromatic normalization.

The source string is parsed once.  A parse error is propagated unchanged; a successful parse is
submitted to `normalizeRawMoleculeAuthoritativeAromaticCertified?`, whose certified result (or its
rejection) is returned unchanged.  This is the checked counterpart of the plain
`parseAndNormalizeOpenSMILESCertified` route, which performs no aromatic/Kekule search. -/
def parseAndNormalizeOpenSMILESAuthoritativeAromaticCertified
    (input : String) (cycles : List AromaticCycle := []) :
    Except ParserError CertifiedChemistryNormalizationResult :=
  match parseOpenSMILES input with
  | Except.error error => Except.error error
  | Except.ok molecule =>
      match normalizeRawMoleculeAuthoritativeAromaticCertified? molecule cycles with
      | some certified => Except.ok certified
      | none => Except.error
          "authoritative aromatic normalization rejected the parsed molecule"

/-- Every successful public route result really came from an actual parse followed by the
authoritative raw-molecule normalization.  No expected output is supplied by the caller. -/
theorem parseAndNormalizeOpenSMILESAuthoritativeAromaticCertified_sound
    (input : String) (cycles : List AromaticCycle)
    (certified : CertifiedChemistryNormalizationResult)
    (observed :
      parseAndNormalizeOpenSMILESAuthoritativeAromaticCertified input cycles =
        Except.ok certified) :
    ∃ molecule, parseOpenSMILES input = Except.ok molecule ∧
      normalizeRawMoleculeAuthoritativeAromaticCertified? molecule cycles = some certified := by
  cases parsed : parseOpenSMILES input with
  | error error =>
      simp [parseAndNormalizeOpenSMILESAuthoritativeAromaticCertified, parsed] at observed
  | ok molecule =>
      cases normalized : normalizeRawMoleculeAuthoritativeAromaticCertified? molecule cycles with
      | none =>
          simp only [parseAndNormalizeOpenSMILESAuthoritativeAromaticCertified, parsed,
            normalized] at observed
          cases observed
      | some result =>
          simp only [parseAndNormalizeOpenSMILESAuthoritativeAromaticCertified, parsed,
            normalized] at observed
          have resultEq : result = certified := by
            simpa only [Except.ok.injEq] using observed
          refine ⟨molecule, rfl, ?_⟩
          rw [← resultEq]
          exact normalized

/-- Exact operational success boundary of the public route. -/
theorem parseAndNormalizeOpenSMILESAuthoritativeAromaticCertified_ok_iff
    (input : String) (cycles : List AromaticCycle) :
    (∃ certified,
      parseAndNormalizeOpenSMILESAuthoritativeAromaticCertified input cycles =
        Except.ok certified) ↔
      ∃ molecule, parseOpenSMILES input = Except.ok molecule ∧
        ∃ certified,
          normalizeRawMoleculeAuthoritativeAromaticCertified? molecule cycles = some certified := by
  constructor
  · rintro ⟨certified, observed⟩
    obtain ⟨molecule, parsed, normalized⟩ :=
      parseAndNormalizeOpenSMILESAuthoritativeAromaticCertified_sound input cycles certified
        observed
    exact ⟨molecule, parsed, certified, normalized⟩
  · rintro ⟨molecule, parsed, certified, normalized⟩
    refine ⟨certified, ?_⟩
    simp [parseAndNormalizeOpenSMILESAuthoritativeAromaticCertified, parsed, normalized]

/-! ## Binding the certified result to the actual Kekule candidate -/

/-- The authoritative certified chemistry pipeline is definitionally the aromatic certified
intake over `normalizeUnspecifiedBonds`; every returned value therefore exposes the exact
`normalizeAromaticKekule?` candidate that constructed it. -/
theorem normalizeAromaticChemistryCertified_candidate
    (source : RawMolecule) (cycles : List AromaticCycle)
    (certified : CertifiedChemistryNormalizationResult)
    (observed : normalizeAromaticChemistryCertified? source cycles = some certified) :
    ∃ candidate,
      normalizeAromaticKekule? source = some candidate ∧
        certified.result.parsed = candidate ∧
          Nonempty (AromaticKekuleNormalizationCertificate source candidate) := by
  unfold normalizeAromaticChemistryCertified? at observed
  split at observed
  · split at observed
    · split at observed
      · cases computed : normalizeAromaticKekuleCertified? source with
        | none => simp [computed] at observed
        | some output =>
            simp only [computed, Option.some.injEq] at observed
            subst certified
            exact ⟨output.candidate, output.computed, rfl, ⟨output.certificate⟩⟩
      · contradiction
    · contradiction
  · contradiction

/-- Raw-molecule form of the candidate binding: the candidate is drawn from the already
`normalizeUnspecifiedBonds`-normalized source actually consumed by the authoritative route. -/
theorem normalizeRawMoleculeAuthoritativeAromaticCertified_candidate
    (source : RawMolecule) (cycles : List AromaticCycle)
    (certified : CertifiedChemistryNormalizationResult)
    (observed :
      normalizeRawMoleculeAuthoritativeAromaticCertified? source cycles = some certified) :
    ∃ candidate,
      normalizeAromaticKekule? source.normalizeUnspecifiedBonds = some candidate ∧
        certified.result.parsed = candidate ∧
          Nonempty
            (AromaticKekuleNormalizationCertificate source.normalizeUnspecifiedBonds candidate) :=
  normalizeAromaticChemistryCertified_candidate source.normalizeUnspecifiedBonds cycles certified
    observed

/-- Complete public binding: one parsed molecule, one actual Kekule candidate, the full
normalization certificate, and the constitutional data that the aromatic route preserves. -/
theorem parseAndNormalizeOpenSMILESAuthoritativeAromaticCertified_binding
    (input : String) (cycles : List AromaticCycle)
    (certified : CertifiedChemistryNormalizationResult)
    (observed :
      parseAndNormalizeOpenSMILESAuthoritativeAromaticCertified input cycles =
        Except.ok certified) :
    ∃ molecule candidate,
      parseOpenSMILES input = Except.ok molecule ∧
        normalizeAromaticKekule? molecule.normalizeUnspecifiedBonds = some candidate ∧
          certified.result.parsed = candidate ∧
            Nonempty
              (AromaticKekuleNormalizationCertificate molecule.normalizeUnspecifiedBonds
                candidate) ∧
              candidate.atoms = molecule.normalizeUnspecifiedBonds.atoms ∧
                candidate.bonds.map RawBond.edgeKey =
                  molecule.normalizeUnspecifiedBonds.bonds.map RawBond.edgeKey := by
  obtain ⟨molecule, parsed, normalized⟩ :=
    parseAndNormalizeOpenSMILESAuthoritativeAromaticCertified_sound input cycles certified observed
  obtain ⟨candidate, computed, parsedEq, certificate⟩ :=
    normalizeRawMoleculeAuthoritativeAromaticCertified_candidate molecule cycles certified
      normalized
  exact ⟨molecule, candidate, parsed, computed, parsedEq, certificate,
    normalizeAromaticKekule?_atoms computed,
    normalizeAromaticKekule?_edgeKeys computed⟩

/-- Source-faithful constitution theorem for the public route.  Relative to the molecule actually
returned by the parser, the certified output preserves atom records, atom count, the ordered
edge-key list, every written-neighbour frame, adjacency support, and the complete introduction
provenance.  Only declared aromatic bond multiplicities may differ. -/
theorem parseAndNormalizeOpenSMILESAuthoritativeAromaticCertified_constitution
    (input : String) (cycles : List AromaticCycle)
    (certified : CertifiedChemistryNormalizationResult)
    (observed :
      parseAndNormalizeOpenSMILESAuthoritativeAromaticCertified input cycles =
        Except.ok certified) :
    ∃ molecule,
      parseOpenSMILES input = Except.ok molecule ∧
        certified.result.parsed.atoms = molecule.normalizeUnspecifiedBonds.atoms ∧
          certified.result.parsed.atomCount = molecule.atomCount ∧
            certified.result.parsed.bonds.map RawBond.edgeKey =
              molecule.normalizeUnspecifiedBonds.bonds.map RawBond.edgeKey ∧
              (∀ atom,
                certified.result.parsed.writtenNeighbors atom =
                  molecule.normalizeUnspecifiedBonds.writtenNeighbors atom) ∧
                (∀ left right,
                  0 < certified.result.parsed.bondOrder left right ↔
                    0 < molecule.normalizeUnspecifiedBonds.bondOrder left right) ∧
                  certified.result.parsed.introductionPredecessors =
                    molecule.normalizeUnspecifiedBonds.introductionPredecessors ∧
                    certified.result.parsed.introductionPredecessorsValid? =
                      molecule.normalizeUnspecifiedBonds.introductionPredecessorsValid? := by
  obtain ⟨molecule, candidate, parsed, computed, parsedEq, _certificate, _atoms, _edges⟩ :=
    parseAndNormalizeOpenSMILESAuthoritativeAromaticCertified_binding input cycles certified
      observed
  refine ⟨molecule, parsed, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [parsedEq]
    exact normalizeAromaticKekule?_atoms computed
  · rw [parsedEq]
    simp [RawMolecule.atomCount, normalizeAromaticKekule?_atoms computed]
  · rw [parsedEq]
    exact normalizeAromaticKekule?_edgeKeys computed
  · intro atom
    rw [parsedEq]
    exact normalizeAromaticKekule?_writtenNeighbors computed atom
  · intro left right
    rw [parsedEq]
    exact normalizeAromaticKekule?_bondOrder_pos_iff computed left right
  · rw [parsedEq]
    exact normalizeAromaticKekule?_introductionPredecessors computed
  · rw [parsedEq]
    exact normalizeAromaticKekule?_introductionPredecessorsValid computed

/-- The certified control fields attached to every public route result. -/
theorem parseAndNormalizeOpenSMILESAuthoritativeAromaticCertified_contract
    (input : String) (cycles : List AromaticCycle)
    (certified : CertifiedChemistryNormalizationResult)
    (_observed :
      parseAndNormalizeOpenSMILESAuthoritativeAromaticCertified input cycles =
        Except.ok certified) :
    certified.result.parsed.Admissible ∧
      certified.result.parsed.WrittenNeighborExact ∧
        certified.result.parsed.ValenceOK ∧
          certified.result.parsed.Rule2MassesKnown :=
  ⟨certified.admissible, certified.writtenNeighborExact, certified.valenceOK,
    certified.rule2MassesKnown⟩

/-- Every authoritative aromatic result exposes the complete chemical applicability boundary,
including exact maximum-matching localization of the selected Kekule form. -/
theorem normalizeRawMoleculeAuthoritativeAromaticCertified_chemical_applicability
    (source : RawMolecule) (cycles : List AromaticCycle)
    (certified : CertifiedChemistryNormalizationResult)
    (observed :
      normalizeRawMoleculeAuthoritativeAromaticCertified? source cycles = some certified) :
    certified.result.parsed.WellFormed ∧
      certified.result.parsed.BondRecordsUnique ∧
        certified.result.parsed.ValenceOK ∧
          LocalizedMancudeKekuleAdmissible certified.result.parsed ∧
            AromaticBondsLocalized source.normalizeUnspecifiedBonds
              certified.result.parsed := by
  obtain ⟨candidate, computed, parsedEq, _certificate⟩ :=
    normalizeRawMoleculeAuthoritativeAromaticCertified_candidate source cycles certified observed
  rw [parsedEq]
  exact normalizeAromaticKekule?_chemical_applicability source.normalizeUnspecifiedBonds
    candidate computed

/-- When the parsed source carried an exact written-neighbour parity frame, the certified
aromatic output is fully stereochemically admissible. -/
theorem normalizeRawMoleculeAuthoritativeAromaticCertified_stereochemicalAdmissible
    (source : RawMolecule) (cycles : List AromaticCycle)
    (certified : CertifiedChemistryNormalizationResult)
    (observed :
      normalizeRawMoleculeAuthoritativeAromaticCertified? source cycles = some certified)
    (sourceWrittenNeighborExact : source.WrittenNeighborExact) :
    certified.result.parsed.StereochemicalAdmissible := by
  obtain ⟨candidate, computed, parsedEq, _certificate⟩ :=
    normalizeRawMoleculeAuthoritativeAromaticCertified_candidate source cycles certified observed
  rw [parsedEq]
  exact normalizeAromaticKekule?_stereochemicalAdmissible computed
    (normalizeUnspecifiedBonds_writtenNeighborExact source sourceWrittenNeighborExact)

/-- Actual-consumer consequence of the public route: every P-92 reference position of every
generated canonical occurrence of the returned molecule has a completed uncapped authoritative
ranking.  This is derived from the actual observed route output, not from an assumed descriptor
equality. -/
theorem normalizeRawMoleculeAuthoritativeAromaticCertified_positionRankingBackend_total
    (source : RawMolecule) (cycles : List AromaticCycle)
    (certified : CertifiedChemistryNormalizationResult)
    (observed :
      normalizeRawMoleculeAuthoritativeAromaticCertified? source cycles = some certified)
    {state : OccurrenceAuxState} {center : Nat}
    (centerBound : center < certified.result.parsed.atomCount)
    {occurrence : CanonicalBranchNode}
    (occurrenceGenerated :
      CanonicalCenterTreeNode certified.result.parsed center occurrence)
    (ligands : List Nat) :
    ∀ referencePosition,
      ∃ ranking,
        authoritativeOccurrenceRule6PositionRankingBackend certified.result.parsed state
            (2 * certified.result.parsed.atomCount + 1)
            (occurrenceLigandCursors certified.result.parsed occurrence) ligands
            referencePosition = some ranking := by
  obtain ⟨candidate, computed, parsedEq, _certificate⟩ :=
    normalizeRawMoleculeAuthoritativeAromaticCertified_candidate source cycles certified observed
  rw [parsedEq] at centerBound occurrenceGenerated ⊢
  exact normalizedAromatic_positionRankingBackend_total computed centerBound occurrenceGenerated
    ligands

/-! ## Coincidence with the plain route for non-aromatic input -/

/-- With no declared aromatic bond, the empty Kekule selection is the identity on the bond list. -/
theorem withAromaticKekuleSelection_nil_of_forall_not_aromatic
    (source : RawMolecule)
    (noAromaticBond : ∀ bond, bond ∈ source.bonds →
      bond.kind ≠ ParsedBondKind.aromatic) :
    withAromaticKekuleSelection source [] = source := by
  have bondIdentity :
      ∀ bonds : List RawBond,
        (∀ bond, bond ∈ bonds → bond.kind ≠ ParsedBondKind.aromatic) →
          bonds.map (withAromaticKekuleSelectionBond []) = bonds := by
    intro bonds
    induction bonds with
    | nil => intro _; rfl
    | cons bond rest inductionHypothesis =>
        intro allNon
        have bondNon : bond.kind ≠ ParsedBondKind.aromatic := allNon bond (by simp)
        have restNon : ∀ item, item ∈ rest → item.kind ≠ ParsedBondKind.aromatic :=
          fun item member => allNon item (by simp [member])
        simp only [List.map_cons, inductionHypothesis restNon]
        congr 1
        unfold withAromaticKekuleSelectionBond
        split <;> rename_i condition
        · exact absurd (by simpa using condition) bondNon
        · rfl
  have mapped : source.bonds.map (withAromaticKekuleSelectionBond []) = source.bonds :=
    bondIdentity source.bonds noAromaticBond
  unfold withAromaticKekuleSelection
  rw [mapped]

/-- No declared aromatic occurrence means the empty selection is the identity. -/
theorem withAromaticKekuleSelection_nil_of_no_aromaticBonds
    (source : RawMolecule) (noAromatic : aromaticBondOccurrences source = []) :
    withAromaticKekuleSelection source [] = source := by
  apply withAromaticKekuleSelection_nil_of_forall_not_aromatic
  intro bond member kindEq
  have noAromaticFilter : source.bonds.filter
      (fun candidate => candidate.kind == ParsedBondKind.aromatic) = [] := by
    simpa [aromaticBondOccurrences] using noAromatic
  have filtered : bond ∈ source.bonds.filter
      (fun candidate => candidate.kind == ParsedBondKind.aromatic) := by
    simp [List.mem_filter, member, kindEq]
  rw [noAromaticFilter] at filtered
  exact absurd filtered (by simp)

/-- On a source without declared aromatic bonds the exhaustive search can only return the source
itself; there is no second Kekule representation to choose. -/
theorem normalizeAromaticKekule?_eq_source_of_no_aromaticBonds
    (source : RawMolecule) (noAromatic : aromaticBondOccurrences source = [])
    {candidate : RawMolecule}
    (computed : normalizeAromaticKekule? source = some candidate) :
    candidate = source := by
  have generated := (normalizeAromaticKekule?_certificate source candidate computed).generated
  have onlyCandidate : candidate ∈ [withAromaticKekuleSelection source []] := by
    simpa [aromaticKekuleCandidates, noAromatic] using generated
  have candidateEq : candidate = withAromaticKekuleSelection source [] := by
    simpa using onlyCandidate
  rw [candidateEq, withAromaticKekuleSelection_nil_of_no_aromaticBonds source noAromatic]

/-- On non-aromatic OpenSMILES input the new public route returns exactly the molecule that the
plain normalization route (`normalizeRawMolecule`) returns.  Thus the authoritative route is a
conservative extension at the public boundary: it adds the Kekule search without perturbing
non-aromatic sources. -/
theorem parseAndNormalizeOpenSMILESAuthoritativeAromaticCertified_eq_plain_of_no_aromaticBonds
    (input : String) (cycles : List AromaticCycle)
    (molecule : RawMolecule) (certified : CertifiedChemistryNormalizationResult)
    (parsed : parseOpenSMILES input = Except.ok molecule)
    (observed :
      parseAndNormalizeOpenSMILESAuthoritativeAromaticCertified input cycles =
        Except.ok certified)
    (noAromatic : aromaticBondOccurrences molecule.normalizeUnspecifiedBonds = []) :
    certified.result.parsed = molecule.normalizeUnspecifiedBonds := by
  obtain ⟨parsedMolecule, candidate, parsedRoute, computed, parsedEq, _certificate, _atoms,
    _edges⟩ :=
    parseAndNormalizeOpenSMILESAuthoritativeAromaticCertified_binding input cycles certified
      observed
  have moleculeEq : parsedMolecule = molecule := by
    have constructorEq : Except.ok parsedMolecule = Except.ok molecule :=
      parsedRoute.symm.trans parsed
    cases constructorEq
    rfl
  subst molecule
  have candidateEq : candidate = parsedMolecule.normalizeUnspecifiedBonds :=
    normalizeAromaticKekule?_eq_source_of_no_aromaticBonds
      parsedMolecule.normalizeUnspecifiedBonds noAromatic computed
  rw [parsedEq, candidateEq]

/-! ## Kekule-choice priority equivalence through the semantic mancude witnesses -/

/-- The remaining exact premise for Kekule-choice priority equivalence: two generated Kekule
realizations of the same source induce the same independent localized mancude edge relation at
equal atom indices.  This is the raw-graph counterpart of the semantic witness
`SemanticAromaticMancudeEdgeSetExact` used by
`AuthoritativeSemanticAromaticKekuleNormalization`; it is deliberately an explicit hypothesis. -/
def SameLocalizedMancudeRelation
    (source : RawMolecule) (leftSelection rightSelection : List RawBond) : Prop :=
  ∀ left right : Fin source.atomCount,
    (withAromaticKekuleSelection source leftSelection).toMoleculeGraph.LocalizedMancudeEdge
        left right ↔
      (withAromaticKekuleSelection source rightSelection).toMoleculeGraph.LocalizedMancudeEdge
        left right

/-- Exact Rule-1a atomic-number observations of two Kekule realizations agree whenever their
independent localized mancude relations agree.  The proof is the existing semantic equivalence
theorem `MoleculeGraph.exactMancudeAverage_eq_of_atomZ_eq_of_localizedMancudeEdge_iff`; Kekule
selection preserves every atom record, so atomic numbers are definitionally equal. -/
theorem exactMancudeAverage_withAromaticKekuleSelection_eq_of_sameLocalized
    (source : RawMolecule) (leftSelection rightSelection : List RawBond)
    (sameLocalized : SameLocalizedMancudeRelation source leftSelection rightSelection)
    (attached : Fin source.atomCount) :
    (withAromaticKekuleSelection source leftSelection).toMoleculeGraph.exactMancudeAverage
        attached =
      (withAromaticKekuleSelection source rightSelection).toMoleculeGraph.exactMancudeAverage
        attached := by
  apply MoleculeGraph.exactMancudeAverage_eq_of_atomZ_eq_of_localizedMancudeEdge_iff
  · intro atom
    rfl
  · exact sameLocalized

/-- The full exact official Rule-1a observation (real atoms, ring duplicates, placeholders, and
multiple-bond duplicates) is likewise independent of the chosen Kekule realization under the same
independently witnessed localized mancude relation. -/
theorem exactOfficialRule1aObservation_withAromaticKekuleSelection_eq_of_sameLocalized
    (source : RawMolecule) (leftSelection rightSelection : List RawBond)
    (sameLocalized : SameLocalizedMancudeRelation source leftSelection rightSelection)
    (node : OfficialCIPNode (Fin source.atomCount)) :
    (withAromaticKekuleSelection source leftSelection).toMoleculeGraph.exactOfficialRule1aObservation
        node =
      (withAromaticKekuleSelection source rightSelection).toMoleculeGraph.exactOfficialRule1aObservation
        node := by
  apply MoleculeGraph.exactOfficialRule1aObservation_eq_of_atomZ_eq_of_localizedMancudeEdge_iff
  · intro atom
    rfl
  · exact sameLocalized

/-- Priority comparison itself is realization independent: the exact Rule-1a weak-priority
relation between any two atoms of the same molecule is unchanged by the Kekule choice once the
localized mancude relation is the same. -/
theorem exactAtomicNumber_weakPriority_withAromaticKekuleSelection_iff
    (source : RawMolecule) (leftSelection rightSelection : List RawBond)
    (sameLocalized : SameLocalizedMancudeRelation source leftSelection rightSelection)
    (attached other : Fin source.atomCount) :
    DeclarativeCIP.ExactAtomicNumber.WeakPriority
        ((withAromaticKekuleSelection source leftSelection).toMoleculeGraph.exactMancudeAverage
          attached)
        ((withAromaticKekuleSelection source leftSelection).toMoleculeGraph.exactMancudeAverage
          other) ↔
      DeclarativeCIP.ExactAtomicNumber.WeakPriority
        ((withAromaticKekuleSelection source rightSelection).toMoleculeGraph.exactMancudeAverage
          attached)
        ((withAromaticKekuleSelection source rightSelection).toMoleculeGraph.exactMancudeAverage
          other) := by
  rw [exactMancudeAverage_withAromaticKekuleSelection_eq_of_sameLocalized source leftSelection
      rightSelection sameLocalized attached,
    exactMancudeAverage_withAromaticKekuleSelection_eq_of_sameLocalized source leftSelection
      rightSelection sameLocalized other]

end TetraStereo.OneCenter.AuthoritativeAromaticPublicFidelity

assert_kernel_only
  TetraStereo.OneCenter.AuthoritativeAromaticPublicFidelity.parseAndNormalizeOpenSMILESAuthoritativeAromaticCertified_sound
assert_kernel_only
  TetraStereo.OneCenter.AuthoritativeAromaticPublicFidelity.parseAndNormalizeOpenSMILESAuthoritativeAromaticCertified_ok_iff
assert_kernel_only
  TetraStereo.OneCenter.AuthoritativeAromaticPublicFidelity.normalizeAromaticChemistryCertified_candidate
assert_kernel_only
  TetraStereo.OneCenter.AuthoritativeAromaticPublicFidelity.normalizeRawMoleculeAuthoritativeAromaticCertified_candidate
assert_kernel_only
  TetraStereo.OneCenter.AuthoritativeAromaticPublicFidelity.parseAndNormalizeOpenSMILESAuthoritativeAromaticCertified_binding
assert_kernel_only
  TetraStereo.OneCenter.AuthoritativeAromaticPublicFidelity.parseAndNormalizeOpenSMILESAuthoritativeAromaticCertified_constitution
assert_kernel_only
  TetraStereo.OneCenter.AuthoritativeAromaticPublicFidelity.parseAndNormalizeOpenSMILESAuthoritativeAromaticCertified_contract
assert_kernel_only
  TetraStereo.OneCenter.AuthoritativeAromaticPublicFidelity.normalizeRawMoleculeAuthoritativeAromaticCertified_chemical_applicability
assert_kernel_only
  TetraStereo.OneCenter.AuthoritativeAromaticPublicFidelity.normalizeRawMoleculeAuthoritativeAromaticCertified_stereochemicalAdmissible
assert_kernel_only
  TetraStereo.OneCenter.AuthoritativeAromaticPublicFidelity.normalizeRawMoleculeAuthoritativeAromaticCertified_positionRankingBackend_total
assert_kernel_only
  TetraStereo.OneCenter.AuthoritativeAromaticPublicFidelity.withAromaticKekuleSelection_nil_of_forall_not_aromatic
assert_kernel_only
  TetraStereo.OneCenter.AuthoritativeAromaticPublicFidelity.withAromaticKekuleSelection_nil_of_no_aromaticBonds
assert_kernel_only
  TetraStereo.OneCenter.AuthoritativeAromaticPublicFidelity.normalizeAromaticKekule?_eq_source_of_no_aromaticBonds
assert_kernel_only
  TetraStereo.OneCenter.AuthoritativeAromaticPublicFidelity.parseAndNormalizeOpenSMILESAuthoritativeAromaticCertified_eq_plain_of_no_aromaticBonds
assert_kernel_only
  TetraStereo.OneCenter.AuthoritativeAromaticPublicFidelity.exactMancudeAverage_withAromaticKekuleSelection_eq_of_sameLocalized
assert_kernel_only
  TetraStereo.OneCenter.AuthoritativeAromaticPublicFidelity.exactOfficialRule1aObservation_withAromaticKekuleSelection_eq_of_sameLocalized
assert_kernel_only
  TetraStereo.OneCenter.AuthoritativeAromaticPublicFidelity.exactAtomicNumber_weakPriority_withAromaticKekuleSelection_iff
