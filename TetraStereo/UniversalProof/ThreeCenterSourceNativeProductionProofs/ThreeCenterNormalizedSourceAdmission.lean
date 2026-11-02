import TetraStereo.UniversalProof.ThreeCenterDrawingSourceProofs.ThreeCenterDrawingSource
import TetraStereo.UniversalProof.SourceNativeRawAnnotationGuardProofs.SourceNativeRawAnnotationGuard
import TetraStereo.OneCenter.AuthoritativeCIPGraph
import TetraStereo.OneCenter.AuthoritativeSingleWedgeOccurrenceDescriptor

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace TetraStereo.UniversalProof.ThreeCenterSourceNativeProductionProofs.ThreeCenterNormalizedSourceAdmission

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.UniversalProof.SourceNativeRawAnnotationGuardProofs.SourceNativeDevelopmentTransaction
open TetraStereo.UniversalProof.SourceNativeRawAnnotationGuardProofs.SourceNativeRawAnnotationGuard







































/-! ## 0. The target source, unchanged -/



abbrev targetSource : AuthoritativeChemicalInput :=
  TetraStereo.UniversalProof.ThreeCenterDrawingSourceProofs.ThreeCenterDrawingSource.source

theorem target_structurallyWellFormed : targetSource.StructurallyWellFormed :=
  TetraStereo.UniversalProof.ThreeCenterDrawingSourceProofs.ThreeCenterDrawingSource.source_structurallyWellFormed

/-! ## 1. Raw literal constitution in the actual source interaction order -/

/-- Total extraction of one raw single-bond record from a semantic interaction's participant order.
The two real participants are preserved in written order; the fallback is only total, and is proved
unreachable on the target source's interactions via `isSinglePair?`. -/
def rawBondOfInteraction (interaction : SemanticInteraction) : RawBond :=
  match interaction.participants with
  | [left, right] => ⟨left, right, ParsedBondKind.single⟩
  | _ => ⟨0, 0, ParsedBondKind.single⟩

/-- Executable test that an interaction is exactly one two-participant covalent single bond. -/
def isSinglePair? (interaction : SemanticInteraction) : Bool :=
  match interaction.participants with
  | [_, _] => decide (interaction.kind = SemanticInteractionKind.covalent 1)
  | _ => false

theorem rawBondOfInteraction_kind (interaction : SemanticInteraction) :
    (rawBondOfInteraction interaction).kind = ParsedBondKind.single := by
  unfold rawBondOfInteraction
  split <;> rfl

theorem isSinglePair?_eq_true_iff (interaction : SemanticInteraction) :
    isSinglePair? interaction = true ↔
      ∃ left right, interaction.participants = [left, right] ∧
        interaction.kind = SemanticInteractionKind.covalent 1 := by
  obtain ⟨participants, kind⟩ := interaction
  cases participants with
  | nil => simp [isSinglePair?]
  | cons _ rest =>
      cases rest with
      | nil => simp [isSinglePair?]
      | cons _ tail =>
          cases tail with
          | nil => simp [isSinglePair?]
          | cons _ _ => simp [isSinglePair?]

/-- A two-participant covalent single bond round-trips exactly through extraction and the semantic
interaction bridge. -/
theorem rawBondOfInteraction_toSemanticInteraction (interaction : SemanticInteraction)
    (accepted : isSinglePair? interaction = true) :
    (rawBondOfInteraction interaction).toSemanticInteraction = interaction := by
  obtain ⟨participants, kind⟩ := interaction
  obtain ⟨left, right, participantsEq, kindEq⟩ :=
    (isSinglePair?_eq_true_iff ⟨participants, kind⟩).mp accepted
  subst participantsEq
  subst kindEq
  rfl

/-- The whole derived record list maps back to the actual interaction list. -/
theorem map_rawBondOfInteraction_toSemanticInteraction (interactions : List SemanticInteraction)
    (accepted : interactions.all isSinglePair? = true) :
    (interactions.map rawBondOfInteraction).map RawBond.toSemanticInteraction = interactions := by
  induction interactions with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      have headAccepted : isSinglePair? head = true :=
        (List.all_eq_true.mp accepted) head (by simp)
      have tailAccepted : tail.all isSinglePair? = true :=
        List.all_eq_true.mpr fun interaction member =>
          (List.all_eq_true.mp accepted) interaction (List.mem_cons_of_mem head member)
      simp only [List.map_cons]
      rw [rawBondOfInteraction_toSemanticInteraction head headAccepted,
        inductionHypothesis tailAccepted]




def rawLiteral : RawMolecule where
  atoms :=
    [AtomSpec.aliphatic .F, AtomSpec.aliphatic .C, AtomSpec.aliphatic .Cl,
      AtomSpec.aliphatic .C, AtomSpec.aliphatic .Br, AtomSpec.aliphatic .I,
      AtomSpec.aliphatic .C, AtomSpec.aliphatic .Br, AtomSpec.aliphatic .I,
      AtomSpec.aliphatic .H, AtomSpec.aliphatic .H]
  bonds := targetSource.molecule.interactions.map rawBondOfInteraction

theorem rawLiteral_atomCount : rawLiteral.atomCount = 11 := rfl

theorem rawLiteral_all_single :
    ∀ bond ∈ rawLiteral.bonds, bond.kind = ParsedBondKind.single := by
  intro bond member
  have member' : bond ∈ targetSource.molecule.interactions.map rawBondOfInteraction := member
  obtain ⟨interaction, _, rfl⟩ := List.mem_map.mp member'
  exact rawBondOfInteraction_kind interaction

/-- The derived raw records map back to exactly the actual source interactions.  This is the
structural derivation of the raw record order from the source molecule, not an assumed equality. -/
theorem rawLiteral_interactions :
    rawLiteral.bonds.map RawBond.toSemanticInteraction = targetSource.molecule.interactions := by
  show (targetSource.molecule.interactions.map rawBondOfInteraction).map
      RawBond.toSemanticInteraction = targetSource.molecule.interactions
  exact map_rawBondOfInteraction_toSemanticInteraction _ (by decide +kernel)

/-- The raw literal converts to precisely the target source's semantic molecule. -/
theorem rawLiteral_toSemanticMolecule :
    rawLiteral.toSemanticMolecule? = some targetSource.molecule := by
  decide +kernel

/-! ## 2. Normalization and the four certification guards -/

def normalizedLiteral : ChemistryNormalizationResult := normalizeRawMolecule rawLiteral

/-- A raw record already carrying the single-bond kind is left fixed by the unspecified-bond
normalizer. -/
theorem normalizeUnspecifiedBond_eq_self_of_single (mol : RawMolecule) (bond : RawBond)
    (kindEq : bond.kind = ParsedBondKind.single) : mol.normalizeUnspecifiedBond bond = bond := by
  unfold RawMolecule.normalizeUnspecifiedBond
  rw [kindEq]

theorem map_normalizeUnspecifiedBond_eq_self (mol : RawMolecule) (bonds : List RawBond)
    (resolved : ∀ bond ∈ bonds, bond.kind = ParsedBondKind.single) :
    bonds.map mol.normalizeUnspecifiedBond = bonds := by
  induction bonds with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      have headEq : mol.normalizeUnspecifiedBond head = head :=
        normalizeUnspecifiedBond_eq_self_of_single mol head (resolved head (by simp))
      have tailEq : tail.map mol.normalizeUnspecifiedBond = tail :=
        inductionHypothesis (fun bond member => resolved bond (by simp [member]))
      simp only [List.map_cons, headEq, tailEq]

theorem normalizeUnspecifiedBonds_eq_self_of_all_single (mol : RawMolecule)
    (resolved : ∀ bond ∈ mol.bonds, bond.kind = ParsedBondKind.single) :
    mol.normalizeUnspecifiedBonds = mol := by
  unfold RawMolecule.normalizeUnspecifiedBonds
  rw [map_normalizeUnspecifiedBond_eq_self mol mol.bonds resolved]

/-- The literal has no unspecified bond, so its normalized parser product is itself. -/
theorem normalizedLiteral_parsed : normalizedLiteral.parsed = rawLiteral :=
  normalizeUnspecifiedBonds_eq_self_of_all_single rawLiteral rawLiteral_all_single

/-- The normalized parser product converts to precisely the target source molecule. -/
theorem normalizedLiteral_constitutional :
    normalizedLiteral.parsed.toSemanticMolecule? = some targetSource.molecule := by
  rw [normalizedLiteral_parsed]
  exact rawLiteral_toSemanticMolecule

theorem normalizedLiteral_admissible : normalizedLiteral.parsed.Admissible :=
  (RawMolecule.admissible?_eq_true_iff _).mp (by decide +kernel)

theorem normalizedLiteral_writtenNeighborExact :
    normalizedLiteral.parsed.WrittenNeighborExact :=
  (RawMolecule.writtenNeighborExact?_eq_true_iff _).mp (by decide +kernel)

theorem normalizedLiteral_valenceOK : normalizedLiteral.parsed.ValenceOK :=
  (RawMolecule.valenceOK?_eq_true_iff _).mp (by decide +kernel)

theorem normalizedLiteral_rule2MassesKnown : normalizedLiteral.parsed.Rule2MassesKnown :=
  (RawMolecule.rule2MassesKnown?_eq_true_iff _).mp (by decide +kernel)

/-- The kernel-admitted normalization certificate of the actual raw literal.  All four guards are
discharged by their own reflection theorem applied to an executable check of the concrete
normalized molecule; no normalization check is assumed. -/
def certifiedLiteral : CertifiedChemistryNormalizationResult where
  result := normalizedLiteral
  admissible := normalizedLiteral_admissible
  writtenNeighborExact := normalizedLiteral_writtenNeighborExact
  valenceOK := normalizedLiteral_valenceOK
  rule2MassesKnown := normalizedLiteral_rule2MassesKnown

/-! ## 3. Actual localized CIP graph and electronic readiness -/

/-- The actual target molecule is in the exact explicit localized closed-shell pair-bond domain of
the direct CIP graph. -/
theorem target_graphReady : targetSource.molecule.LocalizedCIPGraphReady :=
  (SemanticMolecule.localizedCIPGraphReady?_eq_true_iff _).mp (by decide +kernel)

/-- The structurally certified, graph-ready authority input of the target source. -/
def certifiedLocalizedCIPInput : CertifiedLocalizedCIPInput where
  certified :=
    { input := targetSource
      structurallyWellFormed := target_structurallyWellFormed }
  graphReady := target_graphReady

/-- The graph the CIP layer actually consumes is exactly the target molecule's localized graph. -/
theorem certifiedLocalizedCIPInput_actualGraph :
    certifiedLocalizedCIPInput.moleculeGraph =
      targetSource.molecule.toLocalizedMoleculeGraph := rfl

/-- The all-single constitution has no ordinary double-bond endpoint pair. -/
theorem target_no_ordinary_double_bond :
    targetSource.NoAromaticCanonicalOrdinaryDoubleBond := by
  intro left right ordinary
  have noOrderTwo :
      ∀ first second : targetSource.AromaticCanonicalAtom,
        targetSource.molecule.aromaticCanonicalBondOrder first.val second.val ≠ 2 := by
    decide
  exact noOrderTwo left right ordinary.2

/-- The empty electronic-state family is ready: the source is structurally well formed, the empty
record list is well formed, and every directed individual-double-bond endpoint clause is vacuously
satisfied on the all-single constitution. -/
theorem target_empty_supplied_ready :
    targetSource.MainGroupLewisGeneralHybridCertificationReady [] := by
  refine ⟨target_structurallyWellFormed, ?_, ?_⟩
  · exact ⟨by simp, by simp⟩
  · intro endpoint partner directed
    exact absurd directed
      (noDirectedEndpoint_of_noOrdinaryDoubleBond targetSource
        target_no_ordinary_double_bond endpoint partner)

/-! ## 4. Annotation-free future guarded transaction -/

theorem rawLiteral_parsed_atoms : normalizedLiteral.parsed.atoms = rawLiteral.atoms := by
  rw [normalizedLiteral_parsed]

theorem rawLiteral_parsed_bonds : normalizedLiteral.parsed.bonds = rawLiteral.bonds := by
  rw [normalizedLiteral_parsed]

/-- No literal atom carries a parser parity annotation. -/
theorem normalizedLiteral_atoms_tetrahedral_none :
    ∀ atom ∈ normalizedLiteral.parsed.atoms, atom.tetrahedral? = none := by
  rw [rawLiteral_parsed_atoms]
  have checked :
      rawLiteral.atoms.all (fun atom => decide (atom.tetrahedral? = none)) = true := by decide
  intro atom member
  exact of_decide_eq_true ((List.all_eq_true.mp checked) atom member)

/-- No literal bond record carries a directional `/` or `\` marker. -/
theorem normalizedLiteral_bonds_directional_none :
    ∀ bond ∈ normalizedLiteral.parsed.bonds, bond.kind.directional? = none := by
  rw [rawLiteral_parsed_bonds]
  intro bond member
  have member' : bond ∈ targetSource.molecule.interactions.map rawBondOfInteraction := member
  obtain ⟨interaction, _, rfl⟩ := List.mem_map.mp member'
  rw [rawBondOfInteraction_kind]
  rfl

/-- An inhabited future development request over the actual target source.  No spatial channel,
label or auxiliary value from any earlier fixture is transported. -/
noncomputable def admissionRequest : SourceNativeDevelopmentRequest where
  normalized := certifiedLiteral
  input := certifiedLocalizedCIPInput
  supplied := []
  electronicReady := target_empty_supplied_ready
  carrierFuel := 1
  semantics := SingleWedgeSource.occurrenceOrdinaryAuxiliarySemantics targetSource 1 4
  ruleFuel := 4

/-- The request's constitutional agreement is exactly the normalized literal conversion. -/
theorem admissionRequest_constitutionalAgreement :
    admissionRequest.ConstitutionalAgreement := by
  unfold SourceNativeDevelopmentRequest.ConstitutionalAgreement
  rw [show admissionRequest.normalized.result.parsed.toSemanticMolecule? =
        normalizedLiteral.parsed.toSemanticMolecule? from rfl,
      show admissionRequest.source = targetSource from rfl]
  exact normalizedLiteral_constitutional

/-- **RawAnnotationFree.**  The preserved conservative guard's independent meaning holds for the
actual normalized records, so the future transaction passes the raw-annotation gate.
Underlying production success is separate. This is an actual property of the literal, not a bypass. -/
theorem admissionRequest_annotationFree : RawAnnotationFree admissionRequest := by
  unfold RawAnnotationFree
  constructor
  · intro atom member
    have same : admissionRequest.normalized.result.parsed.atoms = rawLiteral.atoms := rfl
    exact normalizedLiteral_atoms_tetrahedral_none atom (same ▸ member)
  · intro bond member
    have same : admissionRequest.normalized.result.parsed.bonds = rawLiteral.bonds := rfl
    exact normalizedLiteral_bonds_directional_none bond (same ▸ member)

/-- The conservative guard does not restrict this payload: guarded production is the underlying
production.  Whether that production succeeds is a separate downstream obligation. -/
theorem admissionRequest_guardedProduce_eq_produce :
    guardedProduce admissionRequest = admissionRequest.produce := by
  unfold guardedProduce
  rw [if_pos ((rawAnnotationIssues_eq_nil_iff admissionRequest).mpr
    admissionRequest_annotationFree)]

end TetraStereo.UniversalProof.ThreeCenterSourceNativeProductionProofs.ThreeCenterNormalizedSourceAdmission
