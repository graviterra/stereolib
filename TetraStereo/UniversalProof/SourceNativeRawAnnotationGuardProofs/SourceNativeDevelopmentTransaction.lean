import TetraStereo.UniversalProof.ScheduledDrawingSpatialEndToEndProofs.ScheduledDrawingSpatialEndToEnd
import TetraStereo.OneCenter.AuthoritativeSingleWedgeProductionKeyReadiness
import TetraStereo.OneCenter.AuthoritativeCIPGraph

set_option autoImplicit false

namespace TetraStereo.UniversalProof.SourceNativeRawAnnotationGuardProofs.SourceNativeDevelopmentTransaction

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.ScheduledDrawingSpatialEndToEndProofs.ScheduledDrawingSpatialIntegration
open TetraStereo.UniversalProof.ScheduledDrawingSpatialEndToEndProofs.ScheduledDrawingSpatialWholeMolecule
open TetraStereo.UniversalProof.ScheduledDrawingSpatialEndToEndProofs.ScheduledDrawingSpatialEndToEnd
























/-! ## 1. Typed source-wide annotation issues -/



inductive AnnotationIssue (source : AuthoritativeChemicalInput) where
  | unsupportedAtomConfiguration (atom : ℕ) (parity : TetrahedralInputParity)
      (scope : DiagramConfigurationScope)
  | nonAbsoluteBondScope (bond : DiagramBond)
  | unsupportedBondStyle (bond : DiagramBond)
  | bondWithoutSemanticBinaryPartner (bond : DiagramBond)
  | unrecognizedWedgeSource (bond : DiagramBond)
  | unrepresentedWedgeSource (bond : DiagramBond)
  | annotatedCenterUnassigned (center : source.AromaticCanonicalAtom)
  | tetrahedralStatusConflict (center : source.AromaticCanonicalAtom)
  deriving DecidableEq

/-- An actual binary source bond has exactly two participants. Ordinary covalent orders must
be positive; order two and higher remain permitted for plain drawing records. -/
def IsActualBinaryBond (interaction : SemanticInteraction) : Prop :=
  ∃ left right,
    interaction.participants = [left, right] ∧
      (interaction.kind = .unspecifiedCovalent ∨ interaction.kind = .aromatic ∨
        ∃ order, interaction.kind = .covalent order ∧ 0 < order)

def actualBinaryBond? (interaction : SemanticInteraction) : Bool :=
  match interaction.participants, interaction.kind with
  | [_, _], .unspecifiedCovalent => true
  | [_, _], .aromatic => true
  | [_, _], .covalent order => decide (0 < order)
  | _, _ => false

/-- Exact executable/declarative correspondence for the binary source-bond test. -/
theorem actualBinaryBond?_eq_true_iff (interaction : SemanticInteraction) :
    actualBinaryBond? interaction = true ↔ IsActualBinaryBond interaction := by
  rcases interaction with ⟨participants, kind⟩
  rcases participants with _ | ⟨left, tail⟩
  · simp [actualBinaryBond?, IsActualBinaryBond]
  rcases tail with _ | ⟨right, rest⟩
  · simp [actualBinaryBond?, IsActualBinaryBond]
  rcases rest with _ | ⟨third, rest⟩
  · cases kind <;> simp [actualBinaryBond?, IsActualBinaryBond]
  · simp [actualBinaryBond?, IsActualBinaryBond]

/-- A diagram bond is backed when some actual source interaction is a binary bond between the two
drawn endpoints, in either participant order. -/
def hasActualBinaryBond? (source : AuthoritativeChemicalInput) (bond : DiagramBond) : Bool :=
  source.molecule.interactions.any fun interaction =>
    actualBinaryBond? interaction &&
      (decide (interaction.participants = [bond.source, bond.target]) ||
        decide (interaction.participants = [bond.target, bond.source]))

theorem hasActualBinaryBond?_eq_true_iff (source : AuthoritativeChemicalInput)
    (bond : DiagramBond) :
    hasActualBinaryBond? source bond = true ↔
      ∃ interaction ∈ source.molecule.interactions,
        IsActualBinaryBond interaction ∧
          (interaction.participants = [bond.source, bond.target] ∨
            interaction.participants = [bond.target, bond.source]) := by
  unfold hasActualBinaryBond?
  rw [List.any_eq_true]
  constructor
  · rintro ⟨interaction, present, accepted⟩
    rw [Bool.and_eq_true, Bool.or_eq_true] at accepted
    refine ⟨interaction, present, (actualBinaryBond?_eq_true_iff interaction).mp accepted.1, ?_⟩
    rcases accepted.2 with directed | reversed
    · exact Or.inl (of_decide_eq_true directed)
    · exact Or.inr (of_decide_eq_true reversed)
  · rintro ⟨interaction, present, binary, ordered⟩
    refine ⟨interaction, present, ?_⟩
    rw [Bool.and_eq_true, Bool.or_eq_true]
    refine ⟨(actualBinaryBond?_eq_true_iff interaction).mpr binary, ?_⟩
    rcases ordered with directed | reversed
    · exact Or.inl (by simp [directed])
    · exact Or.inr (by simp [reversed])

/-- A wedge source centre is recognized when it is a real source atom whose actual single-wedge
extraction succeeds. This reads the source, never an asserted local frame. -/
def wedgeCenterRecognized? (source : AuthoritativeChemicalInput) (bond : DiagramBond) : Bool :=
  if bound : bond.source < source.molecule.atomCount then
    (extract? source ⟨bond.source, bound⟩).isSome
  else false

theorem wedgeCenterRecognized?_eq_true_iff (source : AuthoritativeChemicalInput)
    (bond : DiagramBond) :
    wedgeCenterRecognized? source bond = true ↔
      ∃ _bound : bond.source < source.molecule.atomCount,
        Recognized source bond.source := by
  unfold wedgeCenterRecognized?
  by_cases bound : bond.source < source.molecule.atomCount
  · rw [dif_pos bound]
    rw [Option.isSome_iff_exists]
    constructor
    · rintro ⟨frame, extracted⟩
      exact ⟨bound, (recognized_iff_exists_extracted_frame source ⟨bond.source, bound⟩).mpr
        ⟨frame, extracted⟩⟩
    · rintro ⟨_, recognized⟩
      rcases (recognized_iff_exists_extracted_frame source ⟨bond.source, bound⟩).mp recognized with
        ⟨frame, extracted⟩
      exact ⟨frame, extracted⟩
  · rw [dif_neg bound]
    constructor
    · intro impossible; exact absurd impossible (by simp)
    · rintro ⟨impossible, _⟩; exact absurd impossible bound

def actualSourceNeighbors (source : AuthoritativeChemicalInput)
    (center : source.AromaticCanonicalAtom) : List source.AromaticCanonicalAtom :=
  (List.finRange source.molecule.atomCount).filter fun neighbor =>
    decide (center ≠ neighbor ∧ semanticEdgeKey center.val neighbor.val ∈
      source.molecule.aromaticNormalizedPairKeys)

theorem actualSourceNeighbors_length_eq_card (source : AuthoritativeChemicalInput)
    (center : source.AromaticCanonicalAtom) :
    (actualSourceNeighbors source center).length = (source.aromaticCanonicalNeighborFinset center).card := by
  classical
  have same : (actualSourceNeighbors source center).toFinset =
      source.aromaticCanonicalNeighborFinset center := by
    ext neighbor
    simp [actualSourceNeighbors, mem_aromaticCanonicalNeighborFinset_iff, AromaticCanonicalAdjacent]
  rw [← same]
  exact (List.toFinset_card_of_nodup
    ((List.nodup_finRange source.molecule.atomCount).filter _)).symm

/-- Computable finite perception test, reflected against the actual canonical candidate set. -/
def wedgeSourcePerceived? (source : AuthoritativeChemicalInput) (bond : DiagramBond) : Bool :=
  if bound : bond.source < source.molecule.atomCount then
    decide (ConnectivityOnlyTetrahedralPeriodicElement
      (source.molecule.atoms.get ⟨bond.source, bound⟩).element) &&
      decide ((actualSourceNeighbors source ⟨bond.source, bound⟩).length = 4)
  else false

theorem wedgeSourcePerceived?_eq_true_iff (source : AuthoritativeChemicalInput) (bond : DiagramBond) :
    wedgeSourcePerceived? source bond = true ↔
      ∃ bound : bond.source < source.molecule.atomCount,
        (⟨bond.source, bound⟩ : source.AromaticCanonicalAtom) ∈ source.aromaticCanonicalTetrahedralCenterSet := by
  unfold wedgeSourcePerceived?
  by_cases bound : bond.source < source.molecule.atomCount
  · simp only [dif_pos bound, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · intro accepted
      refine ⟨bound, (source.mem_aromaticCanonicalTetrahedralCenterSet_iff _).mpr ?_⟩
      exact ⟨accepted.1, (actualSourceNeighbors_length_eq_card source _).symm.trans accepted.2⟩
    · rintro ⟨_, accepted⟩
      have meaning := (source.mem_aromaticCanonicalTetrahedralCenterSet_iff _).mp accepted
      exact ⟨meaning.1, (actualSourceNeighbors_length_eq_card source _).trans meaning.2⟩
  · simp [bound]

/-- Every diagram record is audited. Wedge recognition and representation are separate checks:
even a locally recognized source cannot silently disappear from the whole-molecule report. -/
def bondAuditIssues (source : AuthoritativeChemicalInput) (bond : DiagramBond) :
    List (AnnotationIssue source) :=
  (if bond.scope = .absolute then [] else [AnnotationIssue.nonAbsoluteBondScope bond]) ++
    (if hasActualBinaryBond? source bond then []
     else [AnnotationIssue.bondWithoutSemanticBinaryPartner bond]) ++
      (match bond.style with
       | .plain => []
       | .solidWedge | .hashedWedge =>
           (if wedgeCenterRecognized? source bond then []
            else [AnnotationIssue.unrecognizedWedgeSource bond]) ++
             (if wedgeSourcePerceived? source bond then []
              else [AnnotationIssue.unrepresentedWedgeSource bond])
       | _ => [AnnotationIssue.unsupportedBondStyle bond])

/-- All diagram-derived issues. Every atom configuration is unsupported until independent
written-order annotation semantics exists; every bond is audited through `bondAuditIssues`. A source
without a diagram raises no annotation issue, but the conflict guard below still applies. -/
def diagramAuditIssues (source : AuthoritativeChemicalInput) : List (AnnotationIssue source) :=
  match source.diagram? with
  | none => []
  | some diagram =>
      diagram.atomConfigurations.map (fun configuration =>
        AnnotationIssue.unsupportedAtomConfiguration configuration.atom configuration.parity
          configuration.scope) ++
        diagram.bonds.flatMap (bondAuditIssues source)

/-- Atom configurations and every solid/hashed wedge source require an assigned report row. -/
def annotatedAtoms (source : AuthoritativeChemicalInput) : List ℕ :=
  match source.diagram? with
  | none => []
  | some diagram =>
      diagram.atomConfigurations.map (fun configuration => configuration.atom) ++
        (diagram.bonds.filter fun bond =>
          decide (bond.style = .solidWedge ∨ bond.style = .hashedWedge)).map DiagramBond.source

theorem wedge_source_mem_annotatedAtoms (source : AuthoritativeChemicalInput)
    (diagram : DiagramConfiguration) (observed : source.diagram? = some diagram)
    (bond : DiagramBond) (present : bond ∈ diagram.bonds)
    (wedge : bond.style = .solidWedge ∨ bond.style = .hashedWedge) :
    bond.source ∈ annotatedAtoms source := by
  unfold annotatedAtoms
  rw [observed]
  exact List.mem_append.mpr (Or.inr (List.mem_map.mpr
    ⟨bond, List.mem_filter.mpr ⟨present, by simpa using wedge⟩, rfl⟩))

theorem unrepresented_wedge_issue_mem (source : AuthoritativeChemicalInput) (bond : DiagramBond)
    (wedge : bond.style = .solidWedge ∨ bond.style = .hashedWedge)
    (absent : wedgeSourcePerceived? source bond = false) :
    AnnotationIssue.unrepresentedWedgeSource bond ∈ bondAuditIssues source bond := by
  rcases wedge with solid | hashed
  · simp [bondAuditIssues, solid, absent]
  · simp [bondAuditIssues, hashed, absent]

/-- Every tetrahedral report conflict, and every unassigned status at an annotated centre. -/
noncomputable def tetrahedralAuditIssues (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel) (ruleFuel : Nat) :
    List (AnnotationIssue source) :=
  (scheduledTetrahedralReport source semantics ruleFuel).filterMap fun row =>
    match row.status with
    | .conflict => some (AnnotationIssue.tetrahedralStatusConflict row.center.1)
    | .unassigned =>
        if row.center.1.val ∈ annotatedAtoms source then
          some (AnnotationIssue.annotatedCenterUnassigned row.center.1)
        else none
    | .assigned _ => none

theorem annotated_unassigned_issue_mem (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel) (ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (annotated : center.1.val ∈ annotatedAtoms source)
    (unassigned : scheduledDrawingSpatialStatus source semantics ruleFuel center = .unassigned) :
    AnnotationIssue.annotatedCenterUnassigned center.1 ∈ tetrahedralAuditIssues source semantics ruleFuel := by
  apply List.mem_filterMap.mpr
  refine ⟨⟨center, .unassigned⟩,
    (mem_scheduledTetrahedralReport_iff source semantics ruleFuel _).mpr unassigned.symm, ?_⟩
  simp [annotated]

/-! ## 2. The source-native development request -/

/-- A closed development request. It owns the exact constitutional agreement datum, the two
kernel-admitted certificates, the supplied electronic records with their actual readiness proof, and
one explicit auxiliary rule semantics. No scientific-adoption field is asserted. -/
structure SourceNativeDevelopmentRequest where
  normalized : CertifiedChemistryNormalizationResult
  input : CertifiedLocalizedCIPInput
  supplied : List input.certified.input.AromaticCanonicalAtomElectronicStateRecord
  electronicReady :
    input.certified.input.MainGroupLewisGeneralHybridCertificationReady supplied
  carrierFuel : Nat
  semantics : input.certified.input.AromaticCanonicalRuleSemantics carrierFuel
  ruleFuel : Nat

namespace SourceNativeDevelopmentRequest

/-- The format-neutral source owned by the request. -/
def source (request : SourceNativeDevelopmentRequest) : AuthoritativeChemicalInput :=
  request.input.certified.input

/-- Exact constitutional agreement: the normalized parser product converts to precisely the
request's semantic molecule. This is deliberately *not* parser-diagram equality, since a genuine
wedge drawing differs from any plain diagram materialisation. -/
def ConstitutionalAgreement (request : SourceNativeDevelopmentRequest) : Prop :=
  request.normalized.result.parsed.toSemanticMolecule? = some request.source.molecule


noncomputable def auditIssues (request : SourceNativeDevelopmentRequest) :
    List (AnnotationIssue request.source) :=
  diagramAuditIssues request.source ++
    tetrahedralAuditIssues request.source request.semantics request.ruleFuel

/-- The actual development payload: the committed whole-molecule analyzer, never fabricated
assignments. -/
noncomputable def report (request : SourceNativeDevelopmentRequest) :
    List (ScheduledHybridRepresentedResult request.source) :=
  analyzeScheduledHybridRepresentedOfReady request.source request.supplied request.electronicReady
    request.semantics request.ruleFuel



noncomputable def produce (request : SourceNativeDevelopmentRequest) :
    Option (List (ScheduledHybridRepresentedResult request.source)) := by
  classical
  exact if request.ConstitutionalAgreement ∧ request.auditIssues = [] then some request.report else none

/-- **Exact success characterisation.** -/
theorem produce_eq_some_iff (request : SourceNativeDevelopmentRequest)
    (rows : List (ScheduledHybridRepresentedResult request.source)) :
    request.produce = some rows ↔
      request.ConstitutionalAgreement ∧ request.auditIssues = [] ∧ rows = request.report := by
  unfold produce
  by_cases accepted : request.ConstitutionalAgreement ∧ request.auditIssues = []
  · rw [if_pos accepted]
    simp only [Option.some.injEq]
    constructor
    · intro same
      exact ⟨accepted.1, accepted.2, same.symm⟩
    · rintro ⟨agreement, issues, rfl⟩
      rfl
  · rw [if_neg accepted]
    constructor
    · intro impossible; exact absurd impossible (by simp)
    · rintro ⟨agreement, issues, _⟩; exact absurd ⟨agreement, issues⟩ accepted

/-- **Exact global refusal.** -/
theorem produce_eq_none_iff (request : SourceNativeDevelopmentRequest) :
    request.produce = none ↔
      ¬ request.ConstitutionalAgreement ∨ request.auditIssues ≠ [] := by
  unfold produce
  by_cases accepted : request.ConstitutionalAgreement ∧ request.auditIssues = []
  · rw [if_pos accepted]
    constructor
    · intro impossible; exact absurd impossible (by simp)
    · rintro (agreement | issues)
      · exact absurd accepted.1 agreement
      · exact absurd accepted.2 issues
  · rw [if_neg accepted]
    constructor
    · intro _
      by_cases agreement : request.ConstitutionalAgreement
      · exact Or.inr fun issues => accepted ⟨agreement, issues⟩
      · exact Or.inl agreement
    · intro _
      rfl

/-- **Declarative soundness of every emitted row**, by the committed whole-molecule theorem. -/
theorem report_member_sound (request : SourceNativeDevelopmentRequest)
    (result : ScheduledHybridRepresentedResult request.source) (present : result ∈ request.report) :
    ScheduledHybridRepresentedMeaning request.source request.supplied request.electronicReady
      request.semantics request.ruleFuel result :=
  analyzeScheduledHybridRepresentedOfReady_member_sound request.source request.supplied
    request.electronicReady request.semantics request.ruleFuel result present

/-- **Success soundness.** A successful production can only return the actual payload, and every
member of that payload carries its independent declarative meaning. -/
theorem produce_eq_some_member_sound (request : SourceNativeDevelopmentRequest)
    (rows : List (ScheduledHybridRepresentedResult request.source))
    (computed : request.produce = some rows) (result : ScheduledHybridRepresentedResult request.source)
    (present : result ∈ rows) :
    ScheduledHybridRepresentedMeaning request.source request.supplied request.electronicReady
      request.semantics request.ruleFuel result := by
  obtain ⟨_, _, rfl⟩ := (produce_eq_some_iff request rows).mp computed
  exact report_member_sound request result present


theorem produce_eq_none_of_diagramIssues_ne_nil (request : SourceNativeDevelopmentRequest)
    (nonempty : diagramAuditIssues request.source ≠ []) : request.produce = none := by
  refine (produce_eq_none_iff request).mpr (Or.inr ?_)
  intro empty
  exact nonempty (List.append_eq_nil_iff.mp (by simpa [auditIssues] using empty)).1


theorem produce_eq_none_of_tetrahedralIssues_ne_nil (request : SourceNativeDevelopmentRequest)
    (nonempty : tetrahedralAuditIssues request.source request.semantics request.ruleFuel ≠ []) :
    request.produce = none := by
  refine (produce_eq_none_iff request).mpr (Or.inr ?_)
  intro empty
  exact nonempty (List.append_eq_nil_iff.mp (by simpa [auditIssues] using empty)).2

end SourceNativeDevelopmentRequest

/-! ## 3. Symmetric ordinary double bond, and the empty supplied electronic readiness -/

theorem aromaticCanonicalBondOrder_comm (molecule : SemanticMolecule) (left right : ℕ) :
    molecule.aromaticCanonicalBondOrder left right =
      molecule.aromaticCanonicalBondOrder right left := by
  unfold SemanticMolecule.aromaticCanonicalBondOrder
  rw [semanticEdgeKey_comm left right, SemanticMolecule.localizedBondOrder_comm]

theorem aromaticCanonicalAdjacent_comm (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalAtom) :
    source.AromaticCanonicalAdjacent left right ↔
      source.AromaticCanonicalAdjacent right left := by
  unfold AromaticCanonicalAdjacent
  rw [semanticEdgeKey_comm left.val right.val]
  exact ⟨fun h => ⟨fun same => h.1 same.symm, h.2⟩,
    fun h => ⟨fun same => h.1 same.symm, h.2⟩⟩

theorem aromaticCanonicalOrdinaryDoubleBond_comm (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalAtom) :
    source.AromaticCanonicalOrdinaryDoubleBond left right ↔
      source.AromaticCanonicalOrdinaryDoubleBond right left := by
  unfold AromaticCanonicalOrdinaryDoubleBond
  constructor
  · rintro ⟨adjacent, order⟩
    exact ⟨(aromaticCanonicalAdjacent_comm source left right).mp adjacent,
      by rw [aromaticCanonicalBondOrder_comm]; exact order⟩
  · rintro ⟨adjacent, order⟩
    exact ⟨(aromaticCanonicalAdjacent_comm source left right).mpr adjacent,
      by rw [aromaticCanonicalBondOrder_comm]; exact order⟩

/-- A source with no ordinary double bond has no directed individual double-bond endpoint. This is
readiness for double endpoints only, not a universal-valence claim. -/
theorem noDirectedEndpoint_of_noOrdinaryDoubleBond (source : AuthoritativeChemicalInput)
    (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond)
    (endpoint partner : source.AromaticCanonicalAtom) :
    ¬ source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint endpoint partner := by
  rintro ⟨bond, _present, ordered | reversed⟩
  · rcases ordered with ⟨rfl, rfl⟩
    exact noDouble bond.left bond.right bond.ordinary
  · rcases reversed with ⟨rfl, rfl⟩
    exact noDouble bond.right bond.left
      ((aromaticCanonicalOrdinaryDoubleBond_comm source bond.left bond.right).mp bond.ordinary)

/-! ## 4. Closed inhabited request over `SingleWedgeSourceRegression.source` -/

namespace ClosedSource

open SingleWedgeSourceRegression

/-- One raw single bond between two parser indices. -/
def rawBond (source target : ℕ) : RawBond := ⟨source, target, .single⟩

/-- The literal CFClBrI raw molecule: carbon with fluorine, chlorine, bromine and iodine. -/
def rawCF : RawMolecule where
  atoms := [AtomSpec.aliphatic .C, AtomSpec.aliphatic .F, AtomSpec.aliphatic .Cl,
    AtomSpec.aliphatic .Br, AtomSpec.aliphatic .I]
  bonds := [rawBond 0 1, rawBond 0 2, rawBond 0 3, rawBond 0 4]

def normalizedCF : ChemistryNormalizationResult := normalizeRawMolecule rawCF

/-- Every non-smiles bond is already ordinary single, so normalization leaves the molecule fixed. -/
theorem normalizedCF_parsed : normalizedCF.parsed = rawCF := by
  show rawCF.normalizeUnspecifiedBonds = rawCF
  decide +kernel

/-- The certified normalization result. Each of the four fields is closed by its own reflection
theorem from an executable check of the concrete normalized molecule. -/
def certifiedCF : CertifiedChemistryNormalizationResult where
  result := normalizedCF
  admissible := (normalizedCF.parsed.admissible?_eq_true_iff).mp (by decide +kernel)
  writtenNeighborExact :=
    (normalizedCF.parsed.writtenNeighborExact?_eq_true_iff).mp (by decide +kernel)
  valenceOK := (normalizedCF.parsed.valenceOK?_eq_true_iff).mp (by decide +kernel)
  rule2MassesKnown := (normalizedCF.parsed.rule2MassesKnown?_eq_true_iff).mp (by decide +kernel)

theorem source_structurallyWellFormed :
    SingleWedgeSourceRegression.source.StructurallyWellFormed :=
  (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff _).mp (by decide +kernel)

theorem source_graphReady :
    SingleWedgeSourceRegression.source.molecule.LocalizedCIPGraphReady :=
  (SemanticMolecule.localizedCIPGraphReady?_eq_true_iff _).mp (by decide +kernel)

/-- The structurally certified and graph-ready authority input. -/
def certifiedInputCF : CertifiedLocalizedCIPInput where
  certified :=
    { input := SingleWedgeSourceRegression.source
      structurallyWellFormed := source_structurallyWellFormed }
  graphReady := source_graphReady

/-- The empty supplied electronic family is ready: the structural clause holds, the empty record
list is well formed, and the directed-double-endpoint clause is vacuous because the actual source
has no ordinary double bond. -/
theorem suppliedEmptyReady :
    SingleWedgeSourceRegression.source.MainGroupLewisGeneralHybridCertificationReady [] := by
  refine ⟨source_structurallyWellFormed, ?_, ?_⟩
  · exact
      ⟨by simp, by simp⟩
  · intro endpoint partner directed
    exact absurd directed (noDirectedEndpoint_of_noOrdinaryDoubleBond _
      SingleWedgeProductionKeyReadinessRegression.cfclbri_no_ordinary_double_bond endpoint partner)

/-- The existing concrete auxiliary occurrence semantics at carrier zero / rule two. -/
noncomputable def closedSemantics :=
  SingleWedgeSourceRegression.source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics 0 2

/-- The inhabited closed development request. No spatial channel is synthesized. -/
noncomputable def closedRequest : SourceNativeDevelopmentRequest where
  normalized := certifiedCF
  input := certifiedInputCF
  supplied := []
  electronicReady := suppliedEmptyReady
  carrierFuel := 0
  semantics := closedSemantics
  ruleFuel := 2

/-- Exact constitutional agreement: the normalized parser product converts to precisely the
request's semantic molecule. This uses semantic conversion, never parser-diagram equality. -/
theorem closed_constitutionalAgreement :
    closedRequest.ConstitutionalAgreement := by
  show (normalizeRawMolecule rawCF).parsed.toSemanticMolecule? =
    some closedRequest.source.molecule
  decide +kernel

/-! ### Positional uniqueness of the only perceived tetrahedral centre -/

private theorem cfclbri_neighbor_set_one :
    SingleWedgeSourceRegression.source.aromaticCanonicalNeighborFinset ⟨1, by decide⟩ =
      {⟨0, by decide⟩} := by
  ext neighbor
  rw [mem_aromaticCanonicalNeighborFinset_iff]
  fin_cases neighbor <;> unfold AromaticCanonicalAdjacent <;> decide +kernel

private theorem cfclbri_neighbor_set_two :
    SingleWedgeSourceRegression.source.aromaticCanonicalNeighborFinset ⟨2, by decide⟩ =
      {⟨0, by decide⟩} := by
  ext neighbor
  rw [mem_aromaticCanonicalNeighborFinset_iff]
  fin_cases neighbor <;> unfold AromaticCanonicalAdjacent <;> decide +kernel

private theorem cfclbri_neighbor_set_three :
    SingleWedgeSourceRegression.source.aromaticCanonicalNeighborFinset ⟨3, by decide⟩ =
      {⟨0, by decide⟩} := by
  ext neighbor
  rw [mem_aromaticCanonicalNeighborFinset_iff]
  fin_cases neighbor <;> unfold AromaticCanonicalAdjacent <;> decide +kernel

private theorem cfclbri_neighbor_set_four :
    SingleWedgeSourceRegression.source.aromaticCanonicalNeighborFinset ⟨4, by decide⟩ =
      {⟨0, by decide⟩} := by
  ext neighbor
  rw [mem_aromaticCanonicalNeighborFinset_iff]
  fin_cases neighbor <;> unfold AromaticCanonicalAdjacent <;> decide +kernel

/-- Only the carbon has four canonical neighbours, so every perceived tetrahedral centre is the
actual carbon centre. -/
theorem cfclbri_center_val_zero
    (center : SingleWedgeSourceRegression.source.AromaticCanonicalTetrahedralCenter) :
    center.1.val = 0 := by
  rcases center with ⟨⟨value, bound⟩, member⟩
  have card := ((SingleWedgeSourceRegression.source.mem_aromaticCanonicalTetrahedralCenterSet_iff
    (⟨value, bound⟩ : SingleWedgeSourceRegression.source.AromaticCanonicalAtom)).mp member).2
  have valueBound : value < 5 := bound
  interval_cases value
  · rfl
  · rw [show (⟨1, bound⟩ : SingleWedgeSourceRegression.source.AromaticCanonicalAtom) =
        ⟨1, by decide⟩ from Fin.ext rfl, cfclbri_neighbor_set_one] at card
    simp at card
  · rw [show (⟨2, bound⟩ : SingleWedgeSourceRegression.source.AromaticCanonicalAtom) =
        ⟨2, by decide⟩ from Fin.ext rfl, cfclbri_neighbor_set_two] at card
    simp at card
  · rw [show (⟨3, bound⟩ : SingleWedgeSourceRegression.source.AromaticCanonicalAtom) =
        ⟨3, by decide⟩ from Fin.ext rfl, cfclbri_neighbor_set_three] at card
    simp at card
  · rw [show (⟨4, bound⟩ : SingleWedgeSourceRegression.source.AromaticCanonicalAtom) =
        ⟨4, by decide⟩ from Fin.ext rfl, cfclbri_neighbor_set_four] at card
    simp at card

theorem cfclbri_center_unique
    (center : SingleWedgeSourceRegression.source.AromaticCanonicalTetrahedralCenter) :
    center = SingleWedgeOccurrenceAlignmentRegression.cfclbriProductionCenter := by
  apply Subtype.ext
  exact Fin.ext ((cfclbri_center_val_zero center).trans
    (cfclbri_center_val_zero
      SingleWedgeOccurrenceAlignmentRegression.cfclbriProductionCenter).symm)





theorem tetrahedralAuditIssues_eq_nil_of_all_assigned (source : AuthoritativeChemicalInput)
    {carrierFuel : Nat} (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat)
    (assigned : ∀ center : source.AromaticCanonicalTetrahedralCenter,
      ∃ label, scheduledDrawingSpatialStatus source semantics ruleFuel center = .assigned label) :
    tetrahedralAuditIssues source semantics ruleFuel = [] := by
  unfold tetrahedralAuditIssues
  rw [List.filterMap_eq_nil_iff]
  intro row present
  have status := (mem_scheduledTetrahedralReport_iff source semantics ruleFuel row).mp present
  obtain ⟨label, assignedStatus⟩ := assigned row.center
  rw [status, assignedStatus]

theorem closed_tetrahedralIssues_nil :
    tetrahedralAuditIssues closedRequest.source closedRequest.semantics closedRequest.ruleFuel = [] := by
  refine tetrahedralAuditIssues_eq_nil_of_all_assigned _ _ _ ?_
  intro center
  have same : center = SingleWedgeOccurrenceAlignmentRegression.cfclbriProductionCenter :=
    cfclbri_center_unique center
  subst center
  exact ⟨_, cfclbri_solid_scheduled_S closedSemantics⟩

/-- The plain/solid CFClBrI diagram raises no annotation issue: all records are absolute, the three
plain bonds and the wedge are backed by actual `covalent 1` interactions, the wedge source centre is
locally recognized, and there is no atom configuration. -/
theorem closed_diagramIssues_nil : diagramAuditIssues closedRequest.source = [] := by
  decide +kernel


theorem closed_auditIssues_nil : closedRequest.auditIssues = [] := by
  show diagramAuditIssues closedRequest.source ++
    tetrahedralAuditIssues closedRequest.source closedRequest.semantics closedRequest.ruleFuel = []
  rw [List.append_eq_nil_iff]
  exact ⟨closed_diagramIssues_nil, closed_tetrahedralIssues_nil⟩

/-- Production succeeds on the inhabited closed request. -/
theorem closed_produce_eq_some :
    closedRequest.produce = some closedRequest.report :=
  (SourceNativeDevelopmentRequest.produce_eq_some_iff closedRequest closedRequest.report).mpr
    ⟨closed_constitutionalAgreement, closed_auditIssues_nil, rfl⟩

/-- **Solid `R` row, historical API key.**  The old suffix says `S`; under the corrected
calibration the solid CFClBrI drawing emits `R`.  Use `closed_report_contains_solid_R` for new
code. -/
theorem closed_report_contains_solid_S :
    (ScheduledHybridRepresentedResult.tetrahedral
      (⟨SingleWedgeOccurrenceAlignmentRegression.cfclbriProductionCenter,
        .assigned (.chiral RS.R)⟩ :
        TetrahedralStatusRow SingleWedgeSourceRegression.source)) ∈ closedRequest.report := by
  show ScheduledHybridRepresentedResult.tetrahedral
      (⟨SingleWedgeOccurrenceAlignmentRegression.cfclbriProductionCenter,
        .assigned (.chiral RS.R)⟩ :
        TetrahedralStatusRow SingleWedgeSourceRegression.source) ∈
    analyzeScheduledHybridRepresentedOfReady SingleWedgeSourceRegression.source []
      suppliedEmptyReady closedSemantics 2
  apply (mem_analyzeScheduledHybridRepresentedOfReady_iff _ [] suppliedEmptyReady closedSemantics 2 _).mpr
  exact (cfclbri_solid_scheduled_S closedSemantics).symm

/-- Accurate-name alias for the committed solid `R` row. -/
theorem closed_report_contains_solid_R :
    (ScheduledHybridRepresentedResult.tetrahedral
      (⟨SingleWedgeOccurrenceAlignmentRegression.cfclbriProductionCenter,
        .assigned (.chiral RS.R)⟩ :
        TetrahedralStatusRow SingleWedgeSourceRegression.source)) ∈ closedRequest.report :=
  closed_report_contains_solid_S

end ClosedSource

/-! ## 5. Global-rejection counterexamples -/

namespace Counterexamples

open SingleWedgeSourceRegression

/-- The CFClBrI diagram with one valid-index but unsupported atom configuration. -/
def annotatedDiagram : DiagramConfiguration :=
  { SingleWedgeSourceRegression.diagram with
    atomConfigurations := [⟨0, .clockwise, .absolute⟩] }

def annotatedSource : AuthoritativeChemicalInput :=
  { SingleWedgeSourceRegression.source with diagram? := some annotatedDiagram }

/-- The same source with a remote nonplain record the local wedge recognition never inspects. -/
def remoteUnsupportedDiagram : DiagramConfiguration :=
  { SingleWedgeSourceRegression.diagram with
    bonds := SingleWedgeSourceRegression.diagram.bonds ++
      [⟨1, 2, .wavy, .absolute⟩] }

def remoteUnsupportedSource : AuthoritativeChemicalInput :=
  { SingleWedgeSourceRegression.source with diagram? := some remoteUnsupportedDiagram }

/-- A non-plain, non-wedge style always raises `unsupportedBondStyle`. -/
theorem unsupportedBondStyle_mem_of_unsupported (source : AuthoritativeChemicalInput)
    (bond : DiagramBond) (style : bond.style = .wavy ∨ bond.style = .bold ∨
      bond.style = .directionalUp ∨ bond.style = .directionalDown) :
    AnnotationIssue.unsupportedBondStyle bond ∈ bondAuditIssues source bond := by
  unfold bondAuditIssues
  rcases style with wavy | bold | up | down
  · rw [wavy]; simp
  · rw [bold]; simp
  · rw [up]; simp
  · rw [down]; simp

/-- Every listed atom configuration raises `unsupportedAtomConfiguration`. -/
theorem unsupportedAtomConfiguration_mem (source : AuthoritativeChemicalInput)
    (diagram : DiagramConfiguration) (observed : source.diagram? = some diagram)
    (configuration : DiagramAtomConfiguration)
    (present : configuration ∈ diagram.atomConfigurations) :
    AnnotationIssue.unsupportedAtomConfiguration configuration.atom configuration.parity
      configuration.scope ∈ diagramAuditIssues source := by
  unfold diagramAuditIssues
  rw [observed]
  exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨configuration, present, rfl⟩))


theorem bondIssue_mem_of_mem_bonds (source : AuthoritativeChemicalInput)
    (diagram : DiagramConfiguration) (observed : source.diagram? = some diagram)
    (bond : DiagramBond) (present : bond ∈ diagram.bonds)
    (issue : AnnotationIssue source) (raised : issue ∈ bondAuditIssues source bond) :
    issue ∈ diagramAuditIssues source := by
  unfold diagramAuditIssues
  rw [observed]
  exact List.mem_append.mpr
    (Or.inr (List.mem_flatMap.mpr ⟨bond, present, raised⟩))

theorem annotated_issue_member :
    AnnotationIssue.unsupportedAtomConfiguration 0 TetrahedralInputParity.clockwise
      DiagramConfigurationScope.absolute ∈ diagramAuditIssues annotatedSource :=
  unsupportedAtomConfiguration_mem annotatedSource annotatedDiagram rfl
    ⟨0, .clockwise, .absolute⟩ (by simp [annotatedDiagram])

theorem remote_issue_member :
    AnnotationIssue.unsupportedBondStyle ⟨1, 2, .wavy, .absolute⟩ ∈
      diagramAuditIssues remoteUnsupportedSource :=
  bondIssue_mem_of_mem_bonds remoteUnsupportedSource remoteUnsupportedDiagram rfl
    ⟨1, 2, .wavy, .absolute⟩ (by simp [remoteUnsupportedDiagram])
    _ (unsupportedBondStyle_mem_of_unsupported remoteUnsupportedSource
      ⟨1, 2, .wavy, .absolute⟩ (Or.inl rfl))

theorem annotated_audit_ne_nil : diagramAuditIssues annotatedSource ≠ [] := by
  intro empty
  have member := annotated_issue_member
  rw [empty] at member
  exact List.not_mem_nil member

theorem remote_audit_ne_nil : diagramAuditIssues remoteUnsupportedSource ≠ [] := by
  intro empty
  have member := remote_issue_member
  rw [empty] at member
  exact List.not_mem_nil member

/-- A request whose source carries an unsupported atom configuration is refused globally, even
though its local wedge centre remains recognizable. -/
theorem annotated_source_refused (request : SourceNativeDevelopmentRequest)
    (same : request.source = annotatedSource) : request.produce = none :=
  SourceNativeDevelopmentRequest.produce_eq_none_of_diagramIssues_ne_nil request fun empty => by
    rw [same] at empty
    exact annotated_audit_ne_nil empty

/-- The same for a remote nonplain record far from the target centre. -/
theorem remote_unsupported_source_refused (request : SourceNativeDevelopmentRequest)
    (same : request.source = remoteUnsupportedSource) : request.produce = none :=
  SourceNativeDevelopmentRequest.produce_eq_none_of_diagramIssues_ne_nil request fun empty => by
    rw [same] at empty
    exact remote_audit_ne_nil empty

theorem annotated_source_structurallyWellFormed : annotatedSource.StructurallyWellFormed :=
  (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff annotatedSource).mp (by decide +kernel)

def annotatedCertifiedInput : CertifiedLocalizedCIPInput where
  certified := { input := annotatedSource, structurallyWellFormed := annotated_source_structurallyWellFormed }
  graphReady := ClosedSource.source_graphReady

theorem annotated_empty_supplied_ready : annotatedSource.MainGroupLewisGeneralHybridCertificationReady [] := by
  refine ⟨annotated_source_structurallyWellFormed, ?_, ?_⟩
  · exact ⟨by simp, by simp⟩
  · intro endpoint partner directed
    exact absurd directed (noDirectedEndpoint_of_noOrdinaryDoubleBond annotatedSource
      SingleWedgeProductionKeyReadinessRegression.cfclbri_no_ordinary_double_bond endpoint partner)

/-- An inhabited, structurally valid development request with the same genuine normalized
constitution but an unsupported valid-index atom configuration. -/
noncomputable def annotatedRequest : SourceNativeDevelopmentRequest where
  normalized := ClosedSource.certifiedCF
  input := annotatedCertifiedInput
  supplied := []
  electronicReady := annotated_empty_supplied_ready
  carrierFuel := 0
  semantics := annotatedSource.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics 0 2
  ruleFuel := 2

theorem annotated_request_constitutionalAgreement : annotatedRequest.ConstitutionalAgreement :=
  ClosedSource.closed_constitutionalAgreement

theorem annotated_request_local_wedge_recognized :
    (extract? annotatedSource ⟨0, by decide⟩).isSome = true := by decide +kernel

theorem annotated_inhabited_request_refused : annotatedRequest.produce = none :=
  annotated_source_refused annotatedRequest rfl

end Counterexamples

end TetraStereo.UniversalProof.SourceNativeRawAnnotationGuardProofs.SourceNativeDevelopmentTransaction
