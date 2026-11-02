import TetraStereo.UniversalProof.ScheduledDrawingSpatialEndToEndProofs.ScheduledDrawingSpatialIntegration
import TetraStereo.OneCenter.AuthoritativeMainGroupLewisGeneralHybridRichRepresentedPipeline

set_option autoImplicit false

namespace TetraStereo.UniversalProof.ScheduledDrawingSpatialEndToEndProofs.ScheduledDrawingSpatialWholeMolecule

open TetraStereo.OneCenter TetraStereo.OneCenter.AuthoritativeChemicalInput
open ScheduledDrawingSpatialIntegration

/-!
Every perceived tetrahedral center has one report row, including unassigned and conflicting
channels. The supplied auxiliary semantics stays explicit. The five-family successor replaces
only the tetrahedral branch with these rows; the four other branches retain their existing
inventory-certified computations and concrete dependency views. Neither scientific approval nor
complete chemical admission follows from an emitted row.
-/

structure TetrahedralStatusRow (source : AuthoritativeChemicalInput) where
  center : source.AromaticCanonicalTetrahedralCenter
  status : ChannelStatus AromaticCanonicalAuxiliaryLabel
  deriving DecidableEq

noncomputable def scheduledTetrahedralReport (source : AuthoritativeChemicalInput)
    {carrierFuel : Nat} (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) : List (TetrahedralStatusRow source) :=
  source.aromaticCanonicalTetrahedralCenters.map fun center =>
    { center, status := scheduledDrawingSpatialStatus source semantics ruleFuel center }

theorem mem_scheduledTetrahedralReport_iff (source : AuthoritativeChemicalInput)
    {carrierFuel : Nat} (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (row : TetrahedralStatusRow source) :
    row ∈ scheduledTetrahedralReport source semantics ruleFuel ↔
      row.status = scheduledDrawingSpatialStatus source semantics ruleFuel row.center := by
  constructor
  · intro present
    rcases List.mem_map.mp present with ⟨center, _retained, same⟩
    subst row
    rfl
  · intro same
    apply List.mem_map.mpr
    refine ⟨row.center,
      (source.mem_aromaticCanonicalTetrahedralCenters_iff row.center).mpr row.center.property, ?_⟩
    cases row with
    | mk center status =>
        change status = scheduledDrawingSpatialStatus source semantics ruleFuel center at same
        subst status
        rfl

theorem scheduledTetrahedralReport_centers (source : AuthoritativeChemicalInput)
    {carrierFuel : Nat} (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) :
    (scheduledTetrahedralReport source semantics ruleFuel).map TetrahedralStatusRow.center =
      source.aromaticCanonicalTetrahedralCenters := by
  unfold scheduledTetrahedralReport
  rw [List.map_map]
  change source.aromaticCanonicalTetrahedralCenters.map id =
    source.aromaticCanonicalTetrahedralCenters
  exact List.map_id source.aromaticCanonicalTetrahedralCenters

theorem scheduledTetrahedralReport_length (source : AuthoritativeChemicalInput)
    {carrierFuel : Nat} (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) :
    (scheduledTetrahedralReport source semantics ruleFuel).length =
      source.aromaticCanonicalTetrahedralCenters.length := by
  simp [scheduledTetrahedralReport]

theorem scheduledTetrahedralReport_nodup (source : AuthoritativeChemicalInput)
    {carrierFuel : Nat} (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) : (scheduledTetrahedralReport source semantics ruleFuel).Nodup := by
  apply source.aromaticCanonicalTetrahedralCenters_nodup.map
  intro left right same
  exact congrArg TetrahedralStatusRow.center same

theorem scheduledTetrahedralReport_every_center (source : AuthoritativeChemicalInput)
    {carrierFuel : Nat} (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter) :
    ∃! row, row ∈ scheduledTetrahedralReport source semantics ruleFuel ∧ row.center = center := by
  refine ⟨⟨center, scheduledDrawingSpatialStatus source semantics ruleFuel center⟩, ?_, ?_⟩
  · exact ⟨(mem_scheduledTetrahedralReport_iff source semantics ruleFuel _).mpr rfl, rfl⟩
  · intro row present
    have status := (mem_scheduledTetrahedralReport_iff source semantics ruleFuel row).mp present.1
    have centerEq := present.2
    cases row with
    | mk rowCenter rowStatus =>
        simp only at centerEq status
        subst rowCenter
        subst rowStatus
        rfl

theorem scheduledTetrahedralReport_center_count_one (source : AuthoritativeChemicalInput)
    {carrierFuel : Nat} (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter) :
    ((scheduledTetrahedralReport source semantics ruleFuel).map TetrahedralStatusRow.center).count
      center = 1 := by
  rw [scheduledTetrahedralReport_centers]
  exact List.count_eq_one_of_mem source.aromaticCanonicalTetrahedralCenters_nodup
    ((source.mem_aromaticCanonicalTetrahedralCenters_iff center).mpr center.property)

def TetrahedralStatusRowMeaning (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel) (ruleFuel : Nat)
    (row : TetrahedralStatusRow source) : Prop :=
  ScheduledDrawingSpatialMeaning source semantics ruleFuel row.center ∧
    ClassifiesStatus (scheduledDrawingOutputs source semantics ruleFuel row.center) row.status

theorem scheduledTetrahedralReport_member_sound (source : AuthoritativeChemicalInput)
    {carrierFuel : Nat} (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (row : TetrahedralStatusRow source)
    (present : row ∈ scheduledTetrahedralReport source semantics ruleFuel) :
    TetrahedralStatusRowMeaning source semantics ruleFuel row := by
  have status := (mem_scheduledTetrahedralReport_iff source semantics ruleFuel row).mp present
  refine ⟨scheduledDrawingSpatialMeaning_holds source semantics ruleFuel row.center, ?_⟩
  rw [status]
  exact scheduledDrawingSpatialStatus_classifies source semantics ruleFuel row.center

/-- All five actual result families; the tetrahedral payload retains every channel status. -/
inductive ScheduledHybridRepresentedResult (source : AuthoritativeChemicalInput) where
  | tetrahedral (row : TetrahedralStatusRow source)
  | ordinaryDoubleBond (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment)
  | oddOpenCumulene (assignment : source.AromaticCanonicalOddOpenCumuleneSpatialAssignment)
  | evenOpenCumulene (assignment : source.AromaticCanonicalEvenOpenCumuleneAxialAssignment)
  | fullyCyclicCumuleneParent (component : source.AromaticCanonicalCyclicCumuleneComponent)
  deriving DecidableEq

noncomputable def analyzeScheduledHybridRepresentedOfReady (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (ready : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    {carrierFuel : Nat} (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) : List (ScheduledHybridRepresentedResult source) :=
  (scheduledTetrahedralReport source semantics ruleFuel).map .tetrahedral ++
    ((source.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady supplied ready).analyzeOrdinaryDoubleBonds
      carrierFuel
        (source.aromaticCanonicalConcreteDependencyViewAt carrierFuel ruleFuel)).map .ordinaryDoubleBond ++
    (source.analyzeAromaticCanonicalOddOpenCumuleneSpatial carrierFuel ruleFuel).map .oddOpenCumulene ++
    (source.analyzeAromaticCanonicalEvenOpenCumuleneAxial carrierFuel ruleFuel).map .evenOpenCumulene ++
    source.aromaticCanonicalCyclicCumuleneComponents.map .fullyCyclicCumuleneParent

def ScheduledHybridRepresentedExecutableMember (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (ready : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    {carrierFuel : Nat} (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) : ScheduledHybridRepresentedResult source → Prop
  | .tetrahedral row => row.status = scheduledDrawingSpatialStatus source semantics ruleFuel row.center
  | .ordinaryDoubleBond assignment => source.AromaticCanonicalHybridRichRepresentedExecutableMember
      supplied ready carrierFuel ruleFuel (.ordinaryDoubleBond assignment)
  | .oddOpenCumulene assignment => source.AromaticCanonicalHybridRichRepresentedExecutableMember
      supplied ready carrierFuel ruleFuel (.oddOpenCumulene assignment)
  | .evenOpenCumulene assignment => source.AromaticCanonicalHybridRichRepresentedExecutableMember
      supplied ready carrierFuel ruleFuel (.evenOpenCumulene assignment)
  | .fullyCyclicCumuleneParent component => source.AromaticCanonicalHybridRichRepresentedExecutableMember
      supplied ready carrierFuel ruleFuel (.fullyCyclicCumuleneParent component)

def ScheduledHybridRepresentedMeaning (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (ready : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    {carrierFuel : Nat} (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) : ScheduledHybridRepresentedResult source → Prop
  | .tetrahedral row => TetrahedralStatusRowMeaning source semantics ruleFuel row
  | .ordinaryDoubleBond assignment => source.DeclarativeAromaticCanonicalHybridRichRepresentedMember
      supplied ready carrierFuel ruleFuel (.ordinaryDoubleBond assignment)
  | .oddOpenCumulene assignment => source.DeclarativeAromaticCanonicalHybridRichRepresentedMember
      supplied ready carrierFuel ruleFuel (.oddOpenCumulene assignment)
  | .evenOpenCumulene assignment => source.DeclarativeAromaticCanonicalHybridRichRepresentedMember
      supplied ready carrierFuel ruleFuel (.evenOpenCumulene assignment)
  | .fullyCyclicCumuleneParent component => source.DeclarativeAromaticCanonicalHybridRichRepresentedMember
      supplied ready carrierFuel ruleFuel (.fullyCyclicCumuleneParent component)

theorem mem_analyzeScheduledHybridRepresentedOfReady_iff (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (ready : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    {carrierFuel : Nat} (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (result : ScheduledHybridRepresentedResult source) :
    result ∈ analyzeScheduledHybridRepresentedOfReady source supplied ready semantics ruleFuel ↔
      ScheduledHybridRepresentedExecutableMember source supplied ready semantics ruleFuel result := by
  cases result with
  | tetrahedral row =>
      simp [analyzeScheduledHybridRepresentedOfReady, ScheduledHybridRepresentedExecutableMember,
        mem_scheduledTetrahedralReport_iff]
  | ordinaryDoubleBond assignment =>
      simp [analyzeScheduledHybridRepresentedOfReady, ScheduledHybridRepresentedExecutableMember,
        AromaticCanonicalHybridRichRepresentedExecutableMember,
        source.mem_certifiedMainGroupLewisGeneralHybridAnalyzeOrdinaryDoubleBonds_iff_canonical
          supplied ready carrierFuel (source.aromaticCanonicalConcreteDependencyViewAt carrierFuel ruleFuel)
          assignment]
  | oddOpenCumulene assignment =>
      simp [analyzeScheduledHybridRepresentedOfReady, ScheduledHybridRepresentedExecutableMember,
        AromaticCanonicalHybridRichRepresentedExecutableMember,
        source.mem_analyzeAromaticCanonicalOddOpenCumuleneSpatial_iff]
  | evenOpenCumulene assignment =>
      simp [analyzeScheduledHybridRepresentedOfReady, ScheduledHybridRepresentedExecutableMember,
        AromaticCanonicalHybridRichRepresentedExecutableMember,
        source.mem_analyzeAromaticCanonicalEvenOpenCumuleneAxial_iff]
  | fullyCyclicCumuleneParent component =>
      simp [analyzeScheduledHybridRepresentedOfReady, ScheduledHybridRepresentedExecutableMember,
        AromaticCanonicalHybridRichRepresentedExecutableMember,
        source.mem_aromaticCanonicalCyclicCumuleneComponents_iff]

theorem analyzeScheduledHybridRepresentedOfReady_member_sound (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (ready : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    {carrierFuel : Nat} (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (result : ScheduledHybridRepresentedResult source)
    (present : result ∈ analyzeScheduledHybridRepresentedOfReady source supplied ready semantics ruleFuel) :
    ScheduledHybridRepresentedMeaning source supplied ready semantics ruleFuel result := by
  have executable := (mem_analyzeScheduledHybridRepresentedOfReady_iff
    source supplied ready semantics ruleFuel result).mp present
  cases result with
  | tetrahedral row =>
      exact scheduledTetrahedralReport_member_sound source semantics ruleFuel row
        ((mem_scheduledTetrahedralReport_iff source semantics ruleFuel row).mpr executable)
  | ordinaryDoubleBond assignment =>
      exact source.analyzeAromaticCanonicalHybridRichRepresentedOfReady_member_sound
        supplied ready carrierFuel ruleFuel (.ordinaryDoubleBond assignment)
        ((source.mem_analyzeAromaticCanonicalHybridRichRepresentedOfReady_iff
          supplied ready carrierFuel ruleFuel _).mpr executable)
  | oddOpenCumulene assignment =>
      exact source.analyzeAromaticCanonicalHybridRichRepresentedOfReady_member_sound
        supplied ready carrierFuel ruleFuel (.oddOpenCumulene assignment)
        ((source.mem_analyzeAromaticCanonicalHybridRichRepresentedOfReady_iff
          supplied ready carrierFuel ruleFuel _).mpr executable)
  | evenOpenCumulene assignment =>
      exact source.analyzeAromaticCanonicalHybridRichRepresentedOfReady_member_sound
        supplied ready carrierFuel ruleFuel (.evenOpenCumulene assignment)
        ((source.mem_analyzeAromaticCanonicalHybridRichRepresentedOfReady_iff
          supplied ready carrierFuel ruleFuel _).mpr executable)
  | fullyCyclicCumuleneParent component =>
      exact source.analyzeAromaticCanonicalHybridRichRepresentedOfReady_member_sound
        supplied ready carrierFuel ruleFuel (.fullyCyclicCumuleneParent component)
        ((source.mem_analyzeAromaticCanonicalHybridRichRepresentedOfReady_iff
          supplied ready carrierFuel ruleFuel _).mpr executable)

end TetraStereo.UniversalProof.ScheduledDrawingSpatialEndToEndProofs.ScheduledDrawingSpatialWholeMolecule
