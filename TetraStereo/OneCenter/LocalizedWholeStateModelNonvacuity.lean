import TetraStereo.OneCenter.LocalizedWholeStateUniversalModel
import TetraStereo.OneCenter.LocalizedNoDoubleRule3ChemicalCompleteness
import TetraStereo.OneCenter.LocalizedExtendedFuelMonotonicity
import TetraStereo.OneCenter.LocalizedUniversalDescriptorEvaluation
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

















































































namespace TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity

open TetraStereo.OneCenter
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-! ## General endpoint: no localized double bond gives the whole geometry domain -/

/-- Without a localized order-two source record the executable odd-route inspector refuses at every
carrier occurrence.  This applies the existing safe edge certificate through the existing structural
soundness theorem, not an assumed route failure. -/
theorem localizedRule3OddRouteCertificate?_eq_none_of_noDoubleRecords
    (input : CertifiedLocalizedCIPInput)
    (noDouble : input.certified.input.molecule.NoLocalizedDoubleBondRecords)
    {carrierFuel : Nat} (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    input.localizedRule3OddRouteCertificate? occurrence = none :=
  input.localizedRule3OddRouteCertificate?_eq_none_of_not_edge occurrence
    (input.localizedOccurrence_not_rule3DoubleBondEdge_of_noDoubleRecords noDouble occurrence)

/-- Without a localized order-two source record the executable ordinary-route inspector refuses at
every carrier occurrence. -/
theorem localizedRule3OrdinaryRouteCertificate?_eq_none_of_noDoubleRecords
    (input : CertifiedLocalizedCIPInput)
    (noDouble : input.certified.input.molecule.NoLocalizedDoubleBondRecords)
    {carrierFuel : Nat} (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    input.localizedRule3OrdinaryRouteCertificate? occurrence = none :=
  input.localizedRule3OrdinaryRouteCertificate?_eq_none_of_not_edge occurrence
    (input.localizedOccurrence_not_rule3DoubleBondEdge_of_noDoubleRecords noDouble occurrence)

/-- **The independent all-occurrence conditional geometry domain is trivial without localized double
bonds.**  Both executable route certificates are absent at every occurrence, so every conditional
implication of the domain is vacuous.  No geometry, readiness, base or descriptor success is
assumed. -/
theorem localizedRule3ExtendedNodeConditionalGeometryDomainAll_of_noDoubleRecords
    (input : CertifiedLocalizedCIPInput)
    (noDouble : input.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (carrierFuel : Nat) :
    input.LocalizedRule3ExtendedNodeConditionalGeometryDomainAll carrierFuel := by
  intro occurrence
  have oddNone :=
    localizedRule3OddRouteCertificate?_eq_none_of_noDoubleRecords input noDouble occurrence
  have ordinaryNone :=
    localizedRule3OrdinaryRouteCertificate?_eq_none_of_noDoubleRecords input noDouble occurrence
  simp only [LocalizedRule3ExtendedNodeConditionalGeometryDomain, oddNone, ordinaryNone]








/-- **General geometry domain.**  Any runtime input without a localized double-bond source record
satisfies the independent all-occurrence conditional geometry domain at its own carrier fuel. -/
theorem geometryDomainAll_of_noDoubleRecords
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords) :
    input.certified.LocalizedRule3ExtendedNodeConditionalGeometryDomainAll
      (LocalizedUniversalReference.carrierFuel input) :=
  localizedRule3ExtendedNodeConditionalGeometryDomainAll_of_noDoubleRecords
    input.certified noDouble (LocalizedUniversalReference.carrierFuel input)

/-- **General actual reference fixed point.**  The generated reference state is an actual
whole-state fixed point for every input with no localized order-two source record. -/
theorem wholeStateUniversalModel_referenceState_of_noDoubleRecords
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords) :
    LocalizedUniversalReference.WholeStateUniversalModel input
      (LocalizedUniversalReference.referenceState input) :=
  LocalizedUniversalReference.wholeStateUniversalModel_referenceState input
    (geometryDomainAll_of_noDoubleRecords input noDouble)

/-- **General uniqueness.**  For every input with no localized order-two source record, every
actual whole-state fixed point is the generated reference state. -/
theorem wholeStateUniversalModel_eq_referenceState_of_noDoubleRecords
    (input : LocalizedUniversalReference.Input)
    (state : input.certified.LocalizedAuxiliaryState
      (LocalizedUniversalReference.carrierFuel input))
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (model : LocalizedUniversalReference.WholeStateUniversalModel input state) :
    state = LocalizedUniversalReference.referenceState input :=
  LocalizedUniversalReference.wholeStateUniversalModel_eq_referenceState input state
    (geometryDomainAll_of_noDoubleRecords input noDouble) model

/-- **General existence and uniqueness of the actual whole-state model on the
no-localized-double-bond class.**
This is the public endpoint of the module: for any runtime input with no localized order-two source
record, the actual full-state universal model exists and its witness is unique. -/
theorem existsUnique_wholeStateUniversalModel_of_noDoubleRecords
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords) :
    ∃! state : input.certified.LocalizedAuxiliaryState
        (LocalizedUniversalReference.carrierFuel input),
      LocalizedUniversalReference.WholeStateUniversalModel input state :=
  LocalizedUniversalReference.existsUnique_wholeStateUniversalModel input
    (geometryDomainAll_of_noDoubleRecords input noDouble)

/-! ## The concrete five-atom halomethane fixture -/

/-- Checked periodic-table element spelling. -/
def periodicElement (atomicNumber : Nat) (positive : 0 < atomicNumber)
    (bounded : atomicNumber ≤ 118) : PeriodicElement :=
  { atomicNumber := atomicNumber, positive := positive, atMost118 := bounded }

def carbon : PeriodicElement := periodicElement 6 (by decide) (by decide)
def fluorine : PeriodicElement := periodicElement 9 (by decide) (by decide)
def chlorine : PeriodicElement := periodicElement 17 (by decide) (by decide)
def bromine : PeriodicElement := periodicElement 35 (by decide) (by decide)
def iodine : PeriodicElement := periodicElement 53 (by decide) (by decide)

/-- A neutral, unlabelled atom of one element. -/
def atom (element : PeriodicElement) : SemanticAtom := { element := element }

/-- One ordinary single bond. -/
def singleBond (left right : Nat) : SemanticInteraction :=
  { participants := [left, right], kind := .covalent 1 }

/-- Five-atom bromochlorofluoroiodomethane (`C, F, Cl, Br, I`, atom indices `0..4`) with four
ordinary single bonds and the exact rational tetrahedral coordinates of the established probe
fixture.  Atom `0` is the unique four-neighbour tetrahedral candidate. -/
def halomethaneSource : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := [carbon, fluorine, chlorine, bromine, iodine].map atom
        interactions := [singleBond 0 1, singleBond 0 2, singleBond 0 3, singleBond 0 4] }
    spatial? := some { positions :=
      [{ x := 0, y := 0, z := 0 }, { x := -1, y := -1, z := 1 },
       { x := -1, y := 1, z := -1 }, { x := 1, y := -1, z := -1 },
       { x := 1, y := 1, z := 1 }] } }

/-- The fixture passes the structural admission gate. -/
theorem halomethaneSource_structurallyWellFormed :
    halomethaneSource.structurallyWellFormed? = true := by
  decide +kernel

/-- The fixture passes the localized-graph readiness gate: explicit closed-shell atoms, known
Rule-2 masses, ordinary covalent pairs only, and unique extracted records. -/
theorem halomethaneSource_localizedGraphReady :
    halomethaneSource.molecule.localizedCIPGraphReady? = true := by
  decide +kernel

/-- The executable source-record test finds no order-two localized record. -/
theorem halomethaneSource_noDoubleTest :
    halomethaneSource.molecule.noLocalizedDoubleBondRecords? = true := by
  decide +kernel

/-- The source-record no-double-bond restriction holds for the fixture. -/
theorem halomethaneSource_noDoubleRecords :
    halomethaneSource.molecule.NoLocalizedDoubleBondRecords :=
  (halomethaneSource.molecule.noLocalizedDoubleBondRecords?_eq_true_iff).mp
    halomethaneSource_noDoubleTest

/-- The certified authoritative input built from the fixture. -/
def certifiedSource : CertifiedAuthoritativeChemicalInput :=
  { input := halomethaneSource
    structurallyWellFormed :=
      (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff halomethaneSource).mp
        halomethaneSource_structurallyWellFormed }

/-- The certified localized input built from the fixture. -/
def localizedSource : CertifiedLocalizedCIPInput :=
  { certified := certifiedSource
    graphReady :=
      (certifiedSource.input.molecule.localizedCIPGraphReady?_eq_true_iff).mp
        halomethaneSource_localizedGraphReady }

/-- The actual runtime input of the localized universal reference pipeline. -/
def input : LocalizedUniversalReference.Input :=
  { certified := localizedSource }

/-- **Admission.**  The real `admitSource?` pipeline returns exactly the constructed input; this is
a definitional proof through structural and localized-graph certification, with no stored
per-molecule certificate and no assumed readiness. -/
theorem admission : LocalizedUniversalReference.admitSource? halomethaneSource = some input := rfl

/-- The admitted input carries the no-double source-record restriction. -/
theorem input_noDoubleRecords :
    input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords := by
  simpa using halomethaneSource_noDoubleRecords

/-- The carrier fuel of the five-atom fixture is the atom count plus one. -/
theorem carrierFuel_eq :
    LocalizedUniversalReference.carrierFuel input = 6 := rfl

/-- **The independent all-occurrence conditional geometry domain of the admitted fixture, derived
from its source records.**  This is not an assumption. -/
theorem input_geometry :
    input.certified.LocalizedRule3ExtendedNodeConditionalGeometryDomainAll
      (LocalizedUniversalReference.carrierFuel input) :=
  localizedRule3ExtendedNodeConditionalGeometryDomainAll_of_noDoubleRecords
    input.certified input_noDoubleRecords (LocalizedUniversalReference.carrierFuel input)

/-! ## The unique tetrahedral center and its final occurrence -/

/-- Atom `0` (carbon). -/
def centerAtom : input.certified.Atom := ⟨0, by decide⟩

/-- Atom `0` is automatically detected as a four-neighbour tetrahedral candidate. -/
theorem centerAtom_mem : centerAtom ∈ input.certified.tetrahedralCenterSet := by
  decide +kernel

/-- The detected descriptor center. -/
def center : input.certified.TetrahedralCenter := ⟨centerAtom, centerAtom_mem⟩

/-- The final occurrence of the unique center. -/
def target : LocalizedUniversalReference.Occurrence input :=
  input.certified.localizedFinalOccurrenceExecutable
    (LocalizedUniversalReference.carrierFuel input) center

/-- The final center occurrence's node is a real node whose current atom is the detected center. -/
theorem target_realCenterNode :
    input.certified.RealTetrahedralCenterNode target.1.node center := by
  show target.1.node.provenance = OfficialCIPNodeProvenance.realAtom ∧
    target.1.node.current? = some center.1
  exact ⟨rfl, rfl⟩

/-- The final center occurrence stores the detected descriptor center. -/
theorem target_center :
    input.certified.localizedOccurrenceDescriptorCenter? target = some center :=
  (input.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff target center).mpr
    target_realCenterNode

/-! ## Reference-state refusal away from descriptor centers -/

/-- **Exact refusal of the generated reference state at an occurrence without a descriptor
center.**  The operational fixed-point equation reads the actual full descriptor at the state's own
dependency view; an absent centre refuses that descriptor outright, independently of the view. -/
theorem referenceState_eq_none_of_center_none
    (input : LocalizedUniversalReference.Input)
    (target : LocalizedUniversalReference.Occurrence input)
    (missing : input.certified.localizedOccurrenceDescriptorCenter? target = none) :
    LocalizedUniversalReference.referenceState input target = none := by
  have equation := LocalizedUniversalReference.reference_equation input target
  rw [LocalizedUniversalReference.evaluator_eq_universalDescriptor_apply input
    (LocalizedUniversalReference.carrierFuel input) target
    (input.certified.localizedDependencyView
      (LocalizedUniversalReference.referenceState input) target)] at equation
  rw [← equation]
  exact input.certified.universalDescriptor?_eq_none_of_center_none target _ missing

/-- The empty dependency view at the final center occurrence. -/
def emptyView : input.certified.LocalizedDependencyView target := fun _ _ => none

/-! ## Eliminating the non-reducible `Finset.sort`

`Finset.sort` is `Multiset.sort`, whose body is the well-founded `List.mergeSort` that the kernel
does not unfold.  Every executable occurrence enumeration in this pipeline ends in
`executableOfficialNeighborCopies`, hence in `Finset.sort`.  As documented in
`LocalizedRetainedDemandCycleKernel` and `OxidoRootExpansionDiagnostic`, rewriting each sort by an
explicit sorted list (proved through the sort-free `List.toFinset_sort`) lets the kernel evaluate
the remaining structural computation. -/

/-- If `l` is a nodup, sorted enumeration of the neighbours of `a`, then `Finset.sort` is `l`. -/
theorem sort_of_toFinset_eq (a : input.certified.Atom) (l : List input.certified.Atom)
    (hset : l.toFinset = input.certified.moleculeGraph.neighborFinset a)
    (hnd : l.Nodup) (hpw : l.Pairwise (· ≤ ·)) :
    (input.certified.moleculeGraph.neighborFinset a).sort (· ≤ ·) = l := by
  rw [← hset]
  exact (List.toFinset_sort (r := (· ≤ ·)) (l := l) hnd).mpr hpw

/-- The sorted neighbour list of every atom of the fixture.  The right-hand side is a `match` on
the atom value, so it rewrites uniformly at every atom occurrence in an executable term. -/
theorem neighborSort_eq (a : input.certified.Atom) :
    (input.certified.moleculeGraph.neighborFinset a).sort (· ≤ ·) =
      match a.val with
      | 0 => [⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩]
      | _ => [⟨0, by decide⟩] := by
  fin_cases a
  · exact sort_of_toFinset_eq ⟨0, by decide⟩
      [⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq ⟨1, by decide⟩ [⟨0, by decide⟩]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq ⟨2, by decide⟩ [⟨0, by decide⟩]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq ⟨3, by decide⟩ [⟨0, by decide⟩]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq ⟨4, by decide⟩ [⟨0, by decide⟩]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)

/-- Eta-expanded form of the per-atom enumerator, so that the simplifier can see it beneath the
partial application used by `List.flatMap`. -/
theorem localizedOccurrencesAtAtom_partial (fuel : Nat) :
    (input.certified.localizedOccurrencesAtAtom fuel) =
      fun atom => input.certified.localizedOccurrencesAtAtom fuel atom :=
  rfl

/-! ## The dependency view at the final center

The concrete evaluation of the occurrence carrier that would show the reference state's dependency
view at the target to be empty is not part of the sealed core.  The carrier enumeration passes
through `Finset.sort`, whose well-founded `mergeSort` body the kernel does not unfold; the
sort-elimination lemmas above reduce it to a finite case check, but the combined `simp`-then-
`decide` reduction over the mutually recursive Rule-3/45 frame builders overflowed the elaborator's
stack (`exit 134`) in this environment, so the label-computation chain is preserved separately as
`LocalizedWholeStateModelNonvacuity.draft.lean` and is not claimed by this module. -/

/-! ## The unique actual whole-state fixed point -/

/-- The generated reference state is an actual model of the full-state operator. -/
theorem referenceState_wholeStateUniversalModel :
    LocalizedUniversalReference.WholeStateUniversalModel input
      (LocalizedUniversalReference.referenceState input) :=
  LocalizedUniversalReference.wholeStateUniversalModel_referenceState input input_geometry





theorem existsUnique_wholeStateUniversalModel :
    ∃! state : input.certified.LocalizedAuxiliaryState
        (LocalizedUniversalReference.carrierFuel input),
      LocalizedUniversalReference.WholeStateUniversalModel input state :=
  LocalizedUniversalReference.existsUnique_wholeStateUniversalModel input input_geometry

end TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity

-- Kernel-authority certificates for the exported surface.

assert_kernel_only TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity.localizedRule3OddRouteCertificate?_eq_none_of_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity.localizedRule3OrdinaryRouteCertificate?_eq_none_of_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity.localizedRule3ExtendedNodeConditionalGeometryDomainAll_of_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity.geometryDomainAll_of_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity.wholeStateUniversalModel_referenceState_of_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity.wholeStateUniversalModel_eq_referenceState_of_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity.existsUnique_wholeStateUniversalModel_of_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity.periodicElement
assert_kernel_only TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity.carbon
assert_kernel_only TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity.fluorine
assert_kernel_only TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity.chlorine
assert_kernel_only TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity.bromine
assert_kernel_only TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity.iodine
assert_kernel_only TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity.atom
assert_kernel_only TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity.singleBond
assert_kernel_only TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity.halomethaneSource
assert_kernel_only TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity.halomethaneSource_structurallyWellFormed
assert_kernel_only TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity.halomethaneSource_localizedGraphReady
assert_kernel_only TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity.halomethaneSource_noDoubleTest
assert_kernel_only TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity.halomethaneSource_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity.certifiedSource
assert_kernel_only TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity.localizedSource
assert_kernel_only TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity.input
assert_kernel_only TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity.admission
assert_kernel_only TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity.input_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity.carrierFuel_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity.input_geometry
assert_kernel_only TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity.centerAtom
assert_kernel_only TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity.centerAtom_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity.center
assert_kernel_only TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity.target
assert_kernel_only TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity.target_realCenterNode
assert_kernel_only TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity.target_center
assert_kernel_only TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity.referenceState_eq_none_of_center_none
assert_kernel_only TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity.emptyView
assert_kernel_only TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity.sort_of_toFinset_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity.neighborSort_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity.localizedOccurrencesAtAtom_partial
assert_kernel_only TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity.referenceState_wholeStateUniversalModel
assert_kernel_only TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity.existsUnique_wholeStateUniversalModel
