import TetraStereo.OneCenter.AuthoritativeSemanticOrdinaryDoubleBondSpatialAssignment

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Whole-molecule automatic ordinary-double-bond analysis

Only the canonical individual-bond route is traversed.  Odd/even open cumulenes, cyclic
cumulenes, and branched per-bond authority candidates remain in their disjoint owner lists and
cannot be double-assigned here.
-/

/-- Analyze every canonical individual ordinary-double-bond carrier. -/
noncomputable def analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom)) :
    List source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment :=
  source.aromaticCanonicalIndividualDoubleBondCarriers.filterMap fun bond =>
    source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?
      carrierFuel bond (viewAt bond.left) (viewAt bond.right)

/-- Exact computational membership of the whole-family analyzer. -/
theorem mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial_iff
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom))
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) :
    assignment ∈ source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial
        carrierFuel viewAt ↔
      ∃ bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers,
        source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?
          carrierFuel bond (viewAt bond.left) (viewAt bond.right) = some assignment := by
  rw [analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial, List.mem_filterMap]

/-- Independent whole-family positive judgment. -/
def DeclarativeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialMember
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom))
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) : Prop :=
  ∃ bond,
    source.DeclarativeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment
      carrierFuel bond (viewAt bond.left) (viewAt bond.right) assignment

/-- Every whole-family emitted result satisfies the independent endpoint, Rule-5, geometry, and
descriptor judgment for its unique canonical carrier. -/
theorem analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial_member_sound
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom))
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment)
    (present : assignment ∈
      source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial carrierFuel viewAt) :
    source.DeclarativeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialMember
      carrierFuel viewAt assignment := by
  obtain ⟨bond, owner, emitted⟩ :=
    (source.mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial_iff
      carrierFuel viewAt assignment).mp present
  exact ⟨bond,
    source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?_sound
      carrierFuel bond (viewAt bond.left) (viewAt bond.right) assignment emitted⟩

/-- A chemically ready canonical ordinary bond appears in the whole-family output. -/
theorem exists_mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial_of_dependencies
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom))
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (evidence :
      source.AromaticCanonicalOrdinaryDoubleBondAutomaticDependencyEvidence
        carrierFuel bond (viewAt bond.left) (viewAt bond.right)) :
    ∃ assignment,
      assignment ∈ source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial
        carrierFuel viewAt ∧ assignment.bond = bond := by
  obtain ⟨assignment, emitted⟩ :=
    source.exists_aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment_of_dependencies
      carrierFuel bond (viewAt bond.left) (viewAt bond.right) evidence
  refine ⟨assignment, ?_, ?_⟩
  · exact (source.mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial_iff
      carrierFuel viewAt assignment).mpr ⟨bond, evidence.owner, emitted⟩
  · exact (source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?_sound
      carrierFuel bond (viewAt bond.left) (viewAt bond.right) assignment emitted).1

/-- The whole-family analyzer emits at most one assignment for each canonical physical bond and
therefore has no duplicate assignments. -/
theorem analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial_nodup
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom)) :
    (source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial
      carrierFuel viewAt).Nodup := by
  unfold analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial
  unfold aromaticCanonicalIndividualDoubleBondCarriers
  apply (source.aromaticCanonicalOrdinaryDoubleBondRouteCarriers_nodup
    BlueBookP93.Acyclic.DoubleBondAnalysisRoute.individualDoubleBond).filterMap
  intro leftBond rightBond assignment leftEmitted rightEmitted
  have leftDerived :=
    source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?_sound
      carrierFuel leftBond (viewAt leftBond.left) (viewAt leftBond.right)
      assignment (by simpa using leftEmitted)
  have rightDerived :=
    source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?_sound
      carrierFuel rightBond (viewAt rightBond.left) (viewAt rightBond.right)
      assignment (by simpa using rightEmitted)
  exact leftDerived.1.symm.trans rightDerived.1

/-- Every chemically ready canonical physical bond is represented by exactly one assignment in
the whole-family output.  This strengthens mere list `Nodup`: uniqueness is by retained physical
bond identity and by the fact that the per-bond analyzer is an `Option`. -/
theorem existsUnique_mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial_of_dependencies
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom))
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (evidence :
      source.AromaticCanonicalOrdinaryDoubleBondAutomaticDependencyEvidence
        carrierFuel bond (viewAt bond.left) (viewAt bond.right)) :
    ∃! assignment,
      assignment ∈ source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial
        carrierFuel viewAt ∧ assignment.bond = bond := by
  obtain ⟨assignment, assignmentPresent, assignmentBond⟩ :=
    source.exists_mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial_of_dependencies
      carrierFuel viewAt bond evidence
  refine ⟨assignment, ⟨assignmentPresent, assignmentBond⟩, ?_⟩
  intro other ⟨otherPresent, otherBond⟩
  obtain ⟨assignmentOrigin, assignmentOriginOwner, assignmentEmitted⟩ :=
    (source.mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial_iff
      carrierFuel viewAt assignment).mp assignmentPresent
  obtain ⟨otherOrigin, otherOriginOwner, otherEmitted⟩ :=
    (source.mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial_iff
      carrierFuel viewAt other).mp otherPresent
  have assignmentDerived :=
    source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?_sound
      carrierFuel assignmentOrigin (viewAt assignmentOrigin.left)
      (viewAt assignmentOrigin.right) assignment assignmentEmitted
  have otherDerived :=
    source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?_sound
      carrierFuel otherOrigin (viewAt otherOrigin.left) (viewAt otherOrigin.right)
      other otherEmitted
  have assignmentOriginEq : assignmentOrigin = bond :=
    assignmentDerived.1.symm.trans assignmentBond
  have otherOriginEq : otherOrigin = bond := otherDerived.1.symm.trans otherBond
  subst assignmentOrigin
  subst otherOrigin
  rw [assignmentEmitted] at otherEmitted
  exact Option.some.inj otherEmitted.symm

/-- Molecule-wide form: if every carrier in the canonical individual-bond route is chemically
ready, then each of those carriers occurs exactly once in the analyzer output. -/
theorem every_ready_aromaticCanonicalOrdinaryDoubleBond_occurs_exactly_once
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom))
    (ready : ∀ bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers,
      source.AromaticCanonicalOrdinaryDoubleBondAutomaticDependencyEvidence
        carrierFuel bond (viewAt bond.left) (viewAt bond.right)) :
    ∀ bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers,
      ∃! assignment,
        assignment ∈ source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial
          carrierFuel viewAt ∧ assignment.bond = bond := by
  intro bond owner
  exact source.existsUnique_mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial_of_dependencies
    carrierFuel viewAt bond (ready bond owner)

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
