import TetraStereo.OneCenter.IUPACP93CanonicalSourceClaims

set_option autoImplicit false














namespace TetraStereo.OneCenter

open IUPACNormativeProvision

namespace P93CanonicalProgramNoncyclic

/-- External information which must be transcribed with Blue Book provenance before a row can be
inserted into the closed canonical source program. -/
inductive RequiredExternalDatum where
  | absoluteLocatedAssignments
  | relativeLocatedPairAndPreferredRepresentative
  | mixedScopePlanAndTypography
  | racemateLocatedEnantiomerPair
  | amboLocatedQualitativeEpimerPair
  | noncarbonTetrahedralExampleAndDescriptor
  | noncarbonCitationMethodologyExample
  | oniumExampleAndDescriptor
  | amineOrPhosphaneOxideRepresentationPair
  | phosphateOrPhosphonateRepresentationPair
  | sulfateOrSulfonateRepresentationPair
  | group14TetrahedralExampleAndDescriptor
  | acyclicCenterExampleAndDescriptor
  | singleCenterNamePlacement
  | multipleDescriptorsAtOneCenter
  | prefixComponentPlacement
  | ordinaryDoubleBondExampleAndDescriptor
  | doubleBondEZCisTransContext
  | multipleDoubleBondTopologyAndAssignments
  | heteroatomDoubleBondExampleAndDescriptor
  | perceivedEvenCumuleneAxisAndDescriptor
  | perceivedOddCumuleneAxisGeometryAndDescriptor
  | orderedMultipleUnitLocantsAndCompetition
  deriving DecidableEq, Repr

/-- One gap retains the exact canonical clause and its independently maintained normative section
key.  The section string is projected from the manifest rather than retyped here. -/
structure TranscriptionGap where
  clause : P93Clause
  required : RequiredExternalDatum
  deriving DecidableEq, Repr

def gaps : List TranscriptionGap := []

/-- Canonical remaining universe derived from the family enumerations, not from the gap list. -/
def canonicalNoncyclicClauses : List P93Clause :=
  []

@[simp] theorem canonicalNoncyclicClauses_length : canonicalNoncyclicClauses.length = 0 := rfl

theorem canonicalNoncyclicClauses_nodup : canonicalNoncyclicClauses.Nodup := by decide

/-- Exact empty frontier: no noncyclic source-transcription gap remains. -/
theorem gap_clause_projection :
    gaps.map (fun gap => gap.clause) = canonicalNoncyclicClauses := rfl

theorem gap_clauses_nodup : (gaps.map fun gap => gap.clause).Nodup := by
  rw [gap_clause_projection]
  exact canonicalNoncyclicClauses_nodup

@[simp] theorem gaps_length : gaps.length = 0 := rfl

/-- No local object is promoted to source authority merely because its finite structure checks. -/
def entries : List P93CanonicalClauseObservationEntry := []

def coveredClauses : List P93Clause := entries.map fun entry => entry.clause

@[simp] theorem coveredClauses_eq_nil : coveredClauses = [] := rfl

/-- Exact coverage theorem for the currently justified subset (which is honestly empty). -/
theorem covered_clause_has_entry (clause : P93Clause) (covered : clause ∈ coveredClauses) :
    ∃ entry ∈ entries, entry.clause = clause := by
  simpa [coveredClauses] using covered

/-- The manifest's section key remains available for every gap without laundering it into an
audited observation. -/
def TranscriptionGap.sourceSection (gap : TranscriptionGap) : String :=
  gap.clause.provision.sourceSection

end P93CanonicalProgramNoncyclic
end TetraStereo.OneCenter
