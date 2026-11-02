import TetraStereo.OneCenter.ProductionCIPRule1aGeneralSoundness
import TetraStereo.OneCenter.CIPAuthoritativeMancudeTotality

set_option autoImplicit false






























































namespace TetraStereo
namespace UniversalProof
namespace ProductionMancudeSupportCheckProofs

open TetraStereo.OneCenter

/-- Executable exact membership test: the written occurrence list is one of the maximum-cardinality
edge-occurrence matchings of the component edge list.  Membership is a `Bool` scan over the finite
family using `decide` on equality of number-pair lists — a list-contains test with decidable
equality.  It calls no classical decision procedure, and it deliberately avoids relying on a
`LawfulBEq` instance for `List (ℕ × ℕ)`; the idiom matches
`P94MolecularLonePairEvidence.lean` (`lonePairAt?`). -/
def writtenMancudeEdgeMaximumCheck (edges written : List (ℕ × ℕ)) : Bool :=
  (RawMolecule.maximumMancudeEdgeMatchings
    (RawMolecule.exhaustiveMancudeEdgeMatchings edges)).any
    fun matching => decide (matching = written)

/-- The executable membership test reflects exactly onto the importable, nonrecursive maximum-edge
predicate.  This is the bridge that lets a computed `Bool` discharge the graph-theoretic hypothesis
used by the production totality theorem. -/
theorem writtenMancudeEdgeMaximumCheck_eq_true_iff (edges written : List (ℕ × ℕ)) :
    writtenMancudeEdgeMaximumCheck edges written = true ↔
      RawMolecule.IsMaximumMancudeEdgeMatching written edges := by
  simp only [writtenMancudeEdgeMaximumCheck, List.any_eq_true, decide_eq_true_eq,
    RawMolecule.mem_maximum_exhaustiveMancudeEdgeMatchings_iff]
  constructor
  · rintro ⟨matching, hmaximum, hmatchingEq⟩
    rw [← hmatchingEq]
    exact hmaximum
  · intro hmaximum
    exact ⟨written, hmaximum, rfl⟩

/-- Raw-molecule support test for one attached atom: the written noncumulative double bonds of the
localized mancude component containing `attached` are exactly a maximum matching of that component's
edge list.  `localizedMancudeComponentEdges` and `bondOrder` are the same raw data the production
labeler consumes, so no representation boundary is crossed here. -/
def mancudeComponentSupportCheck (mol : RawMolecule) (attached : ℕ) : Bool :=
  writtenMancudeEdgeMaximumCheck
    (mol.localizedMancudeComponentEdges attached)
    ((mol.localizedMancudeComponentEdges attached).filter
      fun edge => mol.bondOrder edge.1 edge.2 == 2)

/-- The per-component test is exactly the written-maximum hypothesis of
`generalMancudeRule1aLabel?_exists_of_localized_maximum`. -/
theorem mancudeComponentSupportCheck_eq_true_iff (mol : RawMolecule) (attached : ℕ) :
    mancudeComponentSupportCheck mol attached = true ↔
      RawMolecule.IsMaximumMancudeEdgeMatching
        ((mol.localizedMancudeComponentEdges attached).filter
          fun edge => mol.bondOrder edge.1 edge.2 == 2)
        (mol.localizedMancudeComponentEdges attached) := by
  unfold mancudeComponentSupportCheck
  exact writtenMancudeEdgeMaximumCheck_eq_true_iff
    (mol.localizedMancudeComponentEdges attached)
    ((mol.localizedMancudeComponentEdges attached).filter
      fun edge => mol.bondOrder edge.1 edge.2 == 2)

/-- Molecule-wide support test: every attached atom's localized mancude component carries its
written noncumulative double bonds as an exact maximum edge-occurrence matching. -/
def localizedMancudeKekuleCheck (mol : RawMolecule) : Bool :=
  (List.range mol.atomCount).all fun attached => mancudeComponentSupportCheck mol attached

/-- Component-wise reading of the molecule-level test. -/
theorem localizedMancudeKekuleCheck_eq_true_iff_forall (mol : RawMolecule) :
    localizedMancudeKekuleCheck mol = true ↔
      ∀ attached : Fin mol.atomCount, mancudeComponentSupportCheck mol attached.val = true := by
  unfold localizedMancudeKekuleCheck
  rw [List.all_eq_true]
  constructor
  · intro checked attached
    exact checked attached.val (List.mem_range.mpr attached.isLt)
  · intro checked attached bound
    exact checked ⟨attached, List.mem_range.mp bound⟩

/-- The molecule-level test is exactly the authoritative written-maximum gate.  The authoritative
predicate is reused, not duplicated, so the production and authoritative pipelines keep one notion
of Kekulé admissibility. -/
theorem localizedMancudeKekuleCheck_eq_true_iff (mol : RawMolecule) :
    localizedMancudeKekuleCheck mol = true ↔
      AuthoritativeCIPMancudeTotality.LocalizedMancudeKekuleAdmissible mol := by
  rw [localizedMancudeKekuleCheck_eq_true_iff_forall]
  constructor
  · intro checked attached
    exact (mancudeComponentSupportCheck_eq_true_iff mol attached.val).1 (checked attached)
  · intro admissible attached
    exact (mancudeComponentSupportCheck_eq_true_iff mol attached.val).2 (admissible attached)

/-- The actual production dispatcher is total at a localized attached duplicate whenever the
computed per-component support check accepts.  The maximum-matching premise is no longer a free
hypothesis: it is discharged by `decide` (or any kernel reduction of the check) at a concrete
molecule. -/
theorem mancudeRule1aLabel?_exists_of_componentSupportCheck
    (mol : RawMolecule) (hwellFormed : mol.WellFormed) (hunique : mol.BondRecordsUnique)
    (attached duplicated : Fin mol.atomCount)
    (hlocalized : RawMolecule.containsUndirectedEdge mol.localizedMancudeEdges
      attached.val duplicated.val = true)
    (hcheck : mancudeComponentSupportCheck mol attached.val = true) :
    ∃ label, mol.mancudeRule1aLabel? attached.val duplicated.val = some label :=
  mol.mancudeRule1aLabel?_exists_of_localized_maximum hwellFormed hunique attached duplicated
    hlocalized ((mancudeComponentSupportCheck_eq_true_iff mol attached.val).1 hcheck)

/-- Molecule-wide form: a single verified `localizedMancudeKekuleCheck` makes the production
dispatcher total at every localized attached duplicate of the molecule. -/
theorem mancudeRule1aLabel?_exists_of_kekuleCheck
    (mol : RawMolecule) (hwellFormed : mol.WellFormed) (hunique : mol.BondRecordsUnique)
    (hcheck : localizedMancudeKekuleCheck mol = true)
    (attached duplicated : Fin mol.atomCount)
    (hlocalized : RawMolecule.containsUndirectedEdge mol.localizedMancudeEdges
      attached.val duplicated.val = true) :
    ∃ label, mol.mancudeRule1aLabel? attached.val duplicated.val = some label := by
  have hcomponent : mancudeComponentSupportCheck mol attached.val = true :=
    (localizedMancudeKekuleCheck_eq_true_iff_forall mol).1 hcheck attached
  exact mancudeRule1aLabel?_exists_of_componentSupportCheck mol hwellFormed hunique
    attached duplicated hlocalized hcomponent

/-- Refusal is explicit: an actual `none` return at a localized attached duplicate forces the
per-component check to `false`.  This is a necessary condition for refusal, not an equivalence: No converse is established. -/
theorem mancudeComponentSupportCheck_eq_false_of_label_none
    (mol : RawMolecule) (hwellFormed : mol.WellFormed) (hunique : mol.BondRecordsUnique)
    (attached duplicated : Fin mol.atomCount)
    (hlocalized : RawMolecule.containsUndirectedEdge mol.localizedMancudeEdges
      attached.val duplicated.val = true)
    (hnone : mol.mancudeRule1aLabel? attached.val duplicated.val = none) :
    mancudeComponentSupportCheck mol attached.val = false := by
  apply Bool.eq_false_of_not_eq_true
  intro hcheck
  obtain ⟨label, hlabel⟩ := mancudeRule1aLabel?_exists_of_componentSupportCheck
    mol hwellFormed hunique attached duplicated hlocalized hcheck
  rw [hnone] at hlabel
  exact absurd hlabel (by simp)

/-!
## Kernel-only regressions

The examples below are proved from the recursive equation lemmas and finite-list simplification.
Direct `decide` reduction gets stuck on the well-founded recursion, so its equations are used
explicitly. The executable check and the assertions are unchanged.  They use no `native_decide`, no compiled evaluator and no `sorry`, and they separate the
four ways a written occurrence list can fail: submaximum size, overlapping endpoints, an absent
edge, and a reoriented edge.  They are stated on raw edge lists because the check is a raw-list
decision; molecule-level instantiations follow the pattern of
`TetraStereo/Examples/Rule1aUniformFallbackRegression.lean`.
-/

/-- Valid maximum: two disjoint written double bonds are the unique maximum matching. -/
theorem writtenMancudeEdgeMaximumCheck_accepts_disjoint_maximum :
    writtenMancudeEdgeMaximumCheck [(0, 1), (2, 3)] [(0, 1), (2, 3)] = true := by
  simp [writtenMancudeEdgeMaximumCheck, RawMolecule.maximumMancudeEdgeMatchings,
    RawMolecule.exhaustiveMancudeEdgeMatchings_cons, RawMolecule.remainingMancudeEdges,
    RawMolecule.MancudeEdgesDisjoint, RawMolecule.mancudeFamilyMaximumSize]

/-- Submaximum: dropping one written double bond leaves a strictly smaller matching. -/
theorem writtenMancudeEdgeMaximumCheck_rejects_submaximum :
    writtenMancudeEdgeMaximumCheck [(0, 1), (2, 3)] [(0, 1)] = false := by
  simp [writtenMancudeEdgeMaximumCheck, RawMolecule.maximumMancudeEdgeMatchings,
    RawMolecule.exhaustiveMancudeEdgeMatchings_cons, RawMolecule.remainingMancudeEdges,
    RawMolecule.MancudeEdgesDisjoint, RawMolecule.mancudeFamilyMaximumSize]

/-- Overlapping written edges: two occurrences sharing an endpoint are not a matching at all. -/
theorem writtenMancudeEdgeMaximumCheck_rejects_overlapping_written :
    writtenMancudeEdgeMaximumCheck [(0, 1), (1, 2)] [(0, 1), (1, 2)] = false := by
  simp [writtenMancudeEdgeMaximumCheck, RawMolecule.maximumMancudeEdgeMatchings,
    RawMolecule.exhaustiveMancudeEdgeMatchings_cons, RawMolecule.remainingMancudeEdges,
    RawMolecule.MancudeEdgesDisjoint, RawMolecule.mancudeFamilyMaximumSize]

/-- The same incident-edge component accepts the single written occurrence, so the rejection above
is not a blanket size test. -/
theorem writtenMancudeEdgeMaximumCheck_accepts_single_on_incident_pair :
    writtenMancudeEdgeMaximumCheck [(0, 1), (1, 2)] [(0, 1)] = true := by
  simp [writtenMancudeEdgeMaximumCheck, RawMolecule.maximumMancudeEdgeMatchings,
    RawMolecule.exhaustiveMancudeEdgeMatchings_cons, RawMolecule.remainingMancudeEdges,
    RawMolecule.MancudeEdgesDisjoint, RawMolecule.mancudeFamilyMaximumSize]

/-- Empty component: the empty written list is its unique maximum matching. -/
theorem writtenMancudeEdgeMaximumCheck_accepts_empty :
    writtenMancudeEdgeMaximumCheck [] [] = true := by
  simp [writtenMancudeEdgeMaximumCheck, RawMolecule.maximumMancudeEdgeMatchings,
    RawMolecule.mancudeFamilyMaximumSize]

/-- Invalid list: an edge absent from the component is rejected. -/
theorem writtenMancudeEdgeMaximumCheck_rejects_absent_edge :
    writtenMancudeEdgeMaximumCheck [] [(3, 4)] = false := by
  simp [writtenMancudeEdgeMaximumCheck, RawMolecule.maximumMancudeEdgeMatchings,
    RawMolecule.mancudeFamilyMaximumSize]

/-- Invalid list: the written occurrence carries its orientation, so the mirrored pair differs. -/
theorem writtenMancudeEdgeMaximumCheck_rejects_reoriented_edge :
    writtenMancudeEdgeMaximumCheck [(0, 1)] [(1, 0)] = false := by
  simp [writtenMancudeEdgeMaximumCheck, RawMolecule.maximumMancudeEdgeMatchings,
    RawMolecule.exhaustiveMancudeEdgeMatchings_cons, RawMolecule.remainingMancudeEdges,
    RawMolecule.mancudeFamilyMaximumSize]

/-- Reflection accepts: the accepted raw list really is a maximum edge matching. -/
theorem isMaximumMancudeEdgeMatching_of_check_disjoint_maximum :
    RawMolecule.IsMaximumMancudeEdgeMatching [(0, 1), (2, 3)] [(0, 1), (2, 3)] :=
  (writtenMancudeEdgeMaximumCheck_eq_true_iff [(0, 1), (2, 3)] [(0, 1), (2, 3)]).1
    writtenMancudeEdgeMaximumCheck_accepts_disjoint_maximum

/-- Reflection rejects submaximum lists at the predicate level, not only at the `Bool` level. -/
theorem not_isMaximumMancudeEdgeMatching_of_check_submaximum :
    ¬ RawMolecule.IsMaximumMancudeEdgeMatching [(0, 1)] [(0, 1), (2, 3)] :=
  fun hmaximum => absurd
    ((writtenMancudeEdgeMaximumCheck_eq_true_iff [(0, 1), (2, 3)] [(0, 1)]).2 hmaximum)
    (by rw [writtenMancudeEdgeMaximumCheck_rejects_submaximum]; decide)

/-- Reflection rejects overlapping written lists at the predicate level. -/
theorem not_isMaximumMancudeEdgeMatching_of_check_overlapping :
    ¬ RawMolecule.IsMaximumMancudeEdgeMatching [(0, 1), (1, 2)] [(0, 1), (1, 2)] :=
  fun hmaximum => absurd
    ((writtenMancudeEdgeMaximumCheck_eq_true_iff [(0, 1), (1, 2)] [(0, 1), (1, 2)]).2 hmaximum)
    (by rw [writtenMancudeEdgeMaximumCheck_rejects_overlapping_written]; decide)

end ProductionMancudeSupportCheckProofs
end UniversalProof
end TetraStereo
