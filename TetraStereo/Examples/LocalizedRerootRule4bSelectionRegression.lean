import TetraStereo.OneCenter.LocalizedOccurrenceRule45Exact

set_option autoImplicit false

namespace TetraStereo.Examples.LocalizedRerootRule4bSelectionRegression

open TetraStereo.OneCenter
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-!
# Kernel regressions for P-92.5.2.1 Rule-4b reference selection

Rank paths identify equivalence classes in the already re-ranked ligand digraph.  Selection must
skip spheres without an uppercase chiral descriptor, use only the first chiral rank class in the
first applicable sphere, and apply the R/S majority rule within exactly that class.
-/

abbrev RankedLabelLayer :=
  List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))

/-- Pseudoasymmetric labels do not supply a Rule-4b reference, and a lower chiral rank class in
the same sphere cannot alter the unique highest-class reference. -/
example :
    localizedRule4bReferencesFromRankedLabels
      ([ [([], none)]
       , [([0], some (.pseudoasymmetric .r)),
          ([1], some (.chiral .R)),
          ([2], some (.chiral .S)),
          ([2], some (.chiral .S))] ] : List RankedLabelLayer) = [.R] := by
  rfl

/-- A tied reference population is lifted in the source-specified R-then-S order. -/
example : localizedRule4bcReferenceAlternatives [RS.R, RS.S] =
    [some RS.R, some RS.S] := by
  rfl

/-- The Rule-5 common-R reading recognizes the corresponding reflection-variant uppercase
auxiliary sense. -/
example :
    localizedRule5Priority .R (some (.chiral .R)) = 1 := by
  rfl

/-- Lowercase `r/s` are reflection-invariant and are not converted into a Rule-5 pair. -/
example :
    localizedRule5Priority .R (some (.pseudoasymmetric .r)) = 0 := by
  rfl

/-- Equivalent highest-ranked nodes are counted together; an R majority selects only R. -/
example :
    localizedRule4bReferencesFromRankedLabels
      ([ [([0], some (.chiral .R)),
          ([0], some (.chiral .S)),
          ([0], some (.chiral .R)),
          ([1], some (.chiral .S))] ] : List RankedLabelLayer) = [.R] := by
  rfl

/-- Equal populations in the equivalent highest rank class retain both sequential references. -/
example :
    localizedRule4bReferencesFromRankedLabels
      ([ [([0], some (.chiral .R)),
          ([0], some (.chiral .S)),
          ([1], some (.chiral .R))] ] : List RankedLabelLayer) = [.R, .S] := by
  rfl

/-- The first applicable sphere is decisive even when a later sphere contains more descriptors. -/
example :
    localizedRule4bReferencesFromRankedLabels
      ([ [([], none)]
       , [([0], some (.chiral .S))]
       , [([0, 0], some (.chiral .R)),
          ([0, 0], some (.chiral .R))] ] : List RankedLabelLayer) = [.S] := by
  rfl

/-! The molecule-backed wrapper is intentionally a separate contract from the pure selector. -/

#check CertifiedLocalizedCIPInput.buildLocalizedRerootUniqueReferenceRule4cKey?
#check CertifiedLocalizedCIPInput.buildLocalizedRerootUniqueReferenceRule4cKey?_sound
#check CertifiedLocalizedCIPInput.compareLocalizedRerootUniqueReferenceRule4cKeys
#check CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule4bcKey?
#check CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule4bcKey?_sound
#check CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundRule4bcKeys
#check CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule45Key?
#check CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule45Key?_sound
#check CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundThroughRule5
#check CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45Key?_eq_some_iff_canonical
#check CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule4bcKey?_eq_some_iff_canonical
#check CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule45Key?_eq_some_iff_canonical
#check CertifiedLocalizedCIPInput.localizedOccurrenceRule45Descriptor?_eq_some_iff_canonical
#check CertifiedLocalizedCIPInput.localizedOccurrenceRule45Descriptor?_eq_none_iff_no_canonical
#check CertifiedLocalizedCIPInput.localizedOccurrenceRule45Descriptor?
#check CertifiedLocalizedCIPInput.localizedOccurrenceRule45Descriptor?_sound

end TetraStereo.Examples.LocalizedRerootRule4bSelectionRegression
