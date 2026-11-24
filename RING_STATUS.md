# Ring source status — 23 November 2026

The ring programme now has an explicit executable development profile and an independent
source-model connection to its detected-centre report. This is a scoped source update, not a
claim of full CIP correctness, chemical completion or release readiness.

## Established connections

- **Public engine:** [`accumulatedReferencesRegenerated`](TetraStereo/Engine/LocalizedChemicalRingPublic.lean)
  executes the cached evaluator and equals the prepared report, preserving refusal entries.
  It is an opt-in profile; the default evaluator is unchanged. The
  [physical admission bridge](TetraStereo/Engine/LocalizedChemicalRingPhysicalCertificate.lean)
  can derive the required calibration evidence when its coordinate checks pass.
- **Independent source and actual report:** the
  [source-model construction](TetraStereo/OneCenter/LocalizedChemicalRingJointPreparedSourceModel.lean)
  and [existence package](TetraStereo/OneCenter/LocalizedChemicalRingJointPreparedSourceModelExistence.lean)
  establish a unique independent accumulated-reference profile agreeing with the actual
  detected-centre report, including refusals.
- **All-root cancellation:** the
  [all-root cancellation/report package](TetraStereo/OneCenter/LocalizedChemicalRingAllRootCancellationReport.lean)
  proves cancellation equality with the actual consensus/step at every final root, including
  two-pair outcomes. The [selected-resolution proof](TetraStereo/OneCenter/LocalizedChemicalRingJointPreparedRootSelectedResolution.lean)
  discharges the earlier resolution premises.
- **Concrete exact result:** the
  [DoubleC3 physical report](TetraStereo/OneCenter/LocalizedChemicalRingJointPreparedDoubleC3PhysicalReport.lean)
  derives auxiliary `R`/`S`, exact final lowercase `s`, and actual report membership. Its
  [source model](TetraStereo/OneCenter/LocalizedChemicalRingJointPreparedDoubleC3SourceModel.lean)
  has an inhabited unique value.
- **Physical classification:** root-key equality has an independent
  [physical-transport characterization](TetraStereo/OneCenter/LocalizedChemicalRingRootPhysicalKeyClasses.lean).
  [Transitive roots](TetraStereo/OneCenter/LocalizedChemicalRingRootTransitiveReport.lean)
  and [nontransitive roots with at most one moving class](TetraStereo/OneCenter/LocalizedChemicalRingRootSingleMovingClass.lean)
  have exact report-level success/refusal criteria. The
  [two-moving-pairs theorem](TetraStereo/OneCenter/LocalizedChemicalRingRootTwoMovingPairs.lean)
  localizes nontransitive refusals without odd symmetry to two moving pairs.
- **Exact two-pair entries:** the [pairing parity theorem](TetraStereo/OneCenter/LocalizedChemicalRingPairingParity.lean)
  identifies the parity of a four-ligand priority order with its action on the three pairings.
  [`report_iff_pairingDescriptor`](TetraStereo/OneCenter/LocalizedChemicalRingTwoPairReport.lean#L230)
  then gives the exact two-pair report entry, including refusal, absolute letter and casing.
  Its criterion reads independently specified contextual source priorities on both geometries;
  no fallback output, desired descriptor or successful promotion is supplied as an assumption.
  Without odd boundary symmetry, success requires matching promotion parities between the two
  classes on both geometries. After success, a parity change under reflection gives lowercase;
  unchanged parity gives uppercase. The calibrated original frame supplies the absolute letter
  together with the original priority parity. Odd-boundary roots refuse.
- **All-root outcomes:** [`existsUnique_allRoot_outcomes`](TetraStereo/OneCenter/LocalizedChemicalRingTwoPairReport.lean#L353)
  combines transitive, single-moving-class and two-pair cases into exact success/refusal criteria
  at every detected root, using one unique source profile. The root frames and source model are
  derived. This is an outcome classification for the named procedure; it does not yet supply
  the complete chemical interpretation of successful letters and casing in every class.

## Domain and remaining work

The generic ring results concern finite inputs with single bonds and constant formal charge,
raw/certified structure agreement, stereochemical admissibility and localized covalent support.
Rings and stereochemically dependent non-root centres are allowed. Physical results additionally
require calibrated coordinates/configuration at every detected centre. Structural admission
alone does not establish this calibration. Auxiliary cancellation statements retain their stated
tied-branch scope; each linked declaration gives its exact hypotheses.

The [exact public certificate](TetraStereo/Engine/LocalizedChemicalRingExactCertificate.lean)
now supplies source-priority letters, casing and refusal criteria at every detected root under
the stated domain hypotheses. This closes the earlier public-interface integration gap. The
[chronology certificate](TetraStereo/Engine/LocalizedChemicalRingChronologyCertificate.lean)
connects frozen disagreements to changed downstream auxiliary readings.

Independent chemical fidelity remains open: contextual reference lifetime, regeneration,
publication schedules and recursive priority meanings must be justified against the intended
chemical procedure. Exactness for the named source model does not establish normative adoption.

The [grouped comparison machinery](TetraStereo/Engine/RingGroupedStereo.lean) builds stage-specific
molecular profiles. The [comparison agreement interface](TetraStereo/Engine/RingComparisonAgreement.lean)
relates independently derived two-geometry comparisons and auxiliary values to source observations.
Its coverage and agreement hypotheses remain explicit; universal comparison coverage is not claimed.

The [two-stage sphere procedure](TetraStereo/Engine/RingSphereQueue.lean) first tries a strict
constitutional ranking, then uses a fresh occurrence-addressed auxiliary store for each root.
It publishes an entire sphere together, from farthest to nearest, including completed refusals.
Its whole-report equality theorem covers every requested atom list on admitted coordinates.
Auxiliary descriptors stay fixed during each Rule 6 trial; a different original root receives
its own assignments.

The [rebuilt stereo evaluator](TetraStereo/Engine/RingRebuiltStereo.lean) now uses zero mass for
ring duplicates at the original root, every queued centre and every stereo sibling sort,
including marked trials. Shallow and deep sorting preserve occurrence identities, reference
path order and selected hands. On ready stores its deciding rule and signed score agree on
both geometries; on admitted coordinates its entire recursive state and requested report equal
the grouped procedure. Repeated requests, lowercase assignments and completed refusals are
included. The [occurrence controls](validation/ring-chronology/OccurrenceStereo.lean) and
[carbon-13 closure control](validation/ring-chronology/Rule2RealMass.lean) exercise these boundaries.

The [Rule 4b selector](TetraStereo/Engine/RingReferenceVotes.lean) chooses the closest occupied
sphere and greatest eligible rank path, retaining each child's rank and inherited parent rank.
It counts all eligible R/S occurrences across parent groups. Empty populations supply no hand,
nonempty balanced populations both, and strict majorities one. In the
[48-atom ring](validation/ring-chronology/ReferenceVoteRing.lean), SSS, RRS and RRS give S by five
to four; majority-per-parent would give R. The rebuilt and grouped evaluators select S and R
on reflection. The [21-atom unequal-rank control](validation/ring-chronology/ReferenceSelectionCut.lean)
selects a senior S occurrence over two junior R occurrences.

The [neutral-word theorem](TetraStereo/Engine/RingNeutralPromotion.lean) preserves complete
Rule 4c row boundaries when all Rule 6 bits are zero. The
[cut certificate](TetraStereo/Engine/RingPromotionCut.lean) derives refusal on both geometries
from ordinary ties, at least three eligible marks, at most two returning arms and marked-atom
locality. Its checker reads molecular identifiers and returning-arm flags; it need not run
marked trials. At an original root, Lean now derives the return-arm bound and locality from the molecular graph.
A path between two neighbors that avoids the root yields a closure down each arm. With fewer
than three origin-zero duplicate occurrences, the evaluator can use ordinary orientation and casing
and skip promotion. A remaining tie gives a completed refusal. At three or more duplicates the
evaluator uses the grouped procedure. The theorem covers each requested atom on admitted coordinates.
Auxiliary occurrences keep their frozen evaluation. [Path proof](TetraStereo/Engine/RingRootReturnPath.lean) ·
[Count-based publication theorem](TetraStereo/Engine/RingRootReturn.lean) ·
[Molecular controls](validation/ring-chronology/RootReturns.lean)

These results close the earlier whole-centre/report integration obligation for the named
frozen-auxiliary procedure. Independent chemical justification remains open for the shared
occurrence inventory, reference selection, stereo observations and promotion policy on the
actual stores. Neither report equality nor the optional regenerated profile establishes
universal IUPAC correctness.

## Runtime and coordinate controls

The separate [Centres API](TetraStereo/Engine/CentresRing.lean) runs the pinned 2018 release and
checks its chronological report. Molecular and mirror APIs strengthen this with independent
comparison/publication derivations and spatial casing. The
[fluorospiro counterexample](TetraStereo/Examples/CentresRingSpiroCasing.lean) demonstrates `S`/`s`
under atom renumbering and a lowercase reflection conflict. The
[comparison witness](TetraStereo/Examples/RingSourceComparisonAgreement.lean) independently
checks the affected molecular comparisons and publications. The published dioxaspiro input is a
separate annotated coordinate control, supported by the
[source checker](TetraStereo/Engine/CentresSpiroSource.lean). Configured-centre inventories are part
of the input: changing them can change auxiliary availability.

The [frozen evaluator](TetraStereo/Engine/LocalizedChemicalRingFrozenExecution.lean) is a matched
control for auxiliary regeneration, not a claim of equivalence with the pinned release.
See [setup and entry points](docs/ring-evaluator.md) for executable and offline routes, receipt
limitations and the distinction between structural and coordinate admission.

## Verification boundary

The earlier preserved original-source checkpoints cover **74 distinct source files and 422
kernel guards**. The subsequent two-module checkpoint adds **eight kernel-only guards** for pairing
parity, exact two-pair entries and exhaustive root outcomes. The two public source files are
byte-identical to those accepted source snapshots; review verified the current and frozen source
and compiled-artifact hashes and the saved successful bounded-build receipts.

For the 23 November update, a focused Lean check against the development artifacts passed
the kernel-only assertions for the rebuilt signature, the full report, the molecular Rule 4b
selector and the conditional Rule 6 refusal. The public export was checked for module coverage
and reproducibility. A clean-checkout compilation of the public package remains unverified.

The [module inventory](source-modules.json) contains all 4,394 maintained Lean modules.
The original umbrella brings the package total to 4,395 Lean files. The validation drivers
are counted separately.
The universal theorem and full chemical approval remain open. See the [README](README.md) for
existing acyclic results, collaboration guidance and safe source checks.
