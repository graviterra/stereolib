# Ring source status — 24 November 2026

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

For the grouped frozen-auxiliary procedure, Lean derives a unique result at every simple
bonded path and a unique report for every requested atom list on admitted coordinates. The
existence and uniqueness proofs pass a transitive dependency check against twelve declarations
for the global evaluator and its agreement theorems. A separate theorem connects that derivation
to the grouped output. [Graph report](TetraStereo/Engine/RingGraphReport.lean) ·
[Dependency check](validation/ring-chronology/GraphDerivationIndependence.lean)

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

## Full-path graph derivation and recursive report

The earlier occurrence and rebuilt comparators agree with the grouped evaluator, including its
parent-by-parent Rule 4b traversal. That equality is not a derivation of all grouped scores from
Hanson et al. In the [41-atom cross-parent witness](validation/ring-chronology/Rule4bCrossParent.lean),
both procedures read the same eight frozen geometric auxiliaries. Grouped concatenation gives
words 1100 and 1010 and assigns R/S at the root. Full-path whole-sphere ordering gives 1100
for both arms under either reference and ultimately refuses. The pinned Jmol default replay
also refuses on this input. [Shared molecular file](validation/ring-chronology/Rule4bCrossParent.mol) ·
[Jmol control](validation/ring-chronology/Rule4bCrossParent.spt)

[Full-path graph derivations](TetraStereo/Engine/RingFullPathPairs.lean) expand the entire next
sphere before sorting complete path keys. Every legal ordering of equal-key visits emits the
same reference word, including visits with different parents. The frozen-score theorem obtains
references and words from the actual grouped frozen store under its through-4a tie hypotheses.
[Path-rank transport](TetraStereo/Engine/RingPathRankTransport.lean) relates molecular priority
keys to local sibling-rank characters; this is a representation theorem for the shared priorities.

The separate [full-path publication](TetraStereo/Engine/RingFullPathPublication.lean) uses its own
recursive frozen store. `reachable_fourB` derives Hanson's best-of-four-word contest for every
pair on either geometry; it decides only after earlier rules tie. `reachable_frame` supplies
both geometries' four ordinary keys, signed fixed-reference Rule 5 comparisons, complete eligible
trial lists and coordinate readings, and the result of cancelling the two vote populations.
`molecular_iff` equates each computed result with a finite molecular derivation that recursively
justifies its visible deeper assignments without referring to the publication table. A separate
induction proves completion at every site on admitted coordinates.

The underlying [report interface](TetraStereo/Engine/RingFullPathReport.lean),
`RingFullPathReport.forAtoms?`, returns exactly these source-derived rows in request order,
including duplicates and completed refusals. It is independent of within-sphere enumeration.
[Executable report controls](validation/ring-chronology/FullPathReport.lean) cover two spiro
inputs and a substituted cyclopropane with deeper auxiliaries. This does not change the existing
grouped public API. The public `Engine.ringMolecularReportFromRaw?` now admits raw graph and
coordinates and resolves zero-based requested atom IDs. `fromRaw_graph_iff` characterizes its
rows by the two-geometry source derivation along simple bonded paths, including every deeper
auxiliary read. It preserves request order and repeated IDs; invalid admission, inadmissible
coordinates and out-of-range IDs fail the request. A row with absent labels is a completed refusal.
[Raw-to-graph API theorem](TetraStereo/Engine/RingMolecularReport.lean)

The public implementation uses the [constitutional shortcut](TetraStereo/Engine/RingFullPathConstitution.lean):
four distinct zero-duplicate-mass constitutional ranks determine both coordinate hands before
stereo suffixes or marks are read. On any ready reader `fast_local` equates this shortcut with
the full-path publication; `fast_state` and `fast_report_exact` extend the equality to the
recursive state and every requested list. The shortcut runs at the root and each queued auxiliary;
a root inventory is needed only on a constitutional tie. This proof uses the full-path keys,
unmarked trial and reversal count directly, without a grouped-publication premise.
`Engine.ringMolecularReport?` selects detected centres and `ringMolecularCarbonReport?` all carbons;
`ringMolecularReportForAtoms?` accepts valid typed atoms. The older `ringGroupedMolecularReport?`
and `ringGroupedCarbonReport?` names remain compatible aliases for their earlier grouped procedure.
[Public names](TetraStereo/Engine/PublicAPI.lean)

The theorem shares the molecular inventory, through-4a/4c priorities,
marked-node policy and coordinate interpretation with its source judgments; independent chemical
fidelity and the external source-review obligations remain open. Inherited priorities at internal
edges and rule applicability need independent justification: the Rule 5 edge priority uses the
lowercase stage without a separate local Rule 4b stage. Reference-count and four-list
procedures are not claimed equivalent on every reference population. The admitted single-bond,
constant-charge domain still requires extension.

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

Bond-record order is a separate graph invariant. For structurally admitted inputs with identical
numbered atom records and coordinates and permuted bond lists,
[RingBondRecordOrder](TetraStereo/Engine/RingBondRecordOrder.lean) transports coordinate admission
and proves literal equality of complete public grouped reports, including centre order, and
selected grouped/cached reports with repeated requests. It assumes no computed-label agreement.
The [single-bond VS300 derivative certificate](validation/ring-chronology/VS300SingleAdmission.lean)
checks these premises for four presentations; it establishes equality without assigning C61 an
absolute letter. The published VS300 has multiple bonds and lies outside this ring proof domain.

The [Jmol diagnostic controls](validation/ring-chronology/check_vs300_bond_order.py) isolate a
release-specific auxiliary return/reread defect: unchanged numbered atoms, coordinates and bonds
can give full-mode C61 results r, absence or s when bond records exchange places. A constructed
single-bond derivative reproduces the defect and is admitted by Lean; it has no published target
descriptor or stability claim. Selective source interventions and
[Figure 14/cubane controls](validation/ring-chronology/check_figure14_regeneration.py) distinguish
auxiliary assignment from optional reassignment. These measurements neither prove universal
Jmol correspondence nor justify retrying every baseline refusal in full mode.

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

The [module inventory](source-modules.json) contains all 4,414 maintained Lean modules.
The original umbrella brings the package total to 4,415 Lean files. The validation drivers
are counted separately.
The universal theorem and full chemical approval remain open. See the [README](README.md) for
existing acyclic results, collaboration guidance and safe source checks.
