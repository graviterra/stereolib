# Ring source status — 25 November 2026

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

The underlying [full-path report](TetraStereo/Engine/RingFullPathReport.lean) remains a
separate source interface. The public aliases now select
[`RingHydrogenReport`](TetraStereo/Engine/RingHydrogenReport.lean), through the prepared chemical
report and its selected pyramidal inventory. It completes ordinary hydrogens and requires the
same whole requested report on every admitted orientation of unplaced P–H bonds. Its
`fromRaw_graph_iff` and `fromRaw_population_iff` characterize every reading by recursive molecular
source derivations. `fromRaw_domain_iff` makes admission of every placement and agreement between
their derivations explicit. Invalid IDs or coordinates, failed placement admission and competing
reports give outer `none`; an agreed refusal remains a row in a successful report. Requests retain
order and duplicates. Hydrogen-complete admitted inputs with valid IDs and the stated coordinate
hypotheses have a unique report. [Public aliases](TetraStereo/Engine/PublicAPI.lean) ·
[Placement domain](TetraStereo/Engine/RingHydrogenReportDomain.lean)

On the public recursive store, the reference-population and full-path four-list procedures agree
for every valid pair tied through Rule 4a, including balanced and empty populations. Ordinary-key
ties are characterized by through-4c root priorities and unordered signed priority-path inventories
at every distance. The integrated inventory evaluator also reconstructs strict priorities and the
whole raw report. These results use the same preceding-rule priorities, hands and promotion policy;
they are not independent chemical approval. [Population theorem](TetraStereo/Engine/RingPopulationReport.lean) ·
[Ordinary inventory](TetraStereo/Engine/RingOrdinaryLigandInventory.lean) ·
[Inventory evaluator](TetraStereo/Engine/RingStereoInventoryReport.lean)

## Repaired chemical controls and remaining Rule 1b question

The earlier mixed explicit/implied hydrogen and pyramidal phosphorus counterexamples exposed
failures of the superseded public profile. The current public API refuses at the substituted
carbon of 1-bromo-1-fluorocyclopropane across the tested hydrogen spellings. On the oxirane bearing
mirror-related P(F)(Cl) arms it returns carbon s/s and phosphorus R/S then S/R. The strict
`--require-conformance` control checks these expected results. This repairs those witnesses;
it does not prove completeness of the new profile.
[Chemical replay](validation/ring-chronology/LocalRuleCoverage.lean) ·
[Phosphorus geometry](validation/ring-chronology/PyramidalPhosphaneOxirane.mol)

The selected pyramidal inventory includes neutral, nonaromatic three-coordinate P/As/Sb and
structurally selected bridgehead or N-alkyl oxaziridine nitrogen after hydrogen materialization.
The same selector supplies roots and auxiliary occurrences. Molecular path theorems characterize
recognized oxaziridine readings, including flat refusals and different hands at distinct addresses.
These structural tests do not establish an exhaustive chemical stability inventory.
[Selector](TetraStereo/Engine/RingPyramidalPublication.lean) ·
[Oxaziridine auxiliary theorem](TetraStereo/Engine/RingOxaziridineAuxiliaryReport.lean)

Lean settles the Rule 2 mass question for every admitted pair of ligand directions. Rebuilding
the branch priorities with zero mass at each ring duplicate preserves all three outcomes of
the constitutional comparison, including a tie. The open Rule 1b question concerns which atom
supplies the origin for measuring a duplicate's distance when an auxiliary is evaluated.
[All-ligand comparison theorem](TetraStereo/Engine/RingLigandTreeComparison.lean#L175)

A hydrogen-complete 13-atom spiro graph gives opposite final descriptors under two duplicate-origin
distance conventions. The public raw API measures from the original root and gives R/S. The
alternative active-focus evaluator gives S/R. Four auxiliary hands change; one carbon-arm priority
exchange reverses the root. Pinned Centres reproduces this policy-dependent reversal, and Jmol
agrees with the public convention on the supplied synthetic coordinates. Which convention the
chemical sources prescribe for rerooted auxiliaries remains open.
[Molecular raw replay and trace](validation/ring-chronology/OriginMetricSpiro.lean) ·
[Shared geometry](validation/ring-chronology/OriginMetricSpiro.mol) ·
[Centres replay](validation/ring-chronology/CentresOriginMetricSpiro.java) ·
[Jmol replay](validation/ring-chronology/OriginMetricSpiro.spt)

Lean proves equality of the two stores and raw reports under explicit graph conditions, including
when deleting one edge leaves a forest. A stronger order criterion checks actual closure-origin
pairs at eligible auxiliary foci. Failure of a sufficient criterion alone does not imply a changed
report. Any actual raw disagreement reaches an auxiliary with identical incoming stores and a
changed local publication whose policy switch changes the root on rerun.
[Metric domain](TetraStereo/Engine/RingOriginMetricReport.lean) ·
[Graph criterion](TetraStereo/Engine/RingOriginOrderGraph.lean) ·
[Single-occurrence witness](TetraStereo/Engine/RingOriginCausal.lean)

VS084 separates auxiliary disagreement from final-output disagreement. With published one-based
atom numbers, the fixture observes R versus S at path 4–5–6–7–1–2–3 in batch 4 below root 4,
and both evaluators give S at root 4 and R on reflection. The sphere lists retain the disagreement
at every subsequent batch because equality at a later batch implies equality at each earlier
boundary. Root 1 has complete store agreement. For any tetrahedral requested root with a strict
constitutional decision, `strict_root_cells` proves that both evaluators return the same root
cell. The remaining question is which auxiliary differences affect a constitutionally tied root.
[VS084 fixture](validation/ring-chronology/OriginTwinVS084.lean) ·
[Kernel theorem](TetraStereo/Engine/RingOriginTwinStore.lean)

A separate Python screen of 480 requests found the strict auxiliary reversal pattern in 116,
including 17 requests with published root labels. Those counts describe auxiliary disagreements.
The executable Lean replay above checks VS084. [Hanson et al. validation corpus](https://doi.org/10.1021/acs.jcim.8b00324)

Independent chemical justification of internal-edge priorities, rule applicability, reference
lifetime, promotion decisions, broader centre/domain coverage and external source review remains
open. No universal CIP theorem or chemical completion is claimed for the current public profile.

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

Bond-record order is a separate graph invariant.
[`RingBondRecordOrder`](TetraStereo/Engine/RingBondRecordOrder.lean) now proves literal equality
of the public raw response under bond-list permutations through implicit hydrogen placement and
consensus, including malformed input and invalid IDs. For independently admitted presentations,
its physical graph/coordinate hypotheses also permit different stored neighbor orders. The older
grouped/cached invariance results remain scoped to those procedures. The
[single-bond VS300 derivative certificate](validation/ring-chronology/VS300SingleAdmission.lean)
establishes equality across its four presentations without an absolute target descriptor.
Published VS300 has multiple bonds and lies outside this ring proof domain.

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

For the [November 25 source checkpoint](https://github.com/graviterra/stereolib/commit/febab3b4de8864518467311c21c23cd4774508a8),
the export reproduced all 4,617 maintained modules. The [strict chemical controls](validation/ring-chronology/LocalRuleCoverage.lean)
and [VS084 replay](validation/ring-chronology/OriginTwinVS084.lean) passed using the exported
fixtures and the existing development compilation. The focused Lean replays ran serially with
a 6 GiB aggregate memory limit and swap disabled. Both the [Lean spiro replay](validation/ring-chronology/OriginMetricSpiro.lean)
and the pinned Java replay reproduced R/S on the supplied geometry and S/R on reflection,
in public-distance/active-distance order.
The exported receipt generator also reproduced both deep-marked Centres receipts.
[Spiro replay](validation/ring-chronology/CentresOriginMetricSpiro.java) ·
[Receipt generator](validation/ring-chronology/generate_deep_marked_source.py) ·
[GitHub source checks](https://github.com/graviterra/stereolib/actions/runs/45768097529)

The [module inventory](source-modules.json) contains all 4,617 maintained Lean modules.
The original umbrella brings the package total to 4,618 Lean files. The validation drivers
are counted separately.
A universal chemical completeness theorem and full chemical approval remain open. See the [README](README.md) for
existing acyclic results, collaboration guidance and safe source checks.
