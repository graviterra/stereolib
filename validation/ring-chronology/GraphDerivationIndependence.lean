import TetraStereo.Engine.RingGraphReport
import ImportGraph.Imports.RequiredModules

/-! The path and report existence proofs are required to remain independent of the
public global store. The final agreement theorem exercises the dependency traversal
on a proof that does use both sides. -/

open Lean Elab Command
open TetraStereo.Engine

run_cmd do
  let joined ← liftCoreM (``RingGraphReport.whole_report).transitivelyUsedConstants
  for required in [``RingGraphReport.unique_derived_report,``RingGraphReport.path_derivation,
      ``RingGraphReport.report_iff,``RingGroupedReport.forAtoms?] do
    unless joined.contains required do throwError "Missing report agreement dependency {required}"
  let forbidden := [``RingGroupedPublication.state, ``RingGroupedPublication.complete,
    ``RingGroupedPublication.molecular_iff, ``RingGroupedPublication.state_eq,
    ``RingGroupedPublication.ready, ``RingGroupedPublication.publish?,
    ``RingGroupedReport.forAtoms?, ``RingActiveDistanceSchedule.frozen,
    ``RingActiveDistanceSchedule.evaluate, ``RingActiveDistanceSchedule.table,
    ``RingGraphReport.report_iff, ``RingGraphReport.atPath_exact]
  let names := [``RingGraphReport.path_derivation, ``RingGraphReport.unique_derived_report]
  for n in names do
    let deps ← liftCoreM n.transitivelyUsedConstants
    let found := forbidden.filter deps.contains
    unless found.isEmpty do throwError "{n} depends on {found}"
    logInfo m!"{n}: checked transitive declaration dependencies against {forbidden.length} evaluator and agreement declarations"
