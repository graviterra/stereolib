import TetraStereo.OneCenter.LocalizedF2SuppliedLabelProbe
import TetraStereo.OneCenter.LocalizedRerootCarrierCache
import TetraStereo.OneCenter.LocalizedRuleMajorCarrierCache

set_option autoImplicit false












namespace TetraStereo.OneCenter.F2RuleMajorEvaluation

open TetraStereo.OneCenter
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.OneCenter.F2SuppliedLabelFixture
open TetraStereo.OneCenter.F2SuppliedLabelProbe
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRerootCarrierCache

def eventPath : System.FilePath := ".lake/build/f2-rulemajor-evaluation-events.log"

def event (message : String) : IO Unit := do
  let handle ← IO.FS.Handle.mk eventPath IO.FS.Mode.append
  handle.putStr (message ++ "\n")
  handle.flush

def orderingName : Ordering → String
  | .lt => "lt"
  | .eq => "eq"
  | .gt => "gt"

def referenceName : Option RS → String
  | none => "none"
  | some .R => "R"
  | some .S => "S"

def firstEntryDelta {α : Type} [DecidableEq α] :
    List (OfficialSparseEntry α) → List (OfficialSparseEntry α) →
      Option (List Nat × List Nat × α × α)
  | [], _ => none
  | _, [] => none
  | (leftAddress, leftValue) :: leftTail, (rightAddress, rightValue) :: rightTail =>
      if leftAddress != rightAddress || leftValue != rightValue then
        some (leftAddress, rightAddress, leftValue, rightValue)
      else firstEntryDelta leftTail rightTail

def firstLayersDelta {α : Type} [DecidableEq α] (sphere : Nat) :
    List (List (OfficialSparseEntry α)) → List (List (OfficialSparseEntry α)) →
      Option (Nat × (List Nat × List Nat × α × α))
  | [], _ => none
  | _, [] => none
  | leftLayer :: leftTail, rightLayer :: rightTail =>
      match firstEntryDelta leftLayer rightLayer with
      | some delta => some (sphere, delta)
      | none => firstLayersDelta (sphere + 1) leftTail rightTail

def stageSummary (label : String)
    (left right : input.LocalizedRerootCompoundRule4bcKey) : IO Unit := do
  let b := input.compareLocalizedRerootCompoundRule4bReadings left.readings right.readings
  let c := input.compareLocalizedRerootCompoundRule4cReadings left.readings right.readings
  let refsLeft := left.readings.map fun r => referenceName r.reference?
  let refsRight := right.readings.map fun r => referenceName r.reference?
  IO.println s!"{label}: refs={refsLeft}/{refsRight}; Rule4b={orderingName b}; Rule4c={orderingName c}"
  event s!"{label}: refs={refsLeft}/{refsRight}; Rule4b={orderingName b}; Rule4c={orderingName c}"

def compareLegacyToRuleMajor (side : String)
    (legacy : input.LocalizedRerootCompoundRule4bcKey)
    (major : input.LocalizedRerootCompoundRule4bcKey) : IO Unit := do
  match legacy.readings, major.readings with
  | [legacyReading], [majorReading] => do
      let bSame := decide (legacyReading.rule4bKey.descriptor = majorReading.rule4bKey.descriptor)
      let cSame := decide (legacyReading.rule4cKey.descriptor = majorReading.rule4cKey.descriptor)
      IO.println s!"{side}: single reading {referenceName legacyReading.reference?}; 4b descriptor preserved={bSame}; 4c descriptor preserved={cSame}"
      event s!"{side}: single reading {referenceName legacyReading.reference?}; 4b descriptor preserved={bSame}; 4c descriptor preserved={cSame}"
      if !bSame then
        IO.println s!"{side} Rule4b first delta legacy/RuleMajor={reprStr (firstLayersDelta 0 legacyReading.rule4bKey.descriptor majorReading.rule4bKey.descriptor)}"
      if !cSame then
        IO.println s!"{side} Rule4c first delta legacy/RuleMajor={reprStr (firstLayersDelta 0 legacyReading.rule4cKey.descriptor majorReading.rule4cKey.descriptor)}"
  | _, _ =>
      IO.println s!"{side}: reading counts differ or are not singleton (legacy={legacy.readings.length}, RuleMajor={major.readings.length}); stage descriptors were not paired"
      event s!"{side}: reading counts differ or are not singleton"

def runRoot12 : IO Unit := do
  IO.FS.writeFile eventPath "F2 root-12 supplied-reader RuleMajor diagnostic\n"
  IO.println "F2 supplied-reader actual RuleMajor diagnostic: target 12; ligand atoms 0 and 1"
  event "START materialize shared carrier"
  let started ← IO.monoNanosNow
  let cache := input.localizedRerootCarrierCache carrierFuel
  let size := cache.frames.length
  let elapsed := (← IO.monoNanosNow) - started
  IO.println s!"shared carrier frames={size}; materialization ms={elapsed / 1000000}"
  event s!"DONE carrier frames={size}; ms={elapsed / 1000000}"
  let view := suppliedView 12 target12
  let fuel := localizedOccurrenceRerootEvaluationFuel carrierFuel
  IO.println s!"shared supplied view; carrierFuel={carrierFuel}; stage fuel={fuel}"
  event s!"START standard localized Rule4bc pair"
  let legacyLeft := WithChildren.buildLocalizedRerootCompoundRule4bcKeyExec?
    input cache.readChildren target12 view buildFuel cursor12_0
  let legacyRight := WithChildren.buildLocalizedRerootCompoundRule4bcKeyExec?
    input cache.readChildren target12 view buildFuel cursor12_1
  event s!"DONE standard localized Rule4bc pair: some={legacyLeft.isSome}/{legacyRight.isSome}"
  event "START actual RuleMajor CompoundRule45 pair"
  let majorLeft := cache.actualRuleMajorCompound45? target12 view fuel cursor12_0
  let majorRight := cache.actualRuleMajorCompound45? target12 view fuel cursor12_1
  event s!"DONE actual RuleMajor CompoundRule45 pair: some={majorLeft.isSome}/{majorRight.isSome}"
  match legacyLeft, legacyRight, majorLeft, majorRight with
  | some legacyLeft, some legacyRight, some majorLeft, some majorRight => do
      let priorOrder := input.compareLocalizedRerootCompoundRule4bcKeys
        majorLeft.prior majorRight.prior
      let through5 := input.compareLocalizedRerootCompoundThroughRule5 majorLeft majorRight
      stageSummary "standard localized Rule4bc" legacyLeft legacyRight
      stageSummary "actual RuleMajor Rule4bc prior" majorLeft.prior majorRight.prior
      IO.println s!"RuleMajor prior comparator={orderingName priorOrder}; throughRule5 ordering={orderingName through5.ordering}; pseudo={through5.pseudo}"
      event s!"RuleMajor prior comparator={orderingName priorOrder}; throughRule5 ordering={orderingName through5.ordering}; pseudo={through5.pseudo}"
      compareLegacyToRuleMajor "ligand 0" legacyLeft majorLeft.prior
      compareLegacyToRuleMajor "ligand 1" legacyRight majorRight.prior
      IO.println s!"Rule5 readings built: left={majorLeft.rule5Readings.length}; right={majorRight.rule5Readings.length}"
      event s!"Rule5 readings built: left={majorLeft.rule5Readings.length}; right={majorRight.rule5Readings.length}"
  | _, _, _, _ =>
      IO.println s!"Some builder failed: legacy={legacyLeft.isSome}/{legacyRight.isSome}; RuleMajor={majorLeft.isSome}/{majorRight.isSome}"
      event "At least one exact builder returned none"

#eval runRoot12

end TetraStereo.OneCenter.F2RuleMajorEvaluation
