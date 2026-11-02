import TetraStereo.OneCenter.LocalizedF2SuppliedLabelProbe
import TetraStereo.OneCenter.LocalizedRerootCarrierCache

set_option autoImplicit false

namespace TetraStereo.OneCenter.F2SuppliedLabelEvaluation

open TetraStereo.OneCenter
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.OneCenter.F2SuppliedLabelFixture
open TetraStereo.OneCenter.F2SuppliedLabelProbe



def eventPath : System.FilePath := ".lake/build/f2-supplied-label-evaluation-events.log"

def event (message : String) : IO Unit := do
  let handle ← IO.FS.Handle.mk eventPath IO.FS.Mode.append
  handle.putStr (message ++ "\n")
  handle.flush

/-- Force one pure optional key build and persist both timing boundaries. -/
def timed {α : Type} (name : String) (compute : Unit → Option α) : IO (Option α) := do
  event s!"START {name}"
  let started ← IO.monoNanosNow
  let result := compute ()
  let status := match result with
    | none => "none"
    | some _ => "some"
  let ended ← IO.monoNanosNow
  let elapsed := (ended - started) / 1000000
  event s!"DONE {name}: {status}; {elapsed} ms"
  IO.println s!"{name}: {status}, {elapsed} ms"
  pure result

/-- Find the first aligned sparse entry at which two projections differ. Addresses are retained
on both sides so any divergence in the positional coordinate itself is visible. -/
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

def orderingName : Ordering → String
  | .lt => "lt"
  | .eq => "eq"
  | .gt => "gt"

def refName? : Option RS → String
  | none => "none"
  | some .R => "R"
  | some .S => "S"

def firstNatIndex (index : Nat) : List Nat → List Nat → Option Nat
  | [], _ => none
  | _, [] => none
  | left :: leftTail, right :: rightTail =>
      if left != right then some index else firstNatIndex (index + 1) leftTail rightTail

theorem throughRule5_strictPrior_pseudo_false
    (left right : input.LocalizedRerootCompoundRule45Key)
    (strict : input.compareLocalizedRerootCompoundRule4bcKeys
      left.prior right.prior ≠ Ordering.eq) :
    input.compareLocalizedRerootCompoundThroughRule5 left right =
      { ordering := input.compareLocalizedRerootCompoundRule4bcKeys left.prior right.prior
        pseudo := false } := by
  unfold CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundThroughRule5
  simp [strict]

assert_kernel_only TetraStereo.OneCenter.F2SuppliedLabelEvaluation.throughRule5_strictPrior_pseudo_false

/-- Show the first comparator component after an exact Rule-4a tie using the already assembled
compound keys; no key construction or label read is repeated. -/
def reportCompoundDifference
    (left right : input.LocalizedRerootCompoundRule4bcKey) : IO Unit := do
  let countOrder := compare left.referenceCountPriority right.referenceCountPriority
  let rule4bOrder := input.compareLocalizedRerootCompoundRule4bReadings
    left.readings right.readings
  let rule4cOrder := input.compareLocalizedRerootCompoundRule4cReadings
    left.readings right.readings
  event s!"post-Rule4a fields: reference-count={orderingName countOrder}; Rule4b={orderingName rule4bOrder}; Rule4c={orderingName rule4cOrder}"
  IO.println s!"post-Rule4a fields: reference-count={orderingName countOrder}; Rule4b={orderingName rule4bOrder}; Rule4c={orderingName rule4cOrder}"
  if countOrder != .eq then
    event s!"DECISIVE Rule4b reference-count priority: left={left.referenceCountPriority}, right={right.referenceCountPriority}"
    IO.println s!"DECISIVE Rule4b reference-count priority: left={left.referenceCountPriority}, right={right.referenceCountPriority}"
  else if rule4bOrder != .eq then
    match left.readings, right.readings with
    | leftReading :: _, rightReading :: _ => do
        let readingOrder := input.compareLocalizedRerootRule4bcReadingsByRule4b
          leftReading rightReading
        let delta := firstLayersDelta 0 leftReading.rule4bKey.descriptor
          rightReading.rule4bKey.descriptor
        let message := s!"DECISIVE Rule4b reading; selected refs={refName? leftReading.reference?}/{refName? rightReading.reference?}; cmp={orderingName readingOrder}; first sparse sphere/address/vector delta={reprStr delta}"
        event message
        IO.println message
    | _, _ =>
        event "DECISIVE Rule4b reading-list length/order difference; no aligned reading pair"
        IO.println "DECISIVE Rule4b reading-list length/order difference; no aligned reading pair"
  else if rule4cOrder != .eq then
    match left.readings, right.readings with
    | leftReading :: _, rightReading :: _ => do
        let rule4bMessage := s!"Rule4b descriptor projections left={reprStr leftReading.rule4bKey.descriptor}; right={reprStr rightReading.rule4bKey.descriptor}"
        event rule4bMessage
        IO.println rule4bMessage
        let delta := firstLayersDelta 0 leftReading.rule4cKey.descriptor
          rightReading.rule4cKey.descriptor
        match delta with
        | some (sphere, (leftAddress, rightAddress, leftVector, rightVector)) => do
            let component := firstNatIndex 0 leftVector rightVector
            let message := s!"DECISIVE Rule4c reading; selected refs={refName? leftReading.reference?}/{refName? rightReading.reference?}; sphere={sphere}; addresses={reprStr leftAddress}/{reprStr rightAddress}; vectors={reprStr leftVector}/{reprStr rightVector}; first differing vector index={reprStr component}"
            event message
            IO.println message
        | none =>
            event s!"Rule4c reading comparator is {orderingName rule4cOrder}, but no aligned sparse entry was found"
            IO.println s!"Rule4c reading comparator is {orderingName rule4cOrder}, but no aligned sparse entry was found"
    | _, _ =>
        event "DECISIVE Rule4c reading-list length/order difference; no aligned reading pair"
        IO.println "DECISIVE Rule4c reading-list length/order difference; no aligned reading pair"
  else
    event "all Rule4bc comparator components tie"
    IO.println "all Rule4bc comparator components tie"

/-- Exact first field of a strict Rule-4a cumulative-key comparison, with the raw sparse address
when the first differing row is aligned in the two projections. -/
def reportRule4aDifference
    (left right : input.LocalizedRerootCumulativeRule45Key) : IO Unit := do
  let leftCon := left.constitutional
  let rightCon := right.constitutional
  let atomic := OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
    leftCon.rule1a rightCon.rule1a
  let duplicate := OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b
    leftCon.rule1b rightCon.rule1b
  let isotope := OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
    leftCon.rule2 rightCon.rule2
  if atomic != .eq then
    event s!"DECISIVE Rule1a; cmp={orderingName atomic}; address/value={reprStr (firstLayersDelta 0 leftCon.rule1a rightCon.rule1a)}"
    IO.println s!"DECISIVE Rule1a; cmp={orderingName atomic}; address/value={reprStr (firstLayersDelta 0 leftCon.rule1a rightCon.rule1a)}"
  else if duplicate != .eq then
    event s!"DECISIVE Rule1b; cmp={orderingName duplicate}; address/value={reprStr (firstLayersDelta 0 leftCon.rule1b rightCon.rule1b)}"
    IO.println s!"DECISIVE Rule1b; cmp={orderingName duplicate}; address/value={reprStr (firstLayersDelta 0 leftCon.rule1b rightCon.rule1b)}"
  else if isotope != .eq then
    event s!"DECISIVE Rule2; cmp={orderingName isotope}; address/value={reprStr (firstLayersDelta 0 leftCon.rule2 rightCon.rule2)}"
    IO.println s!"DECISIVE Rule2; cmp={orderingName isotope}; address/value={reprStr (firstLayersDelta 0 leftCon.rule2 rightCon.rule2)}"
  else
    let descriptor := OfficialRuleMajorKey.compareSparseLayers
      compareLocalizedCumulativeRule45Priority left.descriptor right.descriptor
    event s!"DECISIVE Rule4a descriptor; cmp={orderingName descriptor}; address/value={reprStr (firstLayersDelta 0 left.descriptor right.descriptor)}"
    IO.println s!"DECISIVE Rule4a descriptor; cmp={orderingName descriptor}; address/value={reprStr (firstLayersDelta 0 left.descriptor right.descriptor)}"

/-- Timed construction of the exact Rule-4b/4c reading records when Rule 4a ties. -/
def timedReading {carrierFuel : Nat}
    (root : Nat)
    (cache : input.LocalizedRerootCarrierCache carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (n : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (reference : Option RS) : IO (Option input.LocalizedRerootRule4bcReading) := do
  match reference with
  | none =>
      let rule4bKey ← timed s!"root {root} Rule4b(no reference: Rule4a stage)" fun _ =>
        WithChildren.buildLocalizedRerootCumulativeRule45KeyExec?
          input cache.readChildren .rule4a target view n cursor
      match rule4bKey with
      | none => pure none
      | some rule4bKey => do
          let rule4cKey ← timed s!"root {root} Rule4c(no reference)" fun _ =>
            WithChildren.buildLocalizedRerootCumulativeRule45KeyExec?
              input cache.readChildren .rule4cNoReference target view n cursor
          pure (rule4cKey.map fun rule4cKey =>
            { reference? := none, rule4bKey := rule4bKey, rule4cKey := rule4cKey })
  | some ref =>
      let refName := match ref with | .R => "R" | .S => "S"
      let rule4bKey ← timed s!"root {root} Rule4b(reference {refName})" fun _ =>
        WithChildren.buildLocalizedRerootCumulativeRule45KeyExec?
          input cache.readChildren (.rule4b ref) target view n cursor
      match rule4bKey with
      | none => pure none
      | some rule4bKey => do
          let rule4cKey ← timed s!"root {root} Rule4c(reference {refName})" fun _ =>
            WithChildren.buildLocalizedRerootCumulativeRule45KeyExec?
              input cache.readChildren (.rule4c ref) target view n cursor
          pure (rule4cKey.map fun rule4cKey =>
            { reference? := some ref, rule4bKey := rule4bKey, rule4cKey := rule4cKey })

def timedReadings {carrierFuel : Nat}
    (root : Nat)
    (cache : input.LocalizedRerootCarrierCache carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (n : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    List (Option RS) → IO (Option (List input.LocalizedRerootRule4bcReading))
  | [] => pure (some [])
  | reference :: references => do
      let reading ← timedReading root cache target view n cursor reference
      match reading with
      | none => pure none
      | some reading => do
          let tail ← timedReadings root cache target view n cursor references
          pure (tail.map fun tail => reading :: tail)

def timedActualCompound4bc {carrierFuel : Nat}
    (root : Nat)
    (cache : input.LocalizedRerootCarrierCache carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    IO (Option input.LocalizedRerootCompoundRule4bcKey) := do
  let view := suppliedView root target
  timed s!"root {root} ligand address {reprStr cursor.occurrence.1.address} exact cached CompoundRule4bc builder" fun _ =>
    WithChildren.buildLocalizedRerootCompoundRule4bcKeyExec?
      input cache.readChildren target view buildFuel cursor

def timedCompound4bc {carrierFuel : Nat}
    (root : Nat)
    (cache : input.LocalizedRerootCarrierCache carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (rule4aKey : input.LocalizedRerootCumulativeRule45Key) :
    IO (Option input.LocalizedRerootCompoundRule4bcKey) := do
  let view := suppliedView root target
  let references := localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels
  let alternatives := localizedRule4bcReferenceAlternatives references
  event s!"root {root} reference selection: {references.length} reference(s), {alternatives.length} reading(s)"
  IO.println s!"root {root} selected {references.length} reference(s), {alternatives.length} reading(s)"
  let readings ← timedReadings root cache target view buildFuel cursor alternatives
  pure (readings.map fun readings =>
    { rule4aKey := rule4aKey
      references := references
      referenceCountPriority := constitutionalRule4bReferenceCountPriority references
      readings := readings })

/-- Root-12 target comparator. Start with the Rule-4a comparator keys; if they differ, existing
strict-prior theorems transfer that exact ordering to compound Rule 4bc and through Rule 5, so no
later reading build is needed. Ties continue through the existing actual compound builders. -/
def runRoot12 : IO Unit := do
  IO.FS.writeFile eventPath "F2 root-12 supplied-label comparator run\n"
  event "target atom 12; ligand atoms 0/1; cursors use accepted root occurrences"
  IO.println s!"F2 supplied-label probe: target atom 12, source ligand atoms 0 and 1"
  event "START materialize localized occurrence carrier once"
  let cacheStarted ← IO.monoNanosNow
  let cache := input.localizedRerootCarrierCache carrierFuel
  let carrierLength := cache.frames.length
  let cacheEnded ← IO.monoNanosNow
  let cacheMs := (cacheEnded - cacheStarted) / 1000000
  event s!"DONE materialize localized occurrence carrier: {carrierLength} frames; {cacheMs} ms"
  IO.println s!"materialized shared localized occurrence carrier: {carrierLength} frames in {cacheMs} ms"
  IO.println s!"left cursor address={reprStr cursor12_0.occurrence.1.address}; right cursor address={reprStr cursor12_1.occurrence.1.address}"
  let view := suppliedView 12 target12
  let left4a ← timed "root 12 ligand 0 Rule4a key" fun _ =>
    WithChildren.buildLocalizedRerootCumulativeRule45KeyExec?
      input cache.readChildren .rule4a target12 view buildFuel cursor12_0
  let right4a ← timed "root 12 ligand 1 Rule4a key" fun _ =>
    WithChildren.buildLocalizedRerootCumulativeRule45KeyExec?
      input cache.readChildren .rule4a target12 view buildFuel cursor12_1
  match left4a, right4a with
  | some left4a, some right4a => do
      let priorOrder := input.compareLocalizedRerootCumulativeRule45Keys left4a right4a
      event s!"Rule4a cumulative comparator: {orderingName priorOrder}"
      IO.println s!"Rule4a cumulative comparator: {orderingName priorOrder}"
      if priorOrder != .eq then
        reportRule4aDifference left4a right4a
        event s!"through Rule4bc comparator={orderingName priorOrder}; through Rule5 ordering={orderingName priorOrder} by strict-prior kernel lemmas"
        IO.println s!"through Rule4bc comparator={orderingName priorOrder}; through Rule5 ordering={orderingName priorOrder} by strict-prior kernel lemmas"
      else do
        let left ← timedCompound4bc 12 cache target12 cursor12_0 left4a
        let right ← timedCompound4bc 12 cache target12 cursor12_1 right4a
        match left, right with
        | some stagedLeft, some stagedRight => do
            let stagedOrder := input.compareLocalizedRerootCompoundRule4bcKeys stagedLeft stagedRight
            let stagedName := orderingName stagedOrder
            event s!"timed staged assembly comparator: {stagedName}"
            IO.println s!"timed staged assembly comparator: {stagedName}"
            let exactLeft ← timedActualCompound4bc 12 cache target12 cursor12_0
            let exactRight ← timedActualCompound4bc 12 cache target12 cursor12_1
            match exactLeft, exactRight with
            | some left, some right => do
                let order := input.compareLocalizedRerootCompoundRule4bcKeys left right
                let name := orderingName order
                event s!"exact cached current CompoundRule4bc comparator: {name}; staged/exact agree={stagedOrder == order}"
                IO.println s!"exact cached current CompoundRule4bc comparator: {name}; staged/exact agree={stagedOrder == order}"
                reportCompoundDifference left right
                if order != .eq then
                  let message := s!"through Rule5 ordering={name}, pseudo=false by strict-prior kernel theorem; Rule5 keys were not needed"
                  event message
                  IO.println message
            | none, _ => event "left exact cached compound builder returned none"
            | _, none => event "right exact cached compound builder returned none"
        | none, _ => event "left staged compound assembly returned none"
        | _, none => event "right staged compound assembly returned none"
  | none, _ => event "left Rule4a key returned none"
  | _, none => event "right Rule4a key returned none"

#eval runRoot12

end TetraStereo.OneCenter.F2SuppliedLabelEvaluation
