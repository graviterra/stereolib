import TetraStereo.OneCenter.LocalizedRule3CumulatedChain
import TetraStereo.OneCenter.LocalizedRule3PhysicalTopologyExecutable
import TetraStereo.OneCenter.LocalizedRerootChildrenExecutable

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-- Constructive decision for physical real-atom continuation. -/
instance axisContinuationDecidable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor child : input.LocalizedRerootCursor carrierFuel) :
    Decidable (input.LocalizedRule3AxisContinuation cursor child) := by
  unfold LocalizedRule3AxisContinuation
  split <;> infer_instance

/-- Constructive decision includes zero-copy ring closures, preserving provenance. -/
instance axisPhysicalContinuationDecidable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor child : input.LocalizedRerootCursor carrierFuel) :
    Decidable (input.LocalizedRule3AxisPhysicalContinuation cursor child) := by
  unfold LocalizedRule3AxisPhysicalContinuation LocalizedRule3PhysicalReferenceProvenance
  split <;> split <;> infer_instance

def localizedRule3AxisContinuationCursorsExec
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (children : List (input.LocalizedRerootCursor carrierFuel)) :
    List (input.LocalizedRerootCursor carrierFuel) := by
  exact children.filter fun child => decide (input.LocalizedRule3AxisContinuation cursor child)

theorem localizedRule3AxisContinuationCursorsExec_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (children : List (input.LocalizedRerootCursor carrierFuel)) :
    input.localizedRule3AxisContinuationCursorsExec cursor children = input.localizedRule3AxisContinuationCursors cursor children := by
  unfold localizedRule3AxisContinuationCursorsExec localizedRule3AxisContinuationCursors
  congr 1
  funext child
  simp only [decide_eq_decide]

def localizedRule3AxisContinuationCursorsExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    Option (List (input.LocalizedRerootCursor carrierFuel)) := do
  let children ← input.executableLocalizedRerootChildren? cursor
  some (input.localizedRule3AxisContinuationCursorsExec cursor children)

theorem localizedRule3AxisContinuationCursorsExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    input.localizedRule3AxisContinuationCursorsExec? cursor = input.localizedRule3AxisContinuationCursors? cursor := by
  simp only [localizedRule3AxisContinuationCursorsExec?, localizedRule3AxisContinuationCursors?,
    localizedRerootChildren?_eq_some_executable, executableLocalizedRerootChildren?_eq_some, localizedRule3AxisContinuationCursorsExec_eq_original]

def localizedRule3AxisPhysicalContinuationCursorsExec
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (children : List (input.LocalizedRerootCursor carrierFuel)) :
    List (input.LocalizedRerootCursor carrierFuel) := by
  exact children.filter fun child =>
    decide (input.LocalizedRule3AxisPhysicalContinuation cursor child)

theorem localizedRule3AxisPhysicalContinuationCursorsExec_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (children : List (input.LocalizedRerootCursor carrierFuel)) :
    input.localizedRule3AxisPhysicalContinuationCursorsExec cursor children = input.localizedRule3AxisPhysicalContinuationCursors cursor children := by
  unfold localizedRule3AxisPhysicalContinuationCursorsExec localizedRule3AxisPhysicalContinuationCursors
  congr 1
  funext child
  simp only [decide_eq_decide]

def localizedRule3AxisPhysicalContinuationCursorsExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    Option (List (input.LocalizedRerootCursor carrierFuel)) := do
  let children ← input.executableLocalizedRerootChildren? cursor
  some (input.localizedRule3AxisPhysicalContinuationCursorsExec cursor children)

theorem localizedRule3AxisPhysicalContinuationCursorsExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    input.localizedRule3AxisPhysicalContinuationCursorsExec? cursor = input.localizedRule3AxisPhysicalContinuationCursors? cursor := by
  simp only [localizedRule3AxisPhysicalContinuationCursorsExec?, localizedRule3AxisPhysicalContinuationCursors?,
    localizedRerootChildren?_eq_some_executable, executableLocalizedRerootChildren?_eq_some, localizedRule3AxisPhysicalContinuationCursorsExec_eq_original]

def localizedRule3AxisTopologyExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    Option (input.LocalizedRule3AxisTopology carrierFuel) := do
  let continuations ← input.localizedRule3AxisPhysicalContinuationCursorsExec? cursor
  match continuations with
  | [] => some .terminal
  | [next] =>
      match next.occurrence.1.node.provenance with
      | .realAtom => some (.linear next)
      | .ringDuplicate _ => some (.ringClosure next)
      | .multipleBondDuplicate _ | .placeholder _ _ => none
  | first :: second :: rest => some (.branched first second rest)

theorem localizedRule3AxisTopologyExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    input.localizedRule3AxisTopologyExec? cursor = input.localizedRule3AxisTopology? cursor := by
  simp only [localizedRule3AxisTopologyExec?, localizedRule3AxisTopology?,
    localizedRule3AxisPhysicalContinuationCursorsExec?_eq_original]
  rfl

def walkLocalizedRule3CumulatedAxisExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} :
    Nat → input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel))
  | 0, cursor => do
      let topology ← input.localizedRule3AxisTopologyExec? cursor
      match topology with
      | .terminal => some [cursor]
      | .linear _ | .ringClosure _ | .branched _ _ _ => none
  | fuel + 1, cursor => do
      let topology ← input.localizedRule3AxisTopologyExec? cursor
      match topology with
      | .terminal => some [cursor]
      | .linear next => do
          let tail ← input.walkLocalizedRule3CumulatedAxisExec? fuel next
          some (cursor :: tail)
      | .ringClosure _ | .branched _ _ _ => none

theorem walkLocalizedRule3CumulatedAxisExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (traversalFuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    input.walkLocalizedRule3CumulatedAxisExec? traversalFuel cursor = input.walkLocalizedRule3CumulatedAxis? traversalFuel cursor := by
  induction traversalFuel generalizing cursor with
  | zero => simp only [walkLocalizedRule3CumulatedAxisExec?, walkLocalizedRule3CumulatedAxis?, localizedRule3AxisTopologyExec?_eq_original]
            rfl
  | succ fuel ih =>
      simp only [walkLocalizedRule3CumulatedAxisExec?, walkLocalizedRule3CumulatedAxis?, localizedRule3AxisTopologyExec?_eq_original, ih]
      rfl

def localizedRule3CumulatedAxisEntryExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    Option (input.LocalizedRule3CumulatedAxisEntry carrierFuel) := do
  let initial ← input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence
  let topology ← input.localizedRule3AxisTopologyExec? initial.leftCursor
  match topology with
  | .terminal => some (.terminalStart initial)
  | .linear previousAxis => some (.internal initial previousAxis)
  | .ringClosure closure => some (.ringClosure initial closure)
  | .branched first second rest => some (.branched initial first second rest)

theorem localizedRule3CumulatedAxisEntryExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    input.localizedRule3CumulatedAxisEntryExec? occurrence = input.localizedRule3CumulatedAxisEntry? occurrence := by
  simp only [localizedRule3CumulatedAxisEntryExec?, localizedRule3CumulatedAxisEntry?,
    localizedRule3PhysicalEndpointCursorFrameExec?_eq_original, localizedRule3AxisTopologyExec?_eq_original]
  rfl

def localizedRule3CumulatedEndpointCursorFrameExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (traversalFuel : Nat)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    Option (input.LocalizedRule3CumulatedEndpointCursorFrame carrierFuel) := do
  let entry ← input.localizedRule3CumulatedAxisEntryExec? occurrence
  match entry with
  | .internal _ _ | .ringClosure _ _ | .branched _ _ _ _ => none
  | .terminalStart initial =>
      let rightward ← input.walkLocalizedRule3CumulatedAxisExec?
        traversalFuel initial.rightCursor
      match (initial.leftCursor :: rightward).reverse with
      | rightCursor :: rightPartnerCursor :: _rest => do
          let rightPartner ← rightPartnerCursor.occurrence.1.node.current?
          let right ← rightCursor.occurrence.1.node.current?
          some { initial
                 rightward
                 rightPartnerCursor
                 rightCursor
                 rightPartner
                 right }
      | _ => none

theorem localizedRule3CumulatedEndpointCursorFrameExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (traversalFuel : Nat) (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    input.localizedRule3CumulatedEndpointCursorFrameExec? traversalFuel occurrence = input.localizedRule3CumulatedEndpointCursorFrame? traversalFuel occurrence := by
  simp only [localizedRule3CumulatedEndpointCursorFrameExec?, localizedRule3CumulatedEndpointCursorFrame?,
    localizedRule3CumulatedAxisEntryExec?_eq_original, walkLocalizedRule3CumulatedAxisExec?_eq_original]
  rfl

def localizedRule3OddCumuleneEndpointCursorFrameExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (traversalFuel : Nat)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    Option (input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel) := do
  let initial ← input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence
  let leftTopology ← input.localizedRule3AxisTopologyExec? initial.leftCursor
  match leftTopology with
  | .terminal =>
      let rightward ← input.walkLocalizedRule3CumulatedAxisExec?
        traversalFuel initial.rightCursor
      match rightward.reverse with
      | rightCursor :: rightPartnerCursor :: _rest =>
          if _admissible : 1 < rightward.length ∧ Odd rightward.length then do
            let rightPartner ← rightPartnerCursor.occurrence.1.node.current?
            let right ← rightCursor.occurrence.1.node.current?
            some { initial
                   rightward
                   rightPartnerCursor
                   rightCursor
                   rightPartner
                   right }
          else none
      | _ => none
  | .linear _ | .ringClosure _ | .branched _ _ _ => none

theorem localizedRule3OddCumuleneEndpointCursorFrameExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (traversalFuel : Nat) (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    input.localizedRule3OddCumuleneEndpointCursorFrameExec? traversalFuel occurrence = input.localizedRule3OddCumuleneEndpointCursorFrame? traversalFuel occurrence := by
  simp only [localizedRule3OddCumuleneEndpointCursorFrameExec?, localizedRule3OddCumuleneEndpointCursorFrame?,
    localizedRule3PhysicalEndpointCursorFrameExec?_eq_original, localizedRule3AxisTopologyExec?_eq_original, walkLocalizedRule3CumulatedAxisExec?_eq_original]
  rfl

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
