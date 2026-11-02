import TetraStereo.OneCenter.CIPRule3CoupledTopologyAffineInvariance
import TetraStereo.OneCenter.LocalizedRule3CumulatedChain

/-!
# Coordinate naturality of localized Rule-3 cumulated topology

This module proves that exact parent recovery, oriented endpoint cursors, physical continuation
filtering, terminal/linear/ring/branch classification, fuel-bounded axis walking, and ordinary or
odd cumulene endpoint-frame construction commute with arbitrary coordinate transport. Parity,
branching, ring closure, and every refusal outcome are consequently properties of the molecular
occurrence topology rather than of its coordinate representation.
-/

set_option autoImplicit false

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

private theorem localizedCIPOccurrenceFrameMap_injective
    {input : CertifiedLocalizedCIPInput}
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    Function.Injective (fun frame : input.LocalizedCIPOccurrenceFrame =>
      frame.mapSpatialPoints mapPoint) := by
  intro left right equal
  cases left
  cases right
  simp only [LocalizedCIPOccurrenceFrame.mapSpatialPoints] at equal
  simp_all

@[simp] theorem localizedRule3CarrierParentFrame?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).localizedRule3CarrierParentFrame?
        (occurrence.mapSpatialPoints mapPoint) =
      (input.localizedRule3CarrierParentFrame? occurrence).map
        (fun frame => frame.mapSpatialPoints mapPoint) := by
  unfold localizedRule3CarrierParentFrame?
  have parentFramesEq := localizedCarrierParentFrames_mapSpatialPoints
    input mapPoint (fuel := fuel) occurrence.1
  have occurrenceFrameEq :
      (occurrence.mapSpatialPoints mapPoint).1 =
        occurrence.1.mapSpatialPoints mapPoint := rfl
  rw [occurrenceFrameEq]
  rw [parentFramesEq]
  cases framesEq : input.localizedCarrierParentFrames (fuel := fuel) occurrence.1 with
  | nil => rfl
  | cons frame rest =>
      cases rest <;> rfl

@[simp] theorem localizedRule3CarrierParentOccurrence?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).localizedRule3CarrierParentOccurrence?
        (occurrence.mapSpatialPoints mapPoint) =
      (input.localizedRule3CarrierParentOccurrence? occurrence).map
        (fun parent => parent.mapSpatialPoints mapPoint) := by
  classical
  unfold localizedRule3CarrierParentOccurrence?
  rw [localizedRule3CarrierParentFrame?_mapSpatialPoints]
  cases parentEq : input.localizedRule3CarrierParentFrame? occurrence with
  | none => rfl
  | some parent =>
      simp only [Option.map_some]
      have presentIff :
          parent.mapSpatialPoints mapPoint ∈
              (input.mapSpatialPoints mapPoint).localizedOccurrences fuel ↔
            parent ∈ input.localizedOccurrences fuel := by
        rw [localizedOccurrences_mapSpatialPoints]
        exact List.mem_map_of_injective
          (localizedCIPOccurrenceFrameMap_injective mapPoint)
      by_cases present : parent ∈ input.localizedOccurrences fuel
      · have mappedPresent := presentIff.mpr present
        rw [dif_pos mappedPresent, dif_pos present]
        rfl
      · have notMapped : parent.mapSpatialPoints mapPoint ∉
            (input.mapSpatialPoints mapPoint).localizedOccurrences fuel := by
          exact fun mappedPresent => present (presentIff.mp mappedPresent)
        rw [dif_neg notMapped, dif_neg present]
        rfl

def LocalizedRule3PhysicalEndpointCursorFrame.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (frame : input.LocalizedRule3PhysicalEndpointCursorFrame fuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedRule3PhysicalEndpointCursorFrame fuel :=
  { left := frame.left
    right := frame.right
    leftCursor := frame.leftCursor.mapSpatialPoints mapPoint
    rightCursor := frame.rightCursor.mapSpatialPoints mapPoint }

@[simp] theorem localizedRule3PhysicalEndpointCursorFrame?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).localizedRule3PhysicalEndpointCursorFrame?
        (occurrence.mapSpatialPoints mapPoint) =
      (input.localizedRule3PhysicalEndpointCursorFrame? occurrence).map
        (fun frame => frame.mapSpatialPoints mapPoint) := by
  unfold localizedRule3PhysicalEndpointCursorFrame?
  rw [localizedRule3CarrierParentOccurrence?_mapSpatialPoints]
  simp only [LocalizedCIPOccurrence.mapSpatialPoints,
    LocalizedCIPOccurrenceFrame.mapSpatialPoints]
  by_cases real : occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom
  · have mappedReal : (occurrence.mapSpatialPoints mapPoint).1.node.provenance =
        OfficialCIPNodeProvenance.realAtom := real
    simp only [if_pos real]
    cases currentEq : occurrence.1.node.current? with
    | none => rfl
    | some current =>
        cases parentEq : occurrence.1.node.parent? with
        | none => rfl
        | some parent =>
            by_cases doubleBond : input.moleculeGraph.bond parent current = 2
            · simp only [moleculeGraph_mapSpatialPoints, doubleBond, if_true]
              cases carrierEq : input.localizedRule3CarrierParentOccurrence? occurrence with
              | none => rfl
              | some parentOccurrence =>
                  simp only [Option.map_some]
                  by_cases parentAtom : parentOccurrence.1.node.current? = some parent
                  · simp [parentAtom,
                      LocalizedRule3PhysicalEndpointCursorFrame.mapSpatialPoints,
                      LocalizedRerootCursor.mapSpatialPoints]
                    constructor
                    · constructor <;> apply Subtype.ext <;> rfl
                    · constructor <;> apply Subtype.ext <;> rfl
                  · simp [parentAtom]
            · simp [moleculeGraph_mapSpatialPoints, doubleBond]
  · have notMappedReal :
        (occurrence.mapSpatialPoints mapPoint).1.node.provenance ≠
          OfficialCIPNodeProvenance.realAtom := real
    simp [real]

def LocalizedRule3AxisTopology.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (topology : input.LocalizedRule3AxisTopology fuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedRule3AxisTopology fuel :=
  match topology with
  | .terminal => .terminal
  | .linear next => .linear (next.mapSpatialPoints mapPoint)
  | .ringClosure closure => .ringClosure (closure.mapSpatialPoints mapPoint)
  | .branched first second rest =>
      .branched (first.mapSpatialPoints mapPoint) (second.mapSpatialPoints mapPoint)
        (rest.map fun cursor => cursor.mapSpatialPoints mapPoint)

@[simp] theorem localizedRule3AxisContinuation_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor child : input.LocalizedRerootCursor fuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedRule3AxisContinuation
        (cursor.mapSpatialPoints mapPoint) (child.mapSpatialPoints mapPoint) ↔
      input.LocalizedRule3AxisContinuation cursor child := by
  simp [LocalizedRule3AxisContinuation,
    CertifiedLocalizedCIPInput.mapSpatialPoints,
    CertifiedAuthoritativeChemicalInput.mapSpatialPoints,
    AuthoritativeChemicalInput.mapSpatialPoints,
    CertifiedLocalizedCIPInput.moleculeGraph,
    LocalizedRerootCursor.mapSpatialPoints,
    LocalizedCIPOccurrence.mapSpatialPoints,
    LocalizedCIPOccurrenceFrame.mapSpatialPoints]
  intro cursorReal childReal
  cases currentEq : cursor.occurrence.1.node.current? <;>
    cases nextEq : child.occurrence.1.node.current? <;>
    simp

@[simp] theorem localizedRule3AxisPhysicalContinuation_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor child : input.LocalizedRerootCursor fuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedRule3AxisPhysicalContinuation
        (cursor.mapSpatialPoints mapPoint) (child.mapSpatialPoints mapPoint) ↔
      input.LocalizedRule3AxisPhysicalContinuation cursor child := by
  simp [LocalizedRule3AxisPhysicalContinuation,
    CertifiedLocalizedCIPInput.mapSpatialPoints,
    CertifiedAuthoritativeChemicalInput.mapSpatialPoints,
    AuthoritativeChemicalInput.mapSpatialPoints,
    CertifiedLocalizedCIPInput.moleculeGraph,
    LocalizedRerootCursor.mapSpatialPoints,
    LocalizedCIPOccurrence.mapSpatialPoints,
    LocalizedCIPOccurrenceFrame.mapSpatialPoints]
  intro cursorReal childPhysical
  cases currentEq : cursor.occurrence.1.node.current? <;>
    cases nextEq : child.occurrence.1.node.current? <;>
    simp

private theorem filterMapOfPredicateNatural {α β : Type*}
    (mapValue : α → β) (source : α → Bool) (target : β → Bool)
    (natural : ∀ value, target (mapValue value) = source value) :
    ∀ values : List α,
      (values.map mapValue).filter target =
        (values.filter source).map mapValue
  | [] => rfl
  | value :: values => by
      simp only [List.map_cons, List.filter_cons]
      rw [natural value, filterMapOfPredicateNatural mapValue source target natural values]
      cases source value <;> rfl

@[simp] theorem localizedRule3AxisContinuationCursors_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (children : List (input.LocalizedRerootCursor fuel))
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).localizedRule3AxisContinuationCursors
        (cursor.mapSpatialPoints mapPoint)
        (children.map fun child => child.mapSpatialPoints mapPoint) =
      (input.localizedRule3AxisContinuationCursors cursor children).map
        (fun child => child.mapSpatialPoints mapPoint) := by
  classical
  unfold localizedRule3AxisContinuationCursors
  apply filterMapOfPredicateNatural
  intro child
  simp only [localizedRule3AxisContinuation_mapSpatialPoints]

@[simp] theorem localizedRule3AxisPhysicalContinuationCursors_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (children : List (input.LocalizedRerootCursor fuel))
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).localizedRule3AxisPhysicalContinuationCursors
        (cursor.mapSpatialPoints mapPoint)
        (children.map fun child => child.mapSpatialPoints mapPoint) =
      (input.localizedRule3AxisPhysicalContinuationCursors cursor children).map
        (fun child => child.mapSpatialPoints mapPoint) := by
  classical
  unfold localizedRule3AxisPhysicalContinuationCursors
  apply filterMapOfPredicateNatural
  intro child
  simp only [localizedRule3AxisPhysicalContinuation_mapSpatialPoints]

@[simp] theorem localizedRule3AxisPhysicalContinuationCursors?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).localizedRule3AxisPhysicalContinuationCursors?
        (cursor.mapSpatialPoints mapPoint) =
      (input.localizedRule3AxisPhysicalContinuationCursors? cursor).map
        (List.map fun child => child.mapSpatialPoints mapPoint) := by
  unfold localizedRule3AxisPhysicalContinuationCursors?
  rw [localizedRerootChildren?_mapSpatialPoints]
  cases childrenEq : input.localizedRerootChildren? cursor with
  | none => rfl
  | some children =>
      simp

@[simp] theorem localizedRule3AxisTopology?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).localizedRule3AxisTopology?
        (cursor.mapSpatialPoints mapPoint) =
      (input.localizedRule3AxisTopology? cursor).map
        (fun topology => topology.mapSpatialPoints mapPoint) := by
  unfold localizedRule3AxisTopology?
  rw [localizedRule3AxisPhysicalContinuationCursors?_mapSpatialPoints]
  cases continuationsEq : input.localizedRule3AxisPhysicalContinuationCursors? cursor with
  | none => rfl
  | some continuations =>
      simp
      cases continuations with
      | nil => rfl
      | cons first rest =>
          cases rest with
          | nil =>
              cases provenanceEq : first.occurrence.1.node.provenance <;>
                simp [LocalizedRerootCursor.mapSpatialPoints,
                  LocalizedCIPOccurrence.mapSpatialPoints,
                  LocalizedCIPOccurrenceFrame.mapSpatialPoints, provenanceEq,
                  LocalizedRule3AxisTopology.mapSpatialPoints]
          | cons second more => rfl

theorem walkLocalizedRule3CumulatedAxis?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    ∀ (traversalFuel : Nat) (cursor : input.LocalizedRerootCursor fuel),
    (input.mapSpatialPoints mapPoint).walkLocalizedRule3CumulatedAxis?
        traversalFuel (cursor.mapSpatialPoints mapPoint) =
      (input.walkLocalizedRule3CumulatedAxis? traversalFuel cursor).map
        (List.map fun next => next.mapSpatialPoints mapPoint)
  | 0, cursor => by
      unfold walkLocalizedRule3CumulatedAxis?
      rw [localizedRule3AxisTopology?_mapSpatialPoints]
      cases topologyEq : input.localizedRule3AxisTopology? cursor with
      | none => rfl
      | some topology =>
          cases topology <;> rfl
  | traversalFuel + 1, cursor => by
      unfold walkLocalizedRule3CumulatedAxis?
      rw [localizedRule3AxisTopology?_mapSpatialPoints]
      cases topologyEq : input.localizedRule3AxisTopology? cursor with
      | none => rfl
      | some topology =>
          cases topology with
          | terminal => rfl
          | ringClosure closure | branched first second rest => rfl
          | linear next =>
              simp [LocalizedRule3AxisTopology.mapSpatialPoints]
              rw [walkLocalizedRule3CumulatedAxis?_mapSpatialPoints]
              cases input.walkLocalizedRule3CumulatedAxis? traversalFuel next <;> rfl

def LocalizedRule3CumulatedAxisEntry.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (entry : input.LocalizedRule3CumulatedAxisEntry fuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedRule3CumulatedAxisEntry fuel :=
  match entry with
  | .terminalStart initial => .terminalStart (initial.mapSpatialPoints mapPoint)
  | .internal initial previousAxis =>
      .internal (initial.mapSpatialPoints mapPoint)
        (previousAxis.mapSpatialPoints mapPoint)
  | .ringClosure initial closure =>
      .ringClosure (initial.mapSpatialPoints mapPoint)
        (closure.mapSpatialPoints mapPoint)
  | .branched initial first second rest =>
      .branched (initial.mapSpatialPoints mapPoint)
        (first.mapSpatialPoints mapPoint) (second.mapSpatialPoints mapPoint)
        (rest.map fun cursor => cursor.mapSpatialPoints mapPoint)

@[simp] theorem localizedRule3CumulatedAxisEntry?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).localizedRule3CumulatedAxisEntry?
        (occurrence.mapSpatialPoints mapPoint) =
      (input.localizedRule3CumulatedAxisEntry? occurrence).map
        (fun entry => entry.mapSpatialPoints mapPoint) := by
  unfold localizedRule3CumulatedAxisEntry?
  rw [localizedRule3PhysicalEndpointCursorFrame?_mapSpatialPoints]
  cases initialEq : input.localizedRule3PhysicalEndpointCursorFrame? occurrence with
  | none => rfl
  | some initial =>
      simp only [Option.map_some]
      simp [LocalizedRule3PhysicalEndpointCursorFrame.mapSpatialPoints]
      cases topologyEq : input.localizedRule3AxisTopology? initial.leftCursor with
      | none => simp
      | some topology =>
          cases topology <;>
            simp [LocalizedRule3AxisTopology.mapSpatialPoints,
              LocalizedRule3CumulatedAxisEntry.mapSpatialPoints,
              LocalizedRule3PhysicalEndpointCursorFrame.mapSpatialPoints]

def LocalizedRule3CumulatedEndpointCursorFrame.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (frame : input.LocalizedRule3CumulatedEndpointCursorFrame fuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedRule3CumulatedEndpointCursorFrame fuel :=
  { initial := frame.initial.mapSpatialPoints mapPoint
    rightward := frame.rightward.map fun cursor => cursor.mapSpatialPoints mapPoint
    rightPartnerCursor := frame.rightPartnerCursor.mapSpatialPoints mapPoint
    rightCursor := frame.rightCursor.mapSpatialPoints mapPoint
    rightPartner := frame.rightPartner
    right := frame.right }

@[simp] theorem localizedRule3CumulatedEndpointCursorFrame?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (traversalFuel : Nat) (occurrence : input.LocalizedCIPOccurrence fuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).localizedRule3CumulatedEndpointCursorFrame?
        traversalFuel (occurrence.mapSpatialPoints mapPoint) =
      (input.localizedRule3CumulatedEndpointCursorFrame?
        traversalFuel occurrence).map
          (fun frame => frame.mapSpatialPoints mapPoint) := by
  unfold localizedRule3CumulatedEndpointCursorFrame?
  rw [localizedRule3CumulatedAxisEntry?_mapSpatialPoints]
  cases entryEq : input.localizedRule3CumulatedAxisEntry? occurrence with
  | none => rfl
  | some entry =>
      simp only [Option.map_some]
      cases entry with
      | internal initial previousAxis =>
          simp [LocalizedRule3CumulatedAxisEntry.mapSpatialPoints]
      | ringClosure initial closure =>
          simp [LocalizedRule3CumulatedAxisEntry.mapSpatialPoints]
      | branched initial first second rest =>
          simp [LocalizedRule3CumulatedAxisEntry.mapSpatialPoints]
      | terminalStart initial =>
          simp [LocalizedRule3CumulatedAxisEntry.mapSpatialPoints,
            LocalizedRule3PhysicalEndpointCursorFrame.mapSpatialPoints]
          rw [walkLocalizedRule3CumulatedAxis?_mapSpatialPoints]
          cases rightwardEq : input.walkLocalizedRule3CumulatedAxis?
              traversalFuel initial.rightCursor with
          | none => rfl
          | some rightward =>
              simp only [Option.map_some]
              have reverseEq :
                  (rightward.map fun cursor =>
                      cursor.mapSpatialPoints mapPoint).reverse ++
                      [initial.leftCursor.mapSpatialPoints mapPoint] =
                    (rightward.reverse ++ [initial.leftCursor]).map
                      (fun cursor => cursor.mapSpatialPoints mapPoint) := by
                rw [← List.map_reverse, List.map_append]
                rfl
              simp only [Option.bind_some]
              rw [reverseEq]
              cases reversedEq : rightward.reverse ++ [initial.leftCursor] with
              | nil => rfl
              | cons rightCursor reversedTail =>
                  cases reversedTail with
                  | nil => rfl
                  | cons rightPartnerCursor rest =>
                      simp only [List.map_cons]
                      simp only [LocalizedRerootCursor.mapSpatialPoints,
                        LocalizedCIPOccurrence.mapSpatialPoints,
                        LocalizedCIPOccurrenceFrame.mapSpatialPoints]
                      cases rightPartnerEq :
                          rightPartnerCursor.occurrence.1.node.current? with
                      | none => rfl
                      | some rightPartner =>
                          cases rightEq : rightCursor.occurrence.1.node.current? with
                          | none => rfl
                          | some right =>
                              simp [LocalizedRule3CumulatedEndpointCursorFrame.mapSpatialPoints,
                                LocalizedRerootCursor.mapSpatialPoints,
                                LocalizedCIPOccurrence.mapSpatialPoints,
                                LocalizedCIPOccurrenceFrame.mapSpatialPoints]
                              rfl

def LocalizedRule3OddCumuleneEndpointCursorFrame.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (frame : input.LocalizedRule3OddCumuleneEndpointCursorFrame fuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedRule3OddCumuleneEndpointCursorFrame fuel :=
  { initial := frame.initial.mapSpatialPoints mapPoint
    rightward := frame.rightward.map fun cursor => cursor.mapSpatialPoints mapPoint
    rightPartnerCursor := frame.rightPartnerCursor.mapSpatialPoints mapPoint
    rightCursor := frame.rightCursor.mapSpatialPoints mapPoint
    rightPartner := frame.rightPartner
    right := frame.right }

@[simp] theorem localizedRule3OddCumuleneEndpointCursorFrame?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (traversalFuel : Nat) (occurrence : input.LocalizedCIPOccurrence fuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).localizedRule3OddCumuleneEndpointCursorFrame?
        traversalFuel (occurrence.mapSpatialPoints mapPoint) =
      (input.localizedRule3OddCumuleneEndpointCursorFrame?
        traversalFuel occurrence).map
          (fun frame => frame.mapSpatialPoints mapPoint) := by
  unfold localizedRule3OddCumuleneEndpointCursorFrame?
  rw [localizedRule3PhysicalEndpointCursorFrame?_mapSpatialPoints]
  cases initialEq : input.localizedRule3PhysicalEndpointCursorFrame? occurrence with
  | none => rfl
  | some initial =>
      simp only [Option.map_some]
      simp [LocalizedRule3PhysicalEndpointCursorFrame.mapSpatialPoints]
      cases topologyEq : input.localizedRule3AxisTopology? initial.leftCursor with
      | none => simp
      | some topology =>
          cases topology with
          | linear next =>
              simp [LocalizedRule3AxisTopology.mapSpatialPoints]
          | ringClosure next =>
              simp [LocalizedRule3AxisTopology.mapSpatialPoints]
          | branched first second rest =>
              simp [LocalizedRule3AxisTopology.mapSpatialPoints]
          | terminal =>
              simp [LocalizedRule3AxisTopology.mapSpatialPoints]
              rw [walkLocalizedRule3CumulatedAxis?_mapSpatialPoints]
              cases rightwardEq : input.walkLocalizedRule3CumulatedAxis?
                  traversalFuel initial.rightCursor with
              | none => rfl
              | some rightward =>
                  simp only [Option.map_some, Option.bind_some]
                  have reverseEq :
                      (rightward.map fun cursor =>
                          cursor.mapSpatialPoints mapPoint).reverse =
                        rightward.reverse.map
                          (fun cursor => cursor.mapSpatialPoints mapPoint) := by
                    rw [← List.map_reverse]
                  rw [reverseEq]
                  cases reversedEq : rightward.reverse with
                  | nil => rfl
                  | cons rightCursor reversedTail =>
                      cases reversedTail with
                      | nil => rfl
                      | cons rightPartnerCursor rest =>
                          simp only [List.map_cons]
                          by_cases admissible :
                              1 < rightward.length ∧ Odd rightward.length
                          · have mappedAdmissible :
                                1 < (rightward.map fun cursor =>
                                  cursor.mapSpatialPoints mapPoint).length ∧
                                  Odd (rightward.map fun cursor =>
                                    cursor.mapSpatialPoints mapPoint).length := by
                                simpa using admissible
                            simp [admissible]
                            simp only [LocalizedRerootCursor.mapSpatialPoints,
                              LocalizedCIPOccurrence.mapSpatialPoints,
                              LocalizedCIPOccurrenceFrame.mapSpatialPoints]
                            cases rightPartnerEq :
                                rightPartnerCursor.occurrence.1.node.current? with
                            | none => rfl
                            | some rightPartner =>
                                cases rightEq : rightCursor.occurrence.1.node.current? with
                                | none => rfl
                                | some right =>
                                    simp [LocalizedRule3OddCumuleneEndpointCursorFrame.mapSpatialPoints,
                                      LocalizedRerootCursor.mapSpatialPoints,
                                      LocalizedCIPOccurrence.mapSpatialPoints,
                                      LocalizedCIPOccurrenceFrame.mapSpatialPoints]
                                    rfl
                          · have notMappedAdmissible :
                                ¬ (1 < (rightward.map fun cursor =>
                                  cursor.mapSpatialPoints mapPoint).length ∧
                                  Odd (rightward.map fun cursor =>
                                    cursor.mapSpatialPoints mapPoint).length) := by
                                simpa using admissible
                            simp [admissible]

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
