import TetraStereo.OneCenter.LocalizedRule3OccurrenceReferenceCursor

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput



























/-! ## Carrier parent frame -/

/-- Executable twin of `localizedRule3CarrierParentFrame?`: the singleton carrier-parent frame of
an occurrence, or `none` when the carrier-parent list is empty or ambiguous. -/
def localizedRule3CarrierParentFrameExec?
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    Option input.LocalizedCIPOccurrenceFrame :=
  match input.localizedCarrierParentFrames (fuel := fuel) occurrence.1 with
  | [parent] => some parent
  | _ => none

/-- The executable carrier-parent frame twin is the original singleton check, including the
fail-closed `none` on an empty or non-singleton parent list. -/
theorem localizedRule3CarrierParentFrameExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    input.localizedRule3CarrierParentFrameExec? occurrence =
      input.localizedRule3CarrierParentFrame? occurrence :=
  rfl

/-- Every selected executable parent frame is an exact member of the certified carrier-parent
list, transported from the original soundness theorem along the twin equality. -/
theorem localizedRule3CarrierParentFrameExec?_sound
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (parent : input.LocalizedCIPOccurrenceFrame)
    (computed : input.localizedRule3CarrierParentFrameExec? occurrence = some parent) :
    parent ∈ input.localizedCarrierParentFrames (fuel := fuel) occurrence.1 := by
  rw [localizedRule3CarrierParentFrameExec?_eq_original input occurrence] at computed
  exact input.localizedRule3CarrierParentFrame?_sound occurrence parent computed

/-! ## Carrier parent occurrence -/

/-- Executable twin of `localizedRule3CarrierParentOccurrence?`.  The carrier-membership test of
the original is not evaluated: singleton selection already certifies membership, so the witness is
built from `localizedRule3CarrierParentFrame?_sound` and
`mem_localizedOccurrences_of_mem_localizedCarrierParentFrames`.  Both are proofs of a `Prop`, hence
erased, and the only use of the frame twin equality is inside that erased proof. -/
def localizedRule3CarrierParentOccurrenceExec?
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    Option (input.LocalizedCIPOccurrence fuel) :=
  match parentComputed : input.localizedRule3CarrierParentFrameExec? occurrence with
  | none => none
  | some parent =>
      some
        ⟨parent,
          input.mem_localizedOccurrences_of_mem_localizedCarrierParentFrames
            occurrence.1 parent
            (input.localizedRule3CarrierParentFrame?_sound occurrence parent
              (localizedRule3CarrierParentFrameExec?_eq_original input occurrence ▸
                parentComputed))⟩

/-- The executable parent-occurrence twin equals the original.  The original's membership test is
always true for the selected parent, so its `dite` takes the positive branch, where the two sides
differ only in the erased subtype proof. -/
theorem localizedRule3CarrierParentOccurrenceExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    input.localizedRule3CarrierParentOccurrenceExec? occurrence =
      input.localizedRule3CarrierParentOccurrence? occurrence := by
  classical
  unfold localizedRule3CarrierParentOccurrenceExec? localizedRule3CarrierParentOccurrence?
  rw [← localizedRule3CarrierParentFrameExec?_eq_original input occurrence]
  split
  · rw [show input.localizedRule3CarrierParentFrameExec? occurrence = none from by assumption]
  · rename_i parent frameComputed
    have parentPresent : parent ∈ input.localizedOccurrences fuel :=
      input.mem_localizedOccurrences_of_mem_localizedCarrierParentFrames
        occurrence.1 parent
        (input.localizedRule3CarrierParentFrame?_sound occurrence parent
          (localizedRule3CarrierParentFrameExec?_eq_original input occurrence ▸ frameComputed))
    split <;> simp_all

/-- Every selected executable parent occurrence is the exact shorter-address carrier member,
transported from the original soundness theorem along the twin equality. -/
theorem localizedRule3CarrierParentOccurrenceExec?_sound
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence parent : input.LocalizedCIPOccurrence fuel)
    (computed : input.localizedRule3CarrierParentOccurrenceExec? occurrence = some parent) :
    input.DeclarativeLocalizedRule3CarrierParentOccurrence occurrence parent := by
  rw [localizedRule3CarrierParentOccurrenceExec?_eq_original input occurrence] at computed
  exact input.localizedRule3CarrierParentOccurrence?_sound occurrence parent computed

/-- Executable parent recovery is total and exact at the canonical first child of every perceived
open even-cumulene axis, transported from the original totality theorem. -/
theorem localizedRule3CarrierParentOccurrenceExec?_evenAxialFirstChild
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axis : input.LocalizedEvenAxialChain) :
    input.localizedRule3CarrierParentOccurrenceExec?
        (input.localizedEvenAxialFirstChildOccurrence fuel axis) =
      some (input.localizedEvenAxialRootOccurrence fuel axis) := by
  rw [localizedRule3CarrierParentOccurrenceExec?_eq_original input
    (input.localizedEvenAxialFirstChildOccurrence fuel axis)]
  exact input.localizedRule3CarrierParentOccurrence?_evenAxialFirstChild fuel axis

/-! ## Physical endpoint cursor frame -/

/-- Executable twin of `localizedRule3PhysicalEndpointCursorFrame?`.  The physical provenance test,
the current/parent coordinates, the order-two bond check, the selected-parent-current check and the
emitted frame are the originals; only the parent occurrence comes from the executable twin. -/
def localizedRule3PhysicalEndpointCursorFrameExec?
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    Option (input.LocalizedRule3PhysicalEndpointCursorFrame fuel) :=
  if occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom then
    match occurrence.1.node.current?, occurrence.1.node.parent? with
    | some current, some parent =>
        if input.moleculeGraph.bond parent current = 2 then do
          let parentOccurrence ←
            input.localizedRule3CarrierParentOccurrenceExec? occurrence
          if parentOccurrence.1.node.current? = some parent then
            some
              { left := parent
                right := current
                leftCursor :=
                  { occurrence := parentOccurrence, previous? := some occurrence }
                rightCursor :=
                  { occurrence := occurrence, previous? := some parentOccurrence } }
          else none
        else none
    | _, _ => none
  else none

/-- The executable physical endpoint frame twin equals the original at every occurrence.  The two
bodies differ exactly in the parent-occurrence subterm, which the parent-occurrence twin equality
identifies. -/
theorem localizedRule3PhysicalEndpointCursorFrameExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence =
      input.localizedRule3PhysicalEndpointCursorFrame? occurrence := by
  unfold localizedRule3PhysicalEndpointCursorFrameExec?
  unfold localizedRule3PhysicalEndpointCursorFrame?
  rw [localizedRule3CarrierParentOccurrenceExec?_eq_original input occurrence]
  split <;> exact rfl

/-- Successful executable physical endpoint recovery preserves the exact carrier path in both
directions, transported from the original soundness theorem along the twin equality. -/
theorem localizedRule3PhysicalEndpointCursorFrameExec?_sound
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (frame : input.LocalizedRule3PhysicalEndpointCursorFrame fuel)
    (computed : input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence = some frame) :
    input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame occurrence frame := by
  rw [localizedRule3PhysicalEndpointCursorFrameExec?_eq_original input occurrence] at computed
  exact input.localizedRule3PhysicalEndpointCursorFrame?_sound occurrence frame computed

/-- Executable physical endpoint recovery is total and yields the canonical orientation for every
perceived open even-cumulene axis, transported from the original totality theorem. -/
theorem localizedRule3PhysicalEndpointCursorFrameExec?_evenAxialFirstChild
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axis : input.LocalizedEvenAxialChain) :
    input.localizedRule3PhysicalEndpointCursorFrameExec?
        (input.localizedEvenAxialFirstChildOccurrence fuel axis) =
      some (input.localizedEvenAxialInitialPhysicalEndpointCursorFrame fuel axis) := by
  rw [localizedRule3PhysicalEndpointCursorFrameExec?_eq_original input
    (input.localizedEvenAxialFirstChildOccurrence fuel axis)]
  exact input.localizedRule3PhysicalEndpointCursorFrame?_evenAxialFirstChild fuel axis

/-- Executable physical endpoint recovery is total and canonically oriented for the first child of
every exact maximal open double-bond root, transported from the original totality theorem. -/
theorem localizedRule3PhysicalEndpointCursorFrameExec?_axialRootFirstChild
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axialRoot : input.LocalizedAxialRoot) :
    input.localizedRule3PhysicalEndpointCursorFrameExec?
        (input.localizedAxialRootFirstChildOccurrence fuel axialRoot) =
      some (input.localizedAxialRootInitialPhysicalEndpointCursorFrame fuel axialRoot) := by
  rw [localizedRule3PhysicalEndpointCursorFrameExec?_eq_original input
    (input.localizedAxialRootFirstChildOccurrence fuel axialRoot)]
  exact input.localizedRule3PhysicalEndpointCursorFrame?_axialRootFirstChild fuel axialRoot

/-- Executable physical endpoint recovery is total and returns the canonical orientation for every
molecule-wide physical double bond, transported from the original totality theorem. -/
theorem localizedRule3PhysicalEndpointCursorFrameExec?_canonicalDoubleBondFirstChild
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (bond : input.LocalizedCanonicalDoubleBond) :
    input.localizedRule3PhysicalEndpointCursorFrameExec?
        (input.localizedCanonicalDoubleBondFirstChildOccurrence fuel bond) =
      some (input.localizedCanonicalDoubleBondInitialPhysicalEndpointCursorFrame fuel bond) := by
  rw [localizedRule3PhysicalEndpointCursorFrameExec?_eq_original input
    (input.localizedCanonicalDoubleBondFirstChildOccurrence fuel bond)]
  exact input.localizedRule3PhysicalEndpointCursorFrame?_canonicalDoubleBondFirstChild fuel bond

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
