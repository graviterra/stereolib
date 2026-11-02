import TetraStereo.OneCenter.LocalizedRule3DescriptorBearingReference

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Occurrence-path cursors for Rule-3 endpoint references

Rule-3 reference selection in a ring cannot be reconstructed from an atom-global label.  This
module recovers both physical endpoints from the exact localized carrier occurrence and then
selects reference branches only among the endpoint cursor's cut-neighborhood.  A real child and a
ring-duplicate child are physical substituent positions; multiple-bond duplicate copies and
placeholder nodes are not independent endpoint references.

Every search is singleton-checked and fail-closed.  The next layer can therefore compile a
descriptor-bearing Rules-1a--5 key for the returned cursor without forgetting its occurrence path.
-/

namespace CertifiedLocalizedCIPInput

/-- Physical endpoint references may be represented by an unvisited real atom or by the terminal
duplicate that opens a ring in the current digraph. -/
def LocalizedRule3PhysicalReferenceProvenance :
    OfficialCIPNodeProvenance → Prop
  | .realAtom => True
  | .ringDuplicate _ => True
  | .multipleBondDuplicate _ | .placeholder _ _ => False

instance (provenance : OfficialCIPNodeProvenance) :
    Decidable (LocalizedRule3PhysicalReferenceProvenance provenance) := by
  cases provenance <;> simp only [LocalizedRule3PhysicalReferenceProvenance]
  all_goals first | exact isTrue trivial | exact isFalse id

/-- Executable physical-reference provenance test. -/
def localizedRule3PhysicalReferenceProvenance :
    OfficialCIPNodeProvenance → Bool
  | .realAtom | .ringDuplicate _ => true
  | .multipleBondDuplicate _ | .placeholder _ _ => false

@[simp] theorem localizedRule3PhysicalReferenceProvenance_eq_true_iff
    (provenance : OfficialCIPNodeProvenance) :
    localizedRule3PhysicalReferenceProvenance provenance = true ↔
      LocalizedRule3PhysicalReferenceProvenance provenance := by
  cases provenance <;> simp [localizedRule3PhysicalReferenceProvenance,
    LocalizedRule3PhysicalReferenceProvenance]

/-- Search source whose uncut zipper neighborhood contains the unique carrier parent. -/
def localizedRule3ParentSearchCursor
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    input.LocalizedRerootCursor fuel :=
  { occurrence := occurrence, previous? := none }

/-- Singleton-checked parent frame. -/
noncomputable def localizedRule3CarrierParentFrame?
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    Option input.LocalizedCIPOccurrenceFrame :=
  match input.localizedCarrierParentFrames (fuel := fuel) occurrence.1 with
  | [parent] => some parent
  | _ => none

/-- Singleton selection preserves membership in the exact parent-frame list. -/
theorem localizedRule3CarrierParentFrame?_sound
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (parent : input.LocalizedCIPOccurrenceFrame)
    (computed : input.localizedRule3CarrierParentFrame? occurrence = some parent) :
    parent ∈ input.localizedCarrierParentFrames (fuel := fuel) occurrence.1 := by
  unfold localizedRule3CarrierParentFrame? at computed
  generalize parentFramesIdentity :
      input.localizedCarrierParentFrames (fuel := fuel) occurrence.1 = parentFrames
        at computed
  cases parentFrames with
  | nil => simp at computed
  | cons candidate rest =>
      cases rest with
      | nil =>
          simp at computed
          subst parent
          simp
      | cons next more => simp at computed

/-- The unique shorter-address carrier occurrence immediately preceding a Rule-3 node.  The exact
carrier-parent list is used directly; expanding the entire zipper neighborhood and filtering back
to the shorter address would introduce an unnecessary refusal path. -/
noncomputable def localizedRule3CarrierParentOccurrence?
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    Option (input.LocalizedCIPOccurrence fuel) := by
  classical
  match parentComputed : input.localizedRule3CarrierParentFrame? occurrence with
  | none => exact none
  | some parent =>
      if present : parent ∈ input.localizedOccurrences fuel then
        exact some ⟨parent, present⟩
      else exact none

/-- Independent carrier-parent meaning, retaining the exact certified zipper expansion. -/
def DeclarativeLocalizedRule3CarrierParentOccurrence
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence parent : input.LocalizedCIPOccurrence fuel) : Prop :=
  parent.1 ∈ input.localizedCarrierParentFrames (fuel := fuel) occurrence.1

/-- Every returned parent is the actual shorter-address member of the certified carrier frame. -/
theorem localizedRule3CarrierParentOccurrence?_sound
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence parent : input.LocalizedCIPOccurrence fuel)
    (computed : input.localizedRule3CarrierParentOccurrence? occurrence = some parent) :
    input.DeclarativeLocalizedRule3CarrierParentOccurrence occurrence parent := by
  classical
  unfold localizedRule3CarrierParentOccurrence? at computed
  cases frameComputed : input.localizedRule3CarrierParentFrame? occurrence with
  | none =>
      rw [frameComputed] at computed
      simp at computed
  | some frame =>
      rw [frameComputed] at computed
      simp only at computed
      by_cases present : frame ∈ input.localizedOccurrences fuel
      · rw [dif_pos present] at computed
        simp at computed
        subst parent
        exact input.localizedRule3CarrierParentFrame?_sound
          occurrence frame frameComputed
      · rw [dif_neg present] at computed
        simp at computed

/-- Parent recovery is total and exact for the canonical first occurrence of every perceived open
even-cumulene axis. -/
theorem localizedRule3CarrierParentOccurrence?_evenAxialFirstChild
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axis : input.LocalizedEvenAxialChain) :
    input.localizedRule3CarrierParentOccurrence?
        (input.localizedEvenAxialFirstChildOccurrence fuel axis) =
      some (input.localizedEvenAxialRootOccurrence fuel axis) := by
  classical
  have frameComputed : input.localizedRule3CarrierParentFrame?
      (input.localizedEvenAxialFirstChildOccurrence fuel axis) =
        some (input.localizedEvenAxialRootOccurrence fuel axis).1 := by
    unfold localizedRule3CarrierParentFrame?
    rw [input.localizedCarrierParentFrames_evenAxialFirstChild_eq_singleton fuel axis]
  unfold localizedRule3CarrierParentOccurrence?
  rw [frameComputed]
  simp only
  rw [dif_pos (input.localizedEvenAxialRootOccurrence fuel axis).2]

/-- Parent recovery is total at the first child of any exact maximal open double-bond root,
independent of its later parity classification. -/
theorem localizedRule3CarrierParentOccurrence?_axialRootFirstChild
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axialRoot : input.LocalizedAxialRoot) :
    input.localizedRule3CarrierParentOccurrence?
        (input.localizedAxialRootFirstChildOccurrence fuel axialRoot) =
      some (input.localizedAxialRootOccurrence fuel axialRoot) := by
  classical
  have frameComputed : input.localizedRule3CarrierParentFrame?
      (input.localizedAxialRootFirstChildOccurrence fuel axialRoot) =
        some (input.localizedAxialRootOccurrence fuel axialRoot).1 := by
    unfold localizedRule3CarrierParentFrame?
    rw [input.localizedCarrierParentFrames_axialRootFirstChild_eq_singleton
      fuel axialRoot]
  unfold localizedRule3CarrierParentOccurrence?
  rw [frameComputed]
  simp only
  rw [dif_pos (input.localizedAxialRootOccurrence fuel axialRoot).2]

/-- Parent recovery is total for the canonical first child of every molecule-wide physical
double bond. -/
theorem localizedRule3CarrierParentOccurrence?_canonicalDoubleBondFirstChild
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (bond : input.LocalizedCanonicalDoubleBond) :
    input.localizedRule3CarrierParentOccurrence?
        (input.localizedCanonicalDoubleBondFirstChildOccurrence fuel bond) =
      some (input.localizedAtomRootOccurrence fuel bond.1.1) := by
  classical
  have frameComputed : input.localizedRule3CarrierParentFrame?
      (input.localizedCanonicalDoubleBondFirstChildOccurrence fuel bond) =
        some (input.localizedAtomRootOccurrence fuel bond.1.1).1 := by
    unfold localizedRule3CarrierParentFrame?
    rw [input.localizedCarrierParentFrames_canonicalDoubleBondFirstChild_eq_singleton
      fuel bond]
  unfold localizedRule3CarrierParentOccurrence?
  rw [frameComputed]
  simp only
  rw [dif_pos (input.localizedAtomRootOccurrence fuel bond.1.1).2]

/-- Both directions of the physical double-bond edge as cut reroot cursors. -/
structure LocalizedRule3PhysicalEndpointCursorFrame
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) where
  left : input.Atom
  right : input.Atom
  leftCursor : input.LocalizedRerootCursor fuel
  rightCursor : input.LocalizedRerootCursor fuel

/-- Canonical oriented physical endpoint frame supplied by one perceived open even-axis root and
its real first child. -/
noncomputable def localizedEvenAxialInitialPhysicalEndpointCursorFrame
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axis : input.LocalizedEvenAxialChain) :
    input.LocalizedRule3PhysicalEndpointCursorFrame fuel :=
  let root := input.localizedEvenAxialRootOccurrence fuel axis
  let child := input.localizedEvenAxialFirstChildOccurrence fuel axis
  { left := axis.1.root.terminal
    right := axis.1.root.firstAxis
    leftCursor := { occurrence := root, previous? := some child }
    rightCursor := { occurrence := child, previous? := some root } }

/-- Canonical oriented endpoint frame supplied by any exact maximal open-chain terminal root. -/
noncomputable def localizedAxialRootInitialPhysicalEndpointCursorFrame
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axialRoot : input.LocalizedAxialRoot) :
    input.LocalizedRule3PhysicalEndpointCursorFrame fuel :=
  let root := input.localizedAxialRootOccurrence fuel axialRoot
  let child := input.localizedAxialRootFirstChildOccurrence fuel axialRoot
  { left := axialRoot.1.terminal
    right := axialRoot.1.firstAxis
    leftCursor := { occurrence := root, previous? := some child }
    rightCursor := { occurrence := child, previous? := some root } }

/-- Canonical two-direction endpoint frame for one molecule-wide physical double bond. -/
noncomputable def localizedCanonicalDoubleBondInitialPhysicalEndpointCursorFrame
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (bond : input.LocalizedCanonicalDoubleBond) :
    input.LocalizedRule3PhysicalEndpointCursorFrame fuel :=
  let root := input.localizedAtomRootOccurrence fuel bond.1.1
  let child := input.localizedCanonicalDoubleBondFirstChildOccurrence fuel bond
  { left := bond.1.1
    right := bond.1.2
    leftCursor := { occurrence := root, previous? := some child }
    rightCursor := { occurrence := child, previous? := some root } }

/-- Recover a genuine real order-two occurrence's two endpoint cursors.  The left cursor cuts the
right occurrence, and the right cursor cuts the certified carrier parent. -/
noncomputable def localizedRule3PhysicalEndpointCursorFrame?
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    Option (input.LocalizedRule3PhysicalEndpointCursorFrame fuel) :=
  if occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom then
    match occurrence.1.node.current?, occurrence.1.node.parent? with
    | some current, some parent =>
        if input.moleculeGraph.bond parent current = 2 then do
          let parentOccurrence ← input.localizedRule3CarrierParentOccurrence? occurrence
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

/-- Independent exact topology of a recovered physical endpoint frame. -/
def DeclarativeLocalizedRule3PhysicalEndpointCursorFrame
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (frame : input.LocalizedRule3PhysicalEndpointCursorFrame fuel) : Prop :=
  occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom ∧
    occurrence.1.node.current? = some frame.right ∧
    occurrence.1.node.parent? = some frame.left ∧
    input.moleculeGraph.bond frame.left frame.right = 2 ∧
    input.DeclarativeLocalizedRule3CarrierParentOccurrence
      occurrence frame.leftCursor.occurrence ∧
    frame.leftCursor.occurrence.1.node.current? = some frame.left ∧
    frame.leftCursor.previous? = some occurrence ∧
    frame.rightCursor.occurrence = occurrence ∧
    frame.rightCursor.previous? = some frame.leftCursor.occurrence

/-- Successful physical endpoint recovery preserves the exact carrier path in both directions. -/
theorem localizedRule3PhysicalEndpointCursorFrame?_sound
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (frame : input.LocalizedRule3PhysicalEndpointCursorFrame fuel)
    (computed : input.localizedRule3PhysicalEndpointCursorFrame? occurrence = some frame) :
    input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame occurrence frame := by
  unfold localizedRule3PhysicalEndpointCursorFrame? at computed
  by_cases real : occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom
  · rw [if_pos real] at computed
    cases currentComputed : occurrence.1.node.current? with
    | none => simp [currentComputed] at computed
    | some current =>
        cases parentComputed : occurrence.1.node.parent? with
        | none => simp [currentComputed, parentComputed] at computed
        | some parent =>
            by_cases doubleBond : input.moleculeGraph.bond parent current = 2
            · rw [currentComputed, parentComputed] at computed
              simp only at computed
              rw [if_pos doubleBond] at computed
              cases carrierParentComputed :
                  input.localizedRule3CarrierParentOccurrence? occurrence with
              | none => simp [carrierParentComputed] at computed
              | some parentOccurrence =>
                  by_cases parentAtom :
                      parentOccurrence.1.node.current? = some parent
                  · simp [carrierParentComputed, parentAtom] at computed
                    subst frame
                    exact ⟨real, currentComputed, parentComputed, doubleBond,
                      input.localizedRule3CarrierParentOccurrence?_sound
                        occurrence parentOccurrence carrierParentComputed,
                      parentAtom, rfl, rfl, rfl⟩
                  · simp [carrierParentComputed, parentAtom] at computed
            · simp [currentComputed, parentComputed, doubleBond] at computed
  · simp [real] at computed

/-- Physical endpoint recovery is total and yields the canonical orientation for every perceived
open even-cumulene axis. -/
theorem localizedRule3PhysicalEndpointCursorFrame?_evenAxialFirstChild
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axis : input.LocalizedEvenAxialChain) :
    input.localizedRule3PhysicalEndpointCursorFrame?
        (input.localizedEvenAxialFirstChildOccurrence fuel axis) =
      some (input.localizedEvenAxialInitialPhysicalEndpointCursorFrame fuel axis) := by
  have physical := input.localizedEvenAxialFirstChildOccurrence_physical fuel axis
  unfold localizedRule3PhysicalEndpointCursorFrame?
  rw [if_pos physical.1]
  rw [physical.2.1, physical.2.2.1]
  simp only
  rw [if_pos physical.2.2.2]
  rw [input.localizedRule3CarrierParentOccurrence?_evenAxialFirstChild fuel axis]
  simp [localizedEvenAxialInitialPhysicalEndpointCursorFrame]
  rfl

/-- Physical endpoint recovery is total and canonically oriented for the first child of every
exact maximal open double-bond root. -/
theorem localizedRule3PhysicalEndpointCursorFrame?_axialRootFirstChild
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axialRoot : input.LocalizedAxialRoot) :
    input.localizedRule3PhysicalEndpointCursorFrame?
        (input.localizedAxialRootFirstChildOccurrence fuel axialRoot) =
      some (input.localizedAxialRootInitialPhysicalEndpointCursorFrame
        fuel axialRoot) := by
  have physical := input.localizedAxialRootFirstChildOccurrence_physical fuel axialRoot
  unfold localizedRule3PhysicalEndpointCursorFrame?
  rw [if_pos physical.1]
  rw [physical.2.1, physical.2.2.1]
  simp only
  rw [if_pos physical.2.2.2]
  rw [input.localizedRule3CarrierParentOccurrence?_axialRootFirstChild fuel axialRoot]
  simp [localizedAxialRootInitialPhysicalEndpointCursorFrame,
    localizedAxialRootOccurrence, localizedAtomRootOccurrence]
  rfl

/-- Physical endpoint recovery is total and returns the canonical orientation for every
molecule-wide physical double bond. -/
theorem localizedRule3PhysicalEndpointCursorFrame?_canonicalDoubleBondFirstChild
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (bond : input.LocalizedCanonicalDoubleBond) :
    input.localizedRule3PhysicalEndpointCursorFrame?
        (input.localizedCanonicalDoubleBondFirstChildOccurrence fuel bond) =
      some (input.localizedCanonicalDoubleBondInitialPhysicalEndpointCursorFrame
        fuel bond) := by
  have physical :=
    input.localizedCanonicalDoubleBondFirstChildOccurrence_physical fuel bond
  unfold localizedRule3PhysicalEndpointCursorFrame?
  rw [if_pos physical.1]
  rw [physical.2.1, physical.2.2.1]
  simp only
  rw [if_pos physical.2.2.2]
  rw [input.localizedRule3CarrierParentOccurrence?_canonicalDoubleBondFirstChild fuel bond]
  simp [localizedCanonicalDoubleBondInitialPhysicalEndpointCursorFrame]
  rfl

/-- Candidate endpoint children with the requested physical atom and an admissible real/ring
provenance. -/
def localizedRule3ReferenceCursorCandidates
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (children : List (input.LocalizedRerootCursor fuel))
    (reference : input.Atom) : List (input.LocalizedRerootCursor fuel) :=
  children.filter fun child =>
    child.occurrence.1.node.current? == some reference &&
      localizedRule3PhysicalReferenceProvenance
        child.occurrence.1.node.provenance

/-- Find the unique occurrence-local branch for a physical endpoint reference. -/
noncomputable def localizedRule3ReferenceCursor?
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (endpointCursor : input.LocalizedRerootCursor fuel)
    (reference : input.Atom) : Option (input.LocalizedRerootCursor fuel) := do
  let children ← input.localizedRerootChildren? endpointCursor
  match input.localizedRule3ReferenceCursorCandidates children reference with
  | [cursor] => some cursor
  | _ => none

/-- Independent occurrence-local meaning of a selected reference cursor. -/
def DeclarativeLocalizedRule3ReferenceCursor
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (endpointCursor cursor : input.LocalizedRerootCursor fuel)
    (reference : input.Atom) : Prop :=
  ∃ children,
    input.localizedRerootChildren? endpointCursor = some children ∧
      input.DeclarativeLocalizedRerootChildren endpointCursor children ∧
      cursor ∈ children ∧
      cursor.occurrence.1.node.current? = some reference ∧
      LocalizedRule3PhysicalReferenceProvenance
        cursor.occurrence.1.node.provenance ∧
      cursor.previous? = some endpointCursor.occurrence

/-- Every non-parent physical graph edge below positive carrier depth has a corresponding
occurrence-local reference cursor, provided its sibling coordinate is not the incoming cut.  The
zero copy may be either a fresh real occurrence or a ring-duplicate occurrence. -/
theorem exists_declarativeLocalizedRule3ReferenceCursor_of_real_outward
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (endpointCursor : input.LocalizedRerootCursor fuel)
    (endpoint reference : input.Atom)
    (real : endpointCursor.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (current : endpointCursor.occurrence.1.node.current? = some endpoint)
    (positive : 0 < endpointCursor.occurrence.1.remaining)
    (adjacent : input.moleculeGraph.Adj endpoint reference)
    (notParent : endpointCursor.occurrence.1.node.parent? ≠ some reference)
    (notIncoming : ∀ slot,
      (endpointCursor.occurrence.1.node.extend reference 0, slot) ∈
          (input.executableOfficialCIPChildren
            endpointCursor.occurrence.1.node).zipIdx →
      ∀ previous, endpointCursor.previous? = some previous →
        endpointCursor.occurrence.1.address ++ [slot] ≠ previous.1.address) :
    ∃ cursor,
      input.DeclarativeLocalizedRule3ReferenceCursor
        endpointCursor cursor reference := by
  let child := endpointCursor.occurrence.1.node.extend reference 0
  have childPresent : child ∈ input.executableOfficialCIPChildren
      endpointCursor.occurrence.1.node := by
    exact input.extend_zero_mem_executableOfficialCIPChildren_of_real
      endpointCursor.occurrence.1.node endpoint reference real current adjacent notParent
  rw [List.mem_iff_getElem] at childPresent
  rcases childPresent with ⟨slot, slotValid, childAtSlot⟩
  have childZipPresent : (child, slot) ∈
      (input.executableOfficialCIPChildren
        endpointCursor.occurrence.1.node).zipIdx := by
    rw [List.mem_iff_getElem]
    exact ⟨slot, by simpa using slotValid, by simp [childAtSlot]⟩
  have nonduplicate : endpointCursor.occurrence.1.node.isDuplicateLeaf = false := by
    simp [OfficialCIPNode.isDuplicateLeaf, real]
  obtain ⟨children, cursor, childrenComputed, cursorPresent, cursorFrame⟩ :=
    input.exists_mem_localizedRerootChildren_of_executable_child
      endpointCursor nonduplicate positive child slot childZipPresent
      (notIncoming slot childZipPresent)
  have exactChildren := input.localizedRerootChildren?_sound
    endpointCursor children childrenComputed
  have childPhysical : LocalizedRule3PhysicalReferenceProvenance child.provenance := by
    by_cases seen : reference ∈ endpointCursor.occurrence.1.node.history
    · simp [child, LocalizedRule3PhysicalReferenceProvenance,
        OfficialCIPNode.extend_provenance,
        OfficialCIPNode.childProvenance_ring_duplicate _ _ seen]
    · simp [child, LocalizedRule3PhysicalReferenceProvenance,
        OfficialCIPNode.extend_provenance,
        OfficialCIPNode.childProvenance_real _ _ seen]
  refine ⟨cursor, children, childrenComputed, exactChildren, cursorPresent, ?_, ?_, ?_⟩
  · rw [cursorFrame]
    simp [child]
  · rw [cursorFrame]
    exact childPhysical
  · exact exactChildren.2 cursor cursorPresent

/-- Every selected cursor is an exact cut-neighborhood child representing the requested physical
atom, including the cyclic ring-duplicate representation. -/
theorem localizedRule3ReferenceCursor?_sound
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (endpointCursor cursor : input.LocalizedRerootCursor fuel)
    (reference : input.Atom)
    (computed : input.localizedRule3ReferenceCursor?
      endpointCursor reference = some cursor) :
    input.DeclarativeLocalizedRule3ReferenceCursor
      endpointCursor cursor reference := by
  unfold localizedRule3ReferenceCursor? at computed
  cases childrenComputed : input.localizedRerootChildren? endpointCursor with
  | none => simp [childrenComputed] at computed
  | some children =>
      generalize candidatesIdentity :
          input.localizedRule3ReferenceCursorCandidates children reference =
            candidates at computed
      cases candidates with
      | nil => simp [childrenComputed, candidatesIdentity] at computed
      | cons selected rest =>
          cases rest with
          | nil =>
              simp [childrenComputed, candidatesIdentity] at computed
              subst cursor
              have candidatePresent : selected ∈
                  input.localizedRule3ReferenceCursorCandidates children reference := by
                rw [candidatesIdentity]
                simp
              have filtered := List.mem_filter.mp candidatePresent
              have conditions :
                  selected.occurrence.1.node.current? = some reference ∧
                    localizedRule3PhysicalReferenceProvenance
                      selected.occurrence.1.node.provenance = true := by
                simpa [localizedRule3ReferenceCursorCandidates] using filtered.2
              have exactChildren := input.localizedRerootChildren?_sound
                endpointCursor children childrenComputed
              refine ⟨children, childrenComputed, exactChildren, filtered.1, ?_, ?_, ?_⟩
              · exact conditions.1
              · exact (localizedRule3PhysicalReferenceProvenance_eq_true_iff
                  selected.occurrence.1.node.provenance).mp conditions.2
              · exact exactChildren.2 selected filtered.1
          | cons next more =>
              simp [childrenComputed, candidatesIdentity] at computed

/-- Canonical reference selection adds the chemically necessary uniqueness condition to the
independent physical-reference relation.  It permits either a real occurrence or a ring-duplicate
occurrence, but exactly one cut-neighborhood cursor may represent the requested physical atom. -/
def CanonicalLocalizedRule3ReferenceCursor
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (endpointCursor cursor : input.LocalizedRerootCursor fuel)
    (reference : input.Atom) : Prop :=
  ∃ children,
    input.localizedRerootChildren? endpointCursor = some children ∧
      input.DeclarativeLocalizedRerootChildren endpointCursor children ∧
      cursor ∈ children ∧
      cursor.occurrence.1.node.current? = some reference ∧
      LocalizedRule3PhysicalReferenceProvenance
        cursor.occurrence.1.node.provenance ∧
      cursor.previous? = some endpointCursor.occurrence ∧
      ∀ candidate, candidate ∈ children →
        candidate.occurrence.1.node.current? = some reference →
        LocalizedRule3PhysicalReferenceProvenance
          candidate.occurrence.1.node.provenance →
        candidate = cursor

/-- At an endpoint that is either the carrier root or was entered from its carrier parent, every
uncut zipper neighbor is outward.  These are exactly the two orientations of the endpoint cursors
constructed for a perceived open cumulene. -/
theorem address_eq_append_singleton_of_mem_intended_of_endpoint_shape
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (endpointCursor : input.LocalizedRerootCursor fuel)
    (endpointShape :
      endpointCursor.occurrence.1.address = [] ∨
        ∃ previous incomingSlot,
          endpointCursor.previous? = some previous ∧
            endpointCursor.occurrence.1.address =
              previous.1.address ++ [incomingSlot])
    (frame : input.LocalizedCIPOccurrenceFrame)
    (present : frame ∈ input.intendedLocalizedRerootChildFrames endpointCursor) :
    ∃ slot, frame.address = endpointCursor.occurrence.1.address ++ [slot] := by
  have neighbor := input.mem_localizedRerootNeighborFrames_of_mem_intended
    endpointCursor frame present
  have characterized :=
    (input.mem_localizedRerootNeighborFrames_iff
      endpointCursor.occurrence.1 frame).mp neighbor
  rcases characterized.2 with ⟨_sameRoot, parent | outward⟩
  · rcases endpointShape with root | ⟨previous, incomingSlot,
        previousExact, cursorAddress⟩
    · rw [root] at parent
      simp at parent
    · have uncut := input.address_ne_previous_of_mem_intended
        endpointCursor previous previousExact frame present
      have parentAddress : frame.address = previous.1.address := by
        rw [parent.2, cursorAddress]
        simp
      exact (uncut parentAddress).elim
  · have nonempty : frame.address ≠ [] := by
      intro empty
      rw [empty] at outward
      simp at outward
    let slot := frame.address.getLast nonempty
    refine ⟨slot, ?_⟩
    calc
      frame.address = frame.address.dropLast ++ [slot] :=
        (List.dropLast_append_getLast nonempty).symm
      _ = endpointCursor.occurrence.1.address ++ [slot] := by rw [← outward.2]

/-- Two physical references to the same atom are the same occurrence cursor whenever both are
outward children of the endpoint coordinate.  This is the carrier-level uniqueness fact needed
by endpoint selection: positive multiple-bond copies are excluded by physical provenance, a
real/ring zero copy has one official sibling slot, and the shared occurrence carrier is
functional at a root/address coordinate. -/
theorem localizedRule3PhysicalReferenceCursor_unique_of_outward
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (endpointCursor first second : input.LocalizedRerootCursor fuel)
    (reference : input.Atom)
    (children : List (input.LocalizedRerootCursor fuel))
    (childrenDerived : input.DeclarativeLocalizedRerootChildren
      endpointCursor children)
    (firstPresent : first ∈ children)
    (secondPresent : second ∈ children)
    (firstCurrent : first.occurrence.1.node.current? = some reference)
    (secondCurrent : second.occurrence.1.node.current? = some reference)
    (firstPhysical : LocalizedRule3PhysicalReferenceProvenance
      first.occurrence.1.node.provenance)
    (secondPhysical : LocalizedRule3PhysicalReferenceProvenance
      second.occurrence.1.node.provenance)
    (firstOutward : ∃ slot,
      first.occurrence.1.address = endpointCursor.occurrence.1.address ++ [slot])
    (secondOutward : ∃ slot,
      second.occurrence.1.address = endpointCursor.occurrence.1.address ++ [slot]) :
    first = second := by
  rcases firstOutward with ⟨firstSlot, firstAddress⟩
  rcases secondOutward with ⟨secondSlot, secondAddress⟩
  have sourceDerived :=
    (input.mem_localizedOccurrences_iff fuel endpointCursor.occurrence.1).mp
      endpointCursor.occurrence.2
  have firstRoot := input.localizedRerootChildren_root_eq
    endpointCursor first children childrenDerived firstPresent
  have secondRoot := input.localizedRerootChildren_root_eq
    endpointCursor second children childrenDerived secondPresent
  obtain ⟨firstNode, firstAtSlot, firstFrame⟩ :=
    input.declarativeLocalizedOccurrence_immediate_child
      sourceDerived
      ((input.mem_localizedOccurrences_iff fuel first.occurrence.1).mp
        first.occurrence.2)
      firstRoot firstSlot firstAddress
  obtain ⟨secondNode, secondAtSlot, secondFrame⟩ :=
    input.declarativeLocalizedOccurrence_immediate_child
      sourceDerived
      ((input.mem_localizedOccurrences_iff fuel second.occurrence.1).mp
        second.occurrence.2)
      secondRoot secondSlot secondAddress
  have firstNodeIdentity : first.occurrence.1.node = firstNode := by
    simpa using congrArg LocalizedCIPOccurrenceFrame.node firstFrame
  have secondNodeIdentity : second.occurrence.1.node = secondNode := by
    simpa using congrArg LocalizedCIPOccurrenceFrame.node secondFrame
  have firstPhysicalNode :
      firstNode.provenance = OfficialCIPNodeProvenance.realAtom ∨
        ∃ distance, firstNode.provenance =
          OfficialCIPNodeProvenance.ringDuplicate distance := by
    rw [← firstNodeIdentity]
    cases provenance : first.occurrence.1.node.provenance <;>
      simp [LocalizedRule3PhysicalReferenceProvenance, provenance] at firstPhysical
    · exact Or.inl rfl
    · exact Or.inr ⟨_, rfl⟩
  have secondPhysicalNode :
      secondNode.provenance = OfficialCIPNodeProvenance.realAtom ∨
        ∃ distance, secondNode.provenance =
          OfficialCIPNodeProvenance.ringDuplicate distance := by
    rw [← secondNodeIdentity]
    cases provenance : second.occurrence.1.node.provenance <;>
      simp [LocalizedRule3PhysicalReferenceProvenance, provenance] at secondPhysical
    · exact Or.inl rfl
    · exact Or.inr ⟨_, rfl⟩
  obtain ⟨firstAtom, firstOfficial, _firstNotParent⟩ :=
    input.eq_extend_zero_and_not_parent_of_mem_executableOfficialCIPChildren
      endpointCursor.occurrence.1.node firstNode
      (List.fst_mem_of_mem_zipIdx firstAtSlot) firstPhysicalNode
  obtain ⟨secondAtom, secondOfficial, _secondNotParent⟩ :=
    input.eq_extend_zero_and_not_parent_of_mem_executableOfficialCIPChildren
      endpointCursor.occurrence.1.node secondNode
      (List.fst_mem_of_mem_zipIdx secondAtSlot) secondPhysicalNode
  have firstAtomIdentity : firstAtom = reference := by
    have observed := congrArg OfficialCIPNode.current? firstOfficial
    rw [← firstNodeIdentity, firstCurrent] at observed
    simpa using observed.symm
  have secondAtomIdentity : secondAtom = reference := by
    have observed := congrArg OfficialCIPNode.current? secondOfficial
    rw [← secondNodeIdentity, secondCurrent] at observed
    simpa using observed.symm
  subst firstAtom
  subst secondAtom
  have nodeIdentity : firstNode = secondNode :=
    firstOfficial.trans secondOfficial.symm
  have secondAtFirstNode : (firstNode, secondSlot) ∈
      (input.executableOfficialCIPChildren
        endpointCursor.occurrence.1.node).zipIdx := by
    rw [nodeIdentity]
    exact secondAtSlot
  have slotIdentity : firstSlot = secondSlot :=
    input.physical_executableOfficialCIPChild_slot_unique
      endpointCursor.occurrence.1.node firstNode firstSlot secondSlot
      firstAtSlot secondAtFirstNode firstPhysicalNode
  have frameIdentity : first.occurrence.1 = second.occurrence.1 :=
    input.declarativeLocalizedOccurrence_functional_at_root_address
      ((input.mem_localizedOccurrences_iff fuel first.occurrence.1).mp
        first.occurrence.2)
      ((input.mem_localizedOccurrences_iff fuel second.occurrence.1).mp
        second.occurrence.2)
      (firstRoot.trans secondRoot.symm)
      (by rw [firstAddress, secondAddress, slotIdentity])
  apply LocalizedRerootCursor.ext input
  · exact Subtype.ext frameIdentity
  · exact (childrenDerived.2 first firstPresent).trans
      (childrenDerived.2 second secondPresent).symm

/-- A physical graph reference below positive carrier depth is selected canonically at every
root-or-forward endpoint cursor.  Existence comes from exact official expansion; uniqueness comes
from physical zero-copy sibling uniqueness, so ring-closing references are included while
multiple-bond duplicate copies cannot create a false second candidate. -/
theorem exists_canonicalLocalizedRule3ReferenceCursor_of_real_outward
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (endpointCursor : input.LocalizedRerootCursor fuel)
    (endpoint reference : input.Atom)
    (real : endpointCursor.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (current : endpointCursor.occurrence.1.node.current? = some endpoint)
    (positive : 0 < endpointCursor.occurrence.1.remaining)
    (adjacent : input.moleculeGraph.Adj endpoint reference)
    (notParent : endpointCursor.occurrence.1.node.parent? ≠ some reference)
    (notIncoming : ∀ slot,
      (endpointCursor.occurrence.1.node.extend reference 0, slot) ∈
          (input.executableOfficialCIPChildren
            endpointCursor.occurrence.1.node).zipIdx →
      ∀ previous, endpointCursor.previous? = some previous →
        endpointCursor.occurrence.1.address ++ [slot] ≠ previous.1.address)
    (endpointShape :
      endpointCursor.occurrence.1.address = [] ∨
        ∃ previous incomingSlot,
          endpointCursor.previous? = some previous ∧
            endpointCursor.occurrence.1.address =
              previous.1.address ++ [incomingSlot]) :
    ∃ cursor,
      input.CanonicalLocalizedRule3ReferenceCursor
        endpointCursor cursor reference := by
  obtain ⟨cursor, children, childrenComputed, childrenDerived, cursorPresent,
      cursorCurrent, cursorPhysical, cursorPrevious⟩ :=
    input.exists_declarativeLocalizedRule3ReferenceCursor_of_real_outward
      endpointCursor endpoint reference real current positive adjacent notParent notIncoming
  have cursorIntended : cursor.occurrence.1 ∈
      input.intendedLocalizedRerootChildFrames endpointCursor := by
    rw [← childrenDerived.1]
    exact List.mem_map.mpr ⟨cursor, cursorPresent, rfl⟩
  have cursorOutward :=
    input.address_eq_append_singleton_of_mem_intended_of_endpoint_shape
      endpointCursor endpointShape cursor.occurrence.1 cursorIntended
  refine ⟨cursor, children, childrenComputed, childrenDerived, cursorPresent,
    cursorCurrent, cursorPhysical, cursorPrevious, ?_⟩
  intro candidate candidatePresent candidateCurrent candidatePhysical
  have candidateIntended : candidate.occurrence.1 ∈
      input.intendedLocalizedRerootChildFrames endpointCursor := by
    rw [← childrenDerived.1]
    exact List.mem_map.mpr ⟨candidate, candidatePresent, rfl⟩
  have candidateOutward :=
    input.address_eq_append_singleton_of_mem_intended_of_endpoint_shape
      endpointCursor endpointShape candidate.occurrence.1 candidateIntended
  exact input.localizedRule3PhysicalReferenceCursor_unique_of_outward
    endpointCursor candidate cursor reference children childrenDerived
    candidatePresent cursorPresent candidateCurrent cursorCurrent
    candidatePhysical cursorPhysical candidateOutward cursorOutward

/-- Singleton-checked occurrence-local reference lookup is exactly the canonical unique physical
reference relation. -/
theorem localizedRule3ReferenceCursor?_eq_some_iff
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (endpointCursor cursor : input.LocalizedRerootCursor fuel)
    (reference : input.Atom) :
    input.localizedRule3ReferenceCursor? endpointCursor reference = some cursor ↔
      input.CanonicalLocalizedRule3ReferenceCursor
        endpointCursor cursor reference := by
  constructor
  · intro computed
    have derived := input.localizedRule3ReferenceCursor?_sound
      endpointCursor cursor reference computed
    rcases derived with ⟨children, childrenComputed, exactChildren, cursorPresent,
      cursorCurrent, cursorPhysical, cursorPrevious⟩
    have candidatesIdentity :
        input.localizedRule3ReferenceCursorCandidates children reference = [cursor] := by
      unfold localizedRule3ReferenceCursor? at computed
      rw [childrenComputed] at computed
      generalize candidateListIdentity :
          input.localizedRule3ReferenceCursorCandidates children reference = candidates
            at computed
      cases candidates with
      | nil => simp [candidateListIdentity] at computed
      | cons selected rest =>
          cases rest with
          | nil =>
              simp [candidateListIdentity] at computed
              simp [computed]
          | cons next more => simp [candidateListIdentity] at computed
    refine ⟨children, childrenComputed, exactChildren, cursorPresent, cursorCurrent,
      cursorPhysical, cursorPrevious, ?_⟩
    intro candidate candidatePresent candidateCurrent candidatePhysical
    have candidateFiltered : candidate ∈
        input.localizedRule3ReferenceCursorCandidates children reference := by
      rw [localizedRule3ReferenceCursorCandidates, List.mem_filter]
      refine ⟨candidatePresent, ?_⟩
      simp [candidateCurrent,
        (localizedRule3PhysicalReferenceProvenance_eq_true_iff
          candidate.occurrence.1.node.provenance).mpr candidatePhysical]
    rw [candidatesIdentity] at candidateFiltered
    simpa using candidateFiltered
  · rintro ⟨children, childrenComputed, exactChildren, cursorPresent,
      cursorCurrent, cursorPhysical, _cursorPrevious, unique⟩
    have cursorFiltered : cursor ∈
        input.localizedRule3ReferenceCursorCandidates children reference := by
      rw [localizedRule3ReferenceCursorCandidates, List.mem_filter]
      refine ⟨cursorPresent, ?_⟩
      simp [cursorCurrent,
        (localizedRule3PhysicalReferenceProvenance_eq_true_iff
          cursor.occurrence.1.node.provenance).mpr cursorPhysical]
    have candidatesNodup :
        (input.localizedRule3ReferenceCursorCandidates children reference).Nodup := by
      unfold localizedRule3ReferenceCursorCandidates
      exact (input.localizedRerootChildren_nodup
        endpointCursor children exactChildren).filter _
    have sameMembers : ∀ candidate,
        candidate ∈ input.localizedRule3ReferenceCursorCandidates children reference ↔
          candidate ∈ [cursor] := by
      intro candidate
      constructor
      · intro candidateFiltered
        have filtered := List.mem_filter.mp candidateFiltered
        have conditions :
            candidate.occurrence.1.node.current? = some reference ∧
              localizedRule3PhysicalReferenceProvenance
                candidate.occurrence.1.node.provenance = true := by
          simpa [localizedRule3ReferenceCursorCandidates] using filtered.2
        have candidatePhysical :=
          (localizedRule3PhysicalReferenceProvenance_eq_true_iff
            candidate.occurrence.1.node.provenance).mp conditions.2
        simp [unique candidate filtered.1 conditions.1 candidatePhysical]
      · intro candidateSingleton
        simp only [List.mem_singleton] at candidateSingleton
        subst candidate
        exact cursorFiltered
    have candidatePermutation :
        List.Perm (input.localizedRule3ReferenceCursorCandidates children reference)
          [cursor] :=
      (List.perm_ext_iff_of_nodup candidatesNodup (by simp)).mpr sameMembers
    have candidatesIdentity :
        input.localizedRule3ReferenceCursorCandidates children reference = [cursor] :=
      List.perm_singleton.mp candidatePermutation
    unfold localizedRule3ReferenceCursor?
    simp [childrenComputed, candidatesIdentity]

/-- A canonical physical reference cursor is path-valid for every reroot fuel theorem: its stored
incoming coordinate is exactly the endpoint cursor from whose uncut neighborhood it was selected. -/
theorem CanonicalLocalizedRule3ReferenceCursor.valid
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (endpointCursor cursor : input.LocalizedRerootCursor fuel)
    (reference : input.Atom)
    (canonical : input.CanonicalLocalizedRule3ReferenceCursor
      endpointCursor cursor reference) :
    input.LocalizedRerootCursorValid cursor := by
  rcases canonical with ⟨children, _childrenComputed, exactChildren, cursorPresent,
    _cursorCurrent, _cursorPhysical, cursorPrevious, _unique⟩
  have framePresent : cursor.occurrence.1 ∈
      input.intendedLocalizedRerootChildFrames endpointCursor := by
    rw [← exactChildren.1]
    exact List.mem_map.mpr ⟨cursor, cursorPresent, rfl⟩
  have neighborPresent := input.mem_localizedRerootNeighborFrames_of_mem_intended
    endpointCursor cursor.occurrence.1 framePresent
  unfold LocalizedRerootCursorValid
  rw [cursorPrevious]
  exact neighborPresent

/-- Ring closure is explicitly an admitted physical reference representation rather than being
discarded as an ordinary duplicate copy. -/
theorem localizedRule3ReferenceCursor?_ringDuplicate_supported
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (endpointCursor cursor : input.LocalizedRerootCursor fuel)
    (reference : input.Atom) (distance : Nat)
    (computed : input.localizedRule3ReferenceCursor?
      endpointCursor reference = some cursor)
    (ring : cursor.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.ringDuplicate distance) :
    input.DeclarativeLocalizedRule3ReferenceCursor endpointCursor cursor reference ∧
      LocalizedRule3PhysicalReferenceProvenance
        cursor.occurrence.1.node.provenance := by
  refine ⟨input.localizedRule3ReferenceCursor?_sound
    endpointCursor cursor reference computed, ?_⟩
  simp [ring, LocalizedRule3PhysicalReferenceProvenance]

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
