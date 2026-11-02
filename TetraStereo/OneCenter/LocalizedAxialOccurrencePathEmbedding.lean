import TetraStereo.OneCenter.LocalizedAxialOccurrenceTopology

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Embedding perceived axial paths into the occurrence carrier

Molecule-level open-axis perception and occurrence-zipper traversal formerly met only at their
first edge.  This module embeds every atom of a declarative perceived path into the exact official
zero-copy occurrence subtree.  Each returned cursor is real, observes the corresponding atom, and
records the preceding occurrence as its incoming cut.
-/

namespace CertifiedLocalizedCIPInput

/-- Proof-bearing occurrence realization of one nonempty molecular axial path. -/
structure LocalizedAxialOccurrencePathEmbedding
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (previousOccurrence firstOccurrence : input.LocalizedCIPOccurrence fuel)
    (atomPath : List input.Atom) where
  cursors : List (input.LocalizedRerootCursor fuel)
  atoms : cursors.map (fun cursor => cursor.occurrence.1.node.current?) =
    atomPath.map some
  allReal : ∀ cursor, cursor ∈ cursors →
    cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom
  allPositive : ∀ cursor, cursor ∈ cursors →
    0 < cursor.occurrence.1.remaining
  incoming : List.IsChain
    (fun left right => right.previous? = some left.occurrence) cursors
  incomingOfficialEdge : ∀ cursor, cursor ∈ cursors →
    ∃ previous slot,
      cursor.previous? = some previous ∧
      cursor.occurrence.1.node.parent? = previous.1.node.current? ∧
      cursor.occurrence.1.root = previous.1.root ∧
      cursor.occurrence.1.address = previous.1.address ++ [slot]
  computedWalk : input.LocalizedRule3ComputedCumulatedAxisWalk cursors
  firstOccurrenceExact : cursors.head?.map (fun cursor => cursor.occurrence) =
    some firstOccurrence
  firstPrevious : ∀ cursor, cursor ∈ cursors.head? →
    cursor.previous? = some previousOccurrence

/-- Every explicit non-axis substituent at an embedded real axis cursor has a canonical
occurrence-local reference cursor.  The embedding supplies real provenance, positive carrier
depth, and the exact incoming parent coordinate; explicit-substituent membership supplies the
physical edge and proves that the reference is not the axis partner. -/
theorem LocalizedAxialOccurrencePathEmbedding.exists_canonicalRule3ReferenceCursor
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {previousOccurrence firstOccurrence : input.LocalizedCIPOccurrence fuel}
    {atomPath : List input.Atom}
    (embedding : input.LocalizedAxialOccurrencePathEmbedding
      fuel previousOccurrence firstOccurrence atomPath)
    (cursor : input.LocalizedRerootCursor fuel)
    (cursorPresent : cursor ∈ embedding.cursors)
    (previous : input.LocalizedCIPOccurrence fuel)
    (endpoint partner reference : input.Atom)
    (previousExact : cursor.previous? = some previous)
    (previousCurrent : previous.1.node.current? = some partner)
    (cursorCurrent : cursor.occurrence.1.node.current? = some endpoint)
    (referencePresent : reference ∈
      input.localizedRule3ExplicitSubstituents endpoint partner) :
    ∃ referenceCursor,
      input.CanonicalLocalizedRule3ReferenceCursor
        cursor referenceCursor reference := by
  obtain ⟨carrierPrevious, incomingSlot, carrierPreviousExact, cursorParent,
      _sameRoot, cursorAddress⟩ :=
    embedding.incomingOfficialEdge cursor cursorPresent
  have previousIdentity : carrierPrevious = previous := by
    exact Option.some.inj (carrierPreviousExact.symm.trans previousExact)
  subst carrierPrevious
  have referenceFacts :=
    (input.mem_localizedRule3ExplicitSubstituents_iff
      endpoint partner reference).mp referencePresent
  apply input.exists_canonicalLocalizedRule3ReferenceCursor_of_real_outward
    cursor endpoint reference
  · exact embedding.allReal cursor cursorPresent
  · exact cursorCurrent
  · exact embedding.allPositive cursor cursorPresent
  · exact referenceFacts.1
  · rw [cursorParent, previousCurrent]
    intro identity
    exact referenceFacts.2 (Option.some.inj identity).symm
  · intro slot _childAtSlot candidatePrevious candidatePreviousExact
    have candidateIdentity : candidatePrevious = previous := by
      exact Option.some.inj (candidatePreviousExact.symm.trans previousExact)
    subst candidatePrevious
    intro addressIdentity
    have lengths := congrArg List.length addressIdentity
    rw [cursorAddress] at lengths
    simp at lengths
  · exact Or.inr ⟨previous, incomingSlot, previousExact, cursorAddress⟩

/-- Every explicit substituent at the canonical initial terminal has a canonical reference
cursor as well.  This is the root-oriented companion to the forward-cursor embedding theorem;
the cut first-axis child cannot be selected because explicit substituents exclude the axis
partner. -/
theorem exists_canonicalRule3ReferenceCursor_evenAxialInitialLeft
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axis : input.LocalizedEvenAxialChain)
    (reference : input.Atom)
    (referencePresent : reference ∈
      input.localizedRule3ExplicitSubstituents
        axis.1.root.terminal axis.1.root.firstAxis) :
    ∃ referenceCursor,
      input.CanonicalLocalizedRule3ReferenceCursor
        (input.localizedEvenAxialInitialPhysicalEndpointCursorFrame
          fuel axis).leftCursor referenceCursor reference := by
  let endpointCursor :=
    (input.localizedEvenAxialInitialPhysicalEndpointCursorFrame fuel axis).leftCursor
  have referenceFacts :=
    (input.mem_localizedRule3ExplicitSubstituents_iff
      axis.1.root.terminal axis.1.root.firstAxis reference).mp referencePresent
  apply input.exists_canonicalLocalizedRule3ReferenceCursor_of_real_outward
    endpointCursor axis.1.root.terminal reference
  · rfl
  · rfl
  · simp [endpointCursor, localizedEvenAxialInitialPhysicalEndpointCursorFrame]
  · exact referenceFacts.1
  · simp [endpointCursor, localizedEvenAxialInitialPhysicalEndpointCursorFrame,
      OfficialCIPNode.parent?, OfficialCIPNode.root]
  · intro slot childAtSlot previous previousExact
    have previousIdentity : previous =
        input.localizedEvenAxialFirstChildOccurrence fuel axis := by
      simpa [endpointCursor, localizedEvenAxialInitialPhysicalEndpointCursorFrame] using
        Option.some.inj previousExact.symm
    subst previous
    intro addressIdentity
    have slotIdentity : slot = input.localizedEvenAxialFirstChildSlot axis := by
      simpa [endpointCursor, localizedEvenAxialInitialPhysicalEndpointCursorFrame] using
        addressIdentity
    have childAtRoot :
        ((OfficialCIPNode.root axis.1.root.terminal).extend reference 0,
            input.localizedEvenAxialFirstChildSlot axis) ∈
          (input.executableOfficialCIPChildren
            (OfficialCIPNode.root axis.1.root.terminal)).zipIdx := by
      simpa [endpointCursor, localizedEvenAxialInitialPhysicalEndpointCursorFrame,
        slotIdentity] using childAtSlot
    have targetIndexed := List.mem_zipIdx childAtRoot
    have canonicalIndexed := List.mem_zipIdx
      (input.localizedEvenAxialFirstChildSlot_mem axis)
    have childIdentity :
        (OfficialCIPNode.root axis.1.root.terminal).extend reference 0 =
          input.localizedEvenAxialFirstChildNode axis.1 := by
      exact targetIndexed.2.2.trans canonicalIndexed.2.2.symm
    have atomIdentity : reference = axis.1.root.firstAxis := by
      have observed := congrArg OfficialCIPNode.current? childIdentity
      simpa [localizedEvenAxialFirstChildNode] using observed
    exact referenceFacts.2 atomIdentity
  · exact Or.inl (by
      simp [endpointCursor, localizedEvenAxialInitialPhysicalEndpointCursorFrame])

/-- Every explicit substituent at the initial terminal of any exact maximal open chain has a
canonical occurrence-local reference cursor.  This parity-neutral form supports both planar odd
cumulenes and axial even cumulenes. -/
theorem exists_canonicalRule3ReferenceCursor_axialRootInitialLeft
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axialRoot : input.LocalizedAxialRoot)
    (reference : input.Atom)
    (referencePresent : reference ∈
      input.localizedRule3ExplicitSubstituents
        axialRoot.1.terminal axialRoot.1.firstAxis) :
    ∃ referenceCursor,
      input.CanonicalLocalizedRule3ReferenceCursor
        (input.localizedAxialRootInitialPhysicalEndpointCursorFrame
          fuel axialRoot).leftCursor referenceCursor reference := by
  let endpointCursor :=
    (input.localizedAxialRootInitialPhysicalEndpointCursorFrame fuel axialRoot).leftCursor
  have referenceFacts :=
    (input.mem_localizedRule3ExplicitSubstituents_iff
      axialRoot.1.terminal axialRoot.1.firstAxis reference).mp referencePresent
  apply input.exists_canonicalLocalizedRule3ReferenceCursor_of_real_outward
    endpointCursor axialRoot.1.terminal reference
  · rfl
  · rfl
  · simp [endpointCursor, localizedAxialRootInitialPhysicalEndpointCursorFrame,
      localizedAxialRootOccurrence, localizedAtomRootOccurrence]
  · exact referenceFacts.1
  · simp [endpointCursor, localizedAxialRootInitialPhysicalEndpointCursorFrame,
      localizedAxialRootOccurrence, localizedAtomRootOccurrence,
      OfficialCIPNode.parent?, OfficialCIPNode.root]
  · intro slot childAtSlot previous previousExact
    have previousIdentity : previous =
        input.localizedAxialRootFirstChildOccurrence fuel axialRoot := by
      simpa [endpointCursor, localizedAxialRootInitialPhysicalEndpointCursorFrame] using
        Option.some.inj previousExact.symm
    subst previous
    intro addressIdentity
    have slotIdentity : slot = input.localizedAxialRootFirstChildSlot axialRoot := by
      simpa [endpointCursor, localizedAxialRootInitialPhysicalEndpointCursorFrame] using
        addressIdentity
    have childAtRoot :
        ((OfficialCIPNode.root axialRoot.1.terminal).extend reference 0,
            input.localizedAxialRootFirstChildSlot axialRoot) ∈
          (input.executableOfficialCIPChildren
            (OfficialCIPNode.root axialRoot.1.terminal)).zipIdx := by
      simpa [endpointCursor, localizedAxialRootInitialPhysicalEndpointCursorFrame,
        slotIdentity] using childAtSlot
    have targetIndexed := List.mem_zipIdx childAtRoot
    have canonicalIndexed := List.mem_zipIdx
      (input.localizedAxialRootFirstChildSlot_mem axialRoot)
    have childIdentity :
        (OfficialCIPNode.root axialRoot.1.terminal).extend reference 0 =
          input.localizedAxialRootFirstChildNode axialRoot := by
      exact targetIndexed.2.2.trans canonicalIndexed.2.2.symm
    have atomIdentity : reference = axialRoot.1.firstAxis := by
      have observed := congrArg OfficialCIPNode.current? childIdentity
      simpa [localizedAxialRootFirstChildNode] using observed
    exact referenceFacts.2 atomIdentity
  · exact Or.inl (by
      simp [endpointCursor, localizedAxialRootInitialPhysicalEndpointCursorFrame])

private theorem exists_localizedAxialOccurrenceCursorWalk
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat)
    (axialRoot : input.LocalizedAxialRoot)
    {previous current : input.Atom} {seen atomPath : List input.Atom}
    (walk : input.DeclarativeLocalizedAxialChainWalk
      previous current seen atomPath)
    (previousSeen : previous ∈ seen)
    (address : List Nat) (remaining : Nat)
    (node : OfficialCIPNode input.Atom)
    (enough : atomPath.length ≤ remaining)
    (nodeCurrent : node.current? = some current)
    (nodeParent : node.parent? = some previous)
    (nodeHistory : node.history = current :: seen)
    (nodeReal : node.provenance = OfficialCIPNodeProvenance.realAtom)
    (lift : ∀ occurrence,
      input.DeclarativeLocalizedOccurrenceSubtree axialRoot.1.terminal
          address remaining node occurrence →
        input.DeclarativeLocalizedOccurrence carrierFuel occurrence)
    (previousOccurrence : input.LocalizedCIPOccurrence carrierFuel)
    (previousCurrent : previousOccurrence.1.node.current? = some previous)
    (previousRoot : previousOccurrence.1.root = axialRoot.1.terminal)
    (previousAddress : ∃ slot,
      address = previousOccurrence.1.address ++ [slot]) :
    ∃ currentOccurrence,
      currentOccurrence.1 =
          { root := axialRoot.1.terminal
            address := address
            node := node
            remaining := remaining } ∧
        Nonempty (input.LocalizedAxialOccurrencePathEmbedding carrierFuel
          previousOccurrence currentOccurrence atomPath) := by
  classical
  let currentFrame : input.LocalizedCIPOccurrenceFrame :=
    { root := axialRoot.1.terminal
      address := address
      node := node
      remaining := remaining }
  let currentOccurrence : input.LocalizedCIPOccurrence carrierFuel :=
    ⟨currentFrame, (input.mem_localizedOccurrences_iff carrierFuel currentFrame).mpr
      (lift currentFrame
        (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot address remaining node))⟩
  let currentCursor : input.LocalizedRerootCursor carrierFuel :=
    { occurrence := currentOccurrence, previous? := some previousOccurrence }
  induction walk generalizing address remaining node previousOccurrence with
  | @terminal previous current seen forward =>
      refine ⟨currentOccurrence, rfl, ⟨
        { cursors := [currentCursor]
          atoms := by simp [currentCursor, currentOccurrence, currentFrame, nodeCurrent]
          allReal := by
            intro cursor present
            simp only [List.mem_singleton] at present
            subst cursor
            simpa [currentCursor, currentOccurrence, currentFrame] using nodeReal
          allPositive := by
            intro cursor present
            simp only [List.mem_singleton] at present
            subst cursor
            have positive : 0 < remaining := by simpa using enough
            simpa [currentCursor, currentOccurrence, currentFrame] using positive
          incoming := List.isChain_singleton _
          incomingOfficialEdge := by
            intro cursor present
            simp only [List.mem_singleton] at present
            subst cursor
            rcases previousAddress with ⟨slot, addressIdentity⟩
            exact ⟨previousOccurrence, slot, rfl, by
              simp [currentCursor, currentOccurrence, currentFrame,
                nodeParent, previousCurrent], by
              simpa [currentCursor, currentOccurrence, currentFrame] using previousRoot.symm, by
              simpa [currentCursor, currentOccurrence, currentFrame] using addressIdentity⟩
          computedWalk := by
            rcases previousAddress with ⟨incomingSlot, addressIdentity⟩
            apply LocalizedRule3ComputedCumulatedAxisWalk.terminal
            apply input.localizedRule3AxisTopology?_of_embedded_terminal
              currentCursor previousOccurrence previous current incomingSlot
            · rfl
            · exact previousCurrent
            · simpa [currentCursor, currentOccurrence, currentFrame] using nodeCurrent
            · simpa [currentCursor, currentOccurrence, currentFrame,
                previousCurrent] using nodeParent
            · simpa [currentCursor, currentOccurrence, currentFrame] using previousRoot.symm
            · simpa [currentCursor, currentOccurrence, currentFrame] using addressIdentity
            · exact forward
          firstOccurrenceExact := by
            simp [currentCursor]
          firstPrevious := by
            intro cursor present
            simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at present
            subst cursor
            rfl }⟩⟩
  | @linear previous current seen next tail forward fresh rest inductionHypothesis =>
      have nextPresent : next ∈
          input.localizedAxialForwardNeighbors previous current := by
        simp [forward]
      have doubleBond : input.moleculeGraph.bond current next = 2 :=
        (input.mem_localizedAxialForwardNeighbors_iff
          previous current next).mp nextPresent |>.1
      have nextNeCurrent : next ≠ current := by
        intro same
        subst next
        have impossible : (0 : Nat) = 2 := by
          simpa only [input.moleculeGraph.bond_self] using doubleBond
        exact Nat.noConfusion impossible
      have nextNePrevious : next ≠ previous := by
        intro same
        subst next
        exact fresh previousSeen
      cases remaining with
      | zero =>
          simp at enough
      | succ childRemaining =>
          have childPresent : node.extend next 0 ∈
              input.executableOfficialCIPChildren node :=
            input.extend_zero_mem_executableOfficialCIPChildren_of_real
              node current next nodeReal nodeCurrent
              (by
                show 0 < input.moleculeGraph.bond current next
                rw [doubleBond]
                decide)
              (by
                rw [nodeParent]
                intro equality
                exact nextNePrevious (Option.some.inj equality).symm)
          rw [List.mem_iff_getElem] at childPresent
          rcases childPresent with ⟨slot, slotValid, childAtSlot⟩
          have childZipPresent : (node.extend next 0, slot) ∈
              (input.executableOfficialCIPChildren node).zipIdx := by
            rw [List.mem_iff_getElem]
            refine ⟨slot, by simpa using slotValid, ?_⟩
            simp [childAtSlot]
          have childReal : (node.extend next 0).provenance =
              OfficialCIPNodeProvenance.realAtom := by
            have nextFreshHistory : next ∉ current :: seen := by
              simp [nextNeCurrent, fresh]
            simp [OfficialCIPNode.extend, OfficialCIPNode.childProvenance,
              nodeHistory, nextFreshHistory]
          have tailEnough : tail.length ≤ childRemaining := by
            simp only [List.length_cons] at enough
            omega
          let childLift := fun occurrence
              (derived : input.DeclarativeLocalizedOccurrenceSubtree
                axialRoot.1.terminal (address ++ [slot]) childRemaining
                  (node.extend next 0) occurrence) =>
            lift occurrence
              (DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
                childZipPresent derived)
          obtain ⟨firstTailOccurrence, firstTailFrame, ⟨tailEmbedding⟩⟩ :=
            inductionHypothesis (by simp) (address ++ [slot]) childRemaining
              (node.extend next 0) tailEnough rfl
              (by simp [OfficialCIPNode.parent?, OfficialCIPNode.extend, nodeHistory])
              (by simp [OfficialCIPNode.extend, nodeHistory]) childReal childLift
              currentOccurrence
              (by simpa [currentOccurrence, currentFrame] using nodeCurrent)
              (by simp [currentOccurrence, currentFrame])
              ⟨slot, by simp [currentOccurrence, currentFrame]⟩
          refine ⟨currentOccurrence, rfl, ⟨
            { cursors := currentCursor :: tailEmbedding.cursors
              atoms := by
                simp only [List.map_cons]
                change node.current? ::
                    tailEmbedding.cursors.map
                      (fun cursor => cursor.occurrence.1.node.current?) =
                  some current :: tail.map some
                rw [tailEmbedding.atoms]
                simp [nodeCurrent]
              allReal := by
                intro cursor present
                rw [List.mem_cons] at present
                rcases present with identity | tailPresent
                · subst cursor
                  simpa [currentCursor, currentOccurrence, currentFrame] using nodeReal
                · exact tailEmbedding.allReal cursor tailPresent
              allPositive := by
                intro cursor present
                rw [List.mem_cons] at present
                rcases present with identity | tailPresent
                · subst cursor
                  simp [currentCursor, currentOccurrence, currentFrame]
                · exact tailEmbedding.allPositive cursor tailPresent
              incoming := by
                apply tailEmbedding.incoming.cons
                intro first firstPresent
                simpa [currentCursor] using
                  tailEmbedding.firstPrevious first firstPresent
              incomingOfficialEdge := by
                intro cursor present
                rw [List.mem_cons] at present
                rcases present with identity | tailPresent
                · subst cursor
                  rcases previousAddress with ⟨previousSlot, addressIdentity⟩
                  exact ⟨previousOccurrence, previousSlot, rfl, by
                    simp [currentCursor, currentOccurrence, currentFrame,
                      nodeParent, previousCurrent], by
                    simpa [currentCursor, currentOccurrence, currentFrame] using previousRoot.symm, by
                    simpa [currentCursor, currentOccurrence, currentFrame] using addressIdentity⟩
                · exact tailEmbedding.incomingOfficialEdge cursor tailPresent
              computedWalk := by
                have currentTopology : ∀ tailCursor,
                    tailCursor ∈ tailEmbedding.cursors.head? →
                    input.localizedRule3AxisTopology? currentCursor =
                      some (.linear tailCursor) := by
                  intro tailCursor headPresent
                  have headIdentity : tailEmbedding.cursors.head? = some tailCursor := by
                    simpa [Option.mem_def] using headPresent
                  have mappedHead :
                      tailEmbedding.cursors.head?.map
                          (fun cursor => cursor.occurrence) =
                        some tailCursor.occurrence := by
                    rw [headIdentity]
                    rfl
                  rw [tailEmbedding.firstOccurrenceExact] at mappedHead
                  have occurrenceIdentity : tailCursor.occurrence = firstTailOccurrence :=
                    Option.some.inj mappedHead.symm
                  have tailPrevious : tailCursor.previous? = some currentOccurrence := by
                    simpa using tailEmbedding.firstPrevious tailCursor headPresent
                  have tailRoot : tailCursor.occurrence.1.root = currentOccurrence.1.root := by
                    rw [occurrenceIdentity, firstTailFrame]
                  have tailAddress : tailCursor.occurrence.1.address =
                      currentOccurrence.1.address ++ [slot] := by
                    rw [occurrenceIdentity, firstTailFrame]
                  have tailReal : tailCursor.occurrence.1.node.provenance =
                      OfficialCIPNodeProvenance.realAtom := by
                    rw [occurrenceIdentity, firstTailFrame]
                    exact childReal
                  have tailCurrent : tailCursor.occurrence.1.node.current? = some next := by
                    rw [occurrenceIdentity, firstTailFrame]
                    rfl
                  rcases previousAddress with ⟨incomingSlot, addressIdentity⟩
                  apply input.localizedRule3AxisTopology?_of_embedded_linear
                    currentCursor tailCursor previousOccurrence previous current next
                      incomingSlot slot
                  · rfl
                  · exact previousCurrent
                  · simpa [currentCursor, currentOccurrence, currentFrame] using nodeCurrent
                  · simpa [currentCursor, currentOccurrence, currentFrame,
                      previousCurrent] using nodeParent
                  · simpa [currentCursor, currentOccurrence, currentFrame] using previousRoot.symm
                  · simpa [currentCursor, currentOccurrence, currentFrame] using addressIdentity
                  · simpa [currentCursor, currentOccurrence, currentFrame] using nodeReal
                  · simpa [currentCursor] using tailPrevious
                  · simpa [currentCursor] using tailRoot
                  · simpa [currentCursor] using tailAddress
                  · exact tailReal
                  · exact tailCurrent
                  · exact forward
                exact tailEmbedding.computedWalk.prepend input currentCursor currentTopology
              firstOccurrenceExact := by simp [currentCursor]
              firstPrevious := by
                intro cursor present
                simp only [List.head?_cons, Option.mem_def,
                  Option.some.injEq] at present
                subst cursor
                rfl }⟩⟩

/-- Every independently valid maximal open-chain path embeds completely into the family-neutral
atom-rooted occurrence carrier whenever the selected carrier depth covers its non-root tail. -/
theorem exists_localizedAxialRootOccurrencePathEmbedding
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat)
    (axialRoot : input.LocalizedAxialRoot) (path : List input.Atom)
    (derived : input.DeclarativeLocalizedAxialChainFromRoot axialRoot.1 path)
    (enough : path.length ≤ carrierFuel + 1) :
    ∃ _embedding : input.LocalizedAxialOccurrencePathEmbedding carrierFuel
        (input.localizedAxialRootOccurrence carrierFuel axialRoot)
        (input.localizedAxialRootFirstChildOccurrence carrierFuel axialRoot)
        path.tail,
      True := by
  classical
  rcases derived with ⟨_rootValid, tail, pathIdentity, walk⟩
  have tailIdentity : path.tail = tail := by
    simp [pathIdentity]
  have tailEnough : tail.length ≤ carrierFuel := by
    rw [pathIdentity] at enough
    simpa using enough
  let slot := input.localizedAxialRootFirstChildSlot axialRoot
  let node := input.localizedAxialRootFirstChildNode axialRoot
  let lift : ∀ occurrence,
      input.DeclarativeLocalizedOccurrenceSubtree
          axialRoot.1.terminal [slot] carrierFuel node occurrence →
        input.DeclarativeLocalizedOccurrence carrierFuel occurrence := by
    intro occurrence below
    have full : input.DeclarativeLocalizedOccurrenceSubtree
        axialRoot.1.terminal [] (carrierFuel + 1)
          (OfficialCIPNode.root axialRoot.1.terminal) occurrence := by
      simpa using
        (DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
          (input.localizedAxialRootFirstChildSlot_mem axialRoot) below)
    have rootIdentity : occurrence.root = axialRoot.1.terminal :=
      input.declarativeLocalizedOccurrenceSubtree_root_eq full
    simpa [DeclarativeLocalizedOccurrence,
      DeclarativeLocalizedOccurrenceAtAtom, rootIdentity] using full
  obtain ⟨firstOccurrence, firstFrame, ⟨embedding⟩⟩ :=
    input.exists_localizedAxialOccurrenceCursorWalk carrierFuel axialRoot walk
      (by simp) [slot] carrierFuel node tailEnough rfl rfl rfl
      (input.localizedAxialRootFirstChildOccurrence_physical carrierFuel axialRoot).1
      lift (input.localizedAxialRootOccurrence carrierFuel axialRoot)
      (by rfl)
      (by rfl)
      ⟨slot, by simp [localizedAxialRootOccurrence,
        localizedAtomRootOccurrence]⟩
  have firstIdentity : firstOccurrence =
      input.localizedAxialRootFirstChildOccurrence carrierFuel axialRoot := by
    apply Subtype.ext
    rw [firstFrame]
    rfl
  subst firstOccurrence
  rw [tailIdentity]
  exact ⟨embedding, trivial⟩

/-- The molecule-size carrier depth is sufficient for every independently valid maximal open
chain, independent of its later descriptor-family parity. -/
theorem exists_localizedAxialRootOccurrencePathEmbedding_at_atomCount
    (input : CertifiedLocalizedCIPInput)
    (axialRoot : input.LocalizedAxialRoot) (path : List input.Atom)
    (derived : input.DeclarativeLocalizedAxialChainFromRoot axialRoot.1 path) :
    ∃ _embedding : input.LocalizedAxialOccurrencePathEmbedding
        input.certified.input.molecule.atomCount
        (input.localizedAxialRootOccurrence
          input.certified.input.molecule.atomCount axialRoot)
        (input.localizedAxialRootFirstChildOccurrence
          input.certified.input.molecule.atomCount axialRoot)
        path.tail,
      True := by
  apply input.exists_localizedAxialRootOccurrencePathEmbedding
    input.certified.input.molecule.atomCount axialRoot path derived
  have bounded :=
    (DeclarativeLocalizedAxialChainFromRoot.path_nodup input derived).length_le_card
  have pathBound : path.length ≤ input.certified.input.molecule.atomCount := by
    simpa [CertifiedLocalizedCIPInput.Atom] using bounded
  omega

/-- The generic proof-bearing occurrence embedding executes exactly as the production Rule-3
cumulated-axis walker at atom-count carrier depth. -/
theorem exists_localizedAxialRootOccurrencePathEmbedding_executes_at_atomCount
    (input : CertifiedLocalizedCIPInput)
    (axialRoot : input.LocalizedAxialRoot) (path : List input.Atom)
    (derived : input.DeclarativeLocalizedAxialChainFromRoot axialRoot.1 path) :
    ∃ embedding : input.LocalizedAxialOccurrencePathEmbedding
        input.certified.input.molecule.atomCount
        (input.localizedAxialRootOccurrence
          input.certified.input.molecule.atomCount axialRoot)
        (input.localizedAxialRootFirstChildOccurrence
          input.certified.input.molecule.atomCount axialRoot)
        path.tail,
      input.walkLocalizedRule3CumulatedAxis?
          (input.localizedRule3CumulatedTraversalFuel
            input.certified.input.molecule.atomCount)
          (input.localizedAxialRootInitialPhysicalEndpointCursorFrame
            input.certified.input.molecule.atomCount axialRoot).rightCursor =
        some embedding.cursors := by
  obtain ⟨embedding, _trivial⟩ :=
    input.exists_localizedAxialRootOccurrencePathEmbedding_at_atomCount
      axialRoot path derived
  have bounded :=
    (DeclarativeLocalizedAxialChainFromRoot.path_nodup input derived).length_le_card
  have pathBound : path.length ≤ input.certified.input.molecule.atomCount := by
    simpa [CertifiedLocalizedCIPInput.Atom] using bounded
  have cursorLength : embedding.cursors.length = path.tail.length := by
    have mappedLengths := congrArg List.length embedding.atoms
    simpa using mappedLengths
  have tailBound : path.tail.length ≤ input.certified.input.molecule.atomCount := by
    simp only [List.length_tail]
    omega
  have enough : embedding.cursors.length ≤
      input.localizedRule3CumulatedTraversalFuel
        input.certified.input.molecule.atomCount + 1 := by
    rw [cursorLength]
    unfold localizedRule3CumulatedTraversalFuel
      localizedOccurrenceRerootEvaluationFuel
    omega
  obtain ⟨first, firstHead, computed⟩ :=
    embedding.computedWalk.executes input
      (input.localizedRule3CumulatedTraversalFuel
        input.certified.input.molecule.atomCount) enough
  have firstPresent : first ∈ embedding.cursors.head? := by
    simp [firstHead]
  have firstOccurrence : first.occurrence =
      input.localizedAxialRootFirstChildOccurrence
        input.certified.input.molecule.atomCount axialRoot := by
    have mappedHead : embedding.cursors.head?.map
        (fun cursor => cursor.occurrence) = some first.occurrence := by
      rw [firstHead]
      rfl
    rw [embedding.firstOccurrenceExact] at mappedHead
    exact Option.some.inj mappedHead.symm
  have firstPrevious : first.previous? = some
      (input.localizedAxialRootOccurrence
        input.certified.input.molecule.atomCount axialRoot) :=
    embedding.firstPrevious first firstPresent
  have firstIdentity : first =
      (input.localizedAxialRootInitialPhysicalEndpointCursorFrame
        input.certified.input.molecule.atomCount axialRoot).rightCursor := by
    apply LocalizedRerootCursor.ext input
    · simpa [localizedAxialRootInitialPhysicalEndpointCursorFrame] using firstOccurrence
    · simpa [localizedAxialRootInitialPhysicalEndpointCursorFrame] using firstPrevious
  subst first
  exact ⟨embedding, computed⟩

/-- Every perceived canonical open even axis embeds completely into its official occurrence
carrier whenever the selected carrier depth covers the non-root atom tail.  The inclusive bound
also leaves positive expansion depth at every embedded physical axis atom. -/
theorem exists_localizedEvenAxialOccurrencePathEmbedding
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat)
    (axis : input.LocalizedEvenAxialChain)
    (enough : axis.1.path.length ≤ carrierFuel + 1) :
    ∃ _embedding : input.LocalizedAxialOccurrencePathEmbedding carrierFuel
        (input.localizedEvenAxialRootOccurrence carrierFuel axis)
        (input.localizedEvenAxialFirstChildOccurrence carrierFuel axis)
        axis.1.path.tail,
      True := by
  classical
  have axisValid := (input.mem_localizedEvenAxialChains_iff axis.1).mp axis.2
  rcases axisValid.1 with ⟨rootValid, tail, pathIdentity, walk⟩
  have tailIdentity : axis.1.path.tail = tail := by
    simp [pathIdentity]
  have tailEnough : tail.length ≤ carrierFuel := by
    rw [pathIdentity] at enough
    simpa using enough
  let axialRoot : input.LocalizedAxialRoot :=
    ⟨axis.1.root,
      (input.mem_localizedAxialRootCandidates_iff axis.1.root).mpr rootValid⟩
  let slot := input.localizedEvenAxialFirstChildSlot axis
  let node := input.localizedEvenAxialFirstChildNode axis.1
  let lift : ∀ occurrence,
      input.DeclarativeLocalizedOccurrenceSubtree
          axis.1.root.terminal [slot] carrierFuel node occurrence →
        input.DeclarativeLocalizedOccurrence carrierFuel occurrence := by
    intro occurrence derived
    have full : input.DeclarativeLocalizedOccurrenceSubtree
        axis.1.root.terminal [] (carrierFuel + 1)
          (OfficialCIPNode.root axis.1.root.terminal) occurrence := by
      simpa using
        (DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
          (input.localizedEvenAxialFirstChildSlot_mem axis) derived)
    have rootIdentity : occurrence.root = axis.1.root.terminal :=
      input.declarativeLocalizedOccurrenceSubtree_root_eq full
    simpa [DeclarativeLocalizedOccurrence,
      DeclarativeLocalizedOccurrenceAtAtom, rootIdentity] using full
  obtain ⟨firstOccurrence, firstFrame, ⟨embedding⟩⟩ :=
    input.exists_localizedAxialOccurrenceCursorWalk carrierFuel axialRoot walk
      (by simp) [slot] carrierFuel node tailEnough rfl rfl rfl
      (input.localizedEvenAxialFirstChildOccurrence_physical carrierFuel axis).1
      lift (input.localizedEvenAxialRootOccurrence carrierFuel axis)
      (by rfl)
      (by rfl)
      ⟨slot, by simp [localizedEvenAxialRootOccurrence]⟩
  have firstIdentity : firstOccurrence =
      input.localizedEvenAxialFirstChildOccurrence carrierFuel axis := by
    apply Subtype.ext
    rw [firstFrame]
    rfl
  subst firstOccurrence
  rw [tailIdentity]
  exact ⟨embedding, trivial⟩

/-- The molecule-size carrier depth is sufficient for every perceived canonical open even axis. -/
theorem exists_localizedEvenAxialOccurrencePathEmbedding_at_atomCount
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedEvenAxialChain) :
    ∃ _embedding : input.LocalizedAxialOccurrencePathEmbedding
        input.certified.input.molecule.atomCount
        (input.localizedEvenAxialRootOccurrence
          input.certified.input.molecule.atomCount axis)
        (input.localizedEvenAxialFirstChildOccurrence
          input.certified.input.molecule.atomCount axis)
        axis.1.path.tail,
      True := by
  apply input.exists_localizedEvenAxialOccurrencePathEmbedding
  have axisValid := (input.mem_localizedEvenAxialChains_iff axis.1).mp axis.2
  have bounded :=
    DeclarativeLocalizedEvenAxialChainFrame.path_length_le_atomCount input axisValid
  omega

/-- The proof-bearing occurrence embedding itself is exactly the production Rule-3 zipper walk
at the atom-count carrier. -/
theorem exists_localizedEvenAxialOccurrencePathEmbedding_executes_at_atomCount
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedEvenAxialChain) :
    ∃ embedding : input.LocalizedAxialOccurrencePathEmbedding
        input.certified.input.molecule.atomCount
        (input.localizedEvenAxialRootOccurrence
          input.certified.input.molecule.atomCount axis)
        (input.localizedEvenAxialFirstChildOccurrence
          input.certified.input.molecule.atomCount axis)
        axis.1.path.tail,
      input.walkLocalizedRule3CumulatedAxis?
          (input.localizedRule3CumulatedTraversalFuel
            input.certified.input.molecule.atomCount)
          (input.localizedEvenAxialInitialPhysicalEndpointCursorFrame
            input.certified.input.molecule.atomCount axis).rightCursor =
        some embedding.cursors := by
  obtain ⟨embedding, _trivial⟩ :=
    input.exists_localizedEvenAxialOccurrencePathEmbedding_at_atomCount axis
  have axisValid := (input.mem_localizedEvenAxialChains_iff axis.1).mp axis.2
  have pathBound :=
    DeclarativeLocalizedEvenAxialChainFrame.path_length_le_atomCount input axisValid
  have cursorLength : embedding.cursors.length = axis.1.path.tail.length := by
    have mappedLengths := congrArg List.length embedding.atoms
    simpa using mappedLengths
  have tailBound : axis.1.path.tail.length ≤
      input.certified.input.molecule.atomCount := by
    simp only [List.length_tail]
    omega
  have enough : embedding.cursors.length ≤
      input.localizedRule3CumulatedTraversalFuel
        input.certified.input.molecule.atomCount + 1 := by
    rw [cursorLength]
    unfold localizedRule3CumulatedTraversalFuel
      localizedOccurrenceRerootEvaluationFuel
    omega
  obtain ⟨first, firstHead, computed⟩ :=
    embedding.computedWalk.executes input
      (input.localizedRule3CumulatedTraversalFuel
        input.certified.input.molecule.atomCount) enough
  have firstPresent : first ∈ embedding.cursors.head? := by
    simp [firstHead]
  have firstOccurrence : first.occurrence =
      input.localizedEvenAxialFirstChildOccurrence
        input.certified.input.molecule.atomCount axis := by
    have mappedHead : embedding.cursors.head?.map
        (fun cursor => cursor.occurrence) = some first.occurrence := by
      rw [firstHead]
      rfl
    rw [embedding.firstOccurrenceExact] at mappedHead
    exact Option.some.inj mappedHead.symm
  have firstPrevious : first.previous? = some
      (input.localizedEvenAxialRootOccurrence
        input.certified.input.molecule.atomCount axis) :=
    embedding.firstPrevious first firstPresent
  have firstIdentity : first =
      (input.localizedEvenAxialInitialPhysicalEndpointCursorFrame
        input.certified.input.molecule.atomCount axis).rightCursor := by
    apply LocalizedRerootCursor.ext input
    · simpa [localizedEvenAxialInitialPhysicalEndpointCursorFrame] using firstOccurrence
    · simpa [localizedEvenAxialInitialPhysicalEndpointCursorFrame] using firstPrevious
  subst first
  exact ⟨embedding, computed⟩

/-- For every perceived canonical open even axis, the production Rule-3 zipper walk executes
unconditionally at the atom-count carrier and its cursor observations are exactly the perceived
non-root molecular path.  No separate global nonbranching-resolution premise remains here. -/
theorem exists_walkLocalizedRule3CumulatedAxis?_evenAxial_at_atomCount
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedEvenAxialChain) :
    ∃ cursorPath,
      input.walkLocalizedRule3CumulatedAxis?
          (input.localizedRule3CumulatedTraversalFuel
            input.certified.input.molecule.atomCount)
          (input.localizedEvenAxialInitialPhysicalEndpointCursorFrame
            input.certified.input.molecule.atomCount axis).rightCursor =
        some cursorPath ∧
      cursorPath.map (fun cursor => cursor.occurrence.1.node.current?) =
        axis.1.path.tail.map some := by
  obtain ⟨embedding, computed⟩ :=
    input.exists_localizedEvenAxialOccurrencePathEmbedding_executes_at_atomCount axis
  exact ⟨embedding.cursors, computed, embedding.atoms⟩

/-- The generic terminal-to-terminal constructor retains the proof-bearing occurrence embedding
from which its exact rightward cursor path was built. -/
theorem exists_localizedRule3CumulatedEndpointCursorFrameWithEmbedding_evenAxial_at_atomCount
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedEvenAxialChain) :
    ∃ frame : input.LocalizedRule3CumulatedEndpointCursorFrame
        input.certified.input.molecule.atomCount,
      ∃ embedding : input.LocalizedAxialOccurrencePathEmbedding
        input.certified.input.molecule.atomCount
        (input.localizedEvenAxialRootOccurrence
          input.certified.input.molecule.atomCount axis)
        (input.localizedEvenAxialFirstChildOccurrence
          input.certified.input.molecule.atomCount axis)
        axis.1.path.tail,
      input.localizedRule3CumulatedEndpointCursorFrame?
          (input.localizedRule3CumulatedTraversalFuel
            input.certified.input.molecule.atomCount)
          (input.localizedEvenAxialFirstChildOccurrence
            input.certified.input.molecule.atomCount axis) = some frame ∧
      frame.initial =
        input.localizedEvenAxialInitialPhysicalEndpointCursorFrame
          input.certified.input.molecule.atomCount axis ∧
      frame.rightward = embedding.cursors ∧
      frame.rightCursor ∈ embedding.cursors ∧
      frame.rightPartnerCursor ∈ embedding.cursors ∧
      frame.rightCursor.previous? = some frame.rightPartnerCursor.occurrence := by
  let carrierFuel := input.certified.input.molecule.atomCount
  let traversalFuel := input.localizedRule3CumulatedTraversalFuel carrierFuel
  let initial := input.localizedEvenAxialInitialPhysicalEndpointCursorFrame
    carrierFuel axis
  obtain ⟨embedding, walkComputed⟩ :=
    input.exists_localizedEvenAxialOccurrencePathEmbedding_executes_at_atomCount axis
  let cursorPath := embedding.cursors
  have atoms : cursorPath.map
      (fun cursor => cursor.occurrence.1.node.current?) =
        axis.1.path.tail.map some := by
    exact embedding.atoms
  have axisValid := (input.mem_localizedEvenAxialChains_iff axis.1).mp axis.2
  have pathLong : 1 < axis.1.path.length - 1 := axisValid.2.1
  have cursorLength : cursorPath.length = axis.1.path.tail.length := by
    have mappedLengths := congrArg List.length atoms
    simpa using mappedLengths
  have cursorPathTwo : 2 ≤ cursorPath.length := by
    rw [cursorLength]
    simp only [List.length_tail]
    exact pathLong
  have currentSome : ∀ cursor, cursor ∈ cursorPath →
      ∃ atom, cursor.occurrence.1.node.current? = some atom := by
    intro cursor present
    have observedPresent : cursor.occurrence.1.node.current? ∈
        cursorPath.map (fun candidate => candidate.occurrence.1.node.current?) :=
      List.mem_map.mpr ⟨cursor, present, rfl⟩
    rw [atoms] at observedPresent
    rw [List.mem_map] at observedPresent
    rcases observedPresent with ⟨atom, _atomPresent, observedIdentity⟩
    exact ⟨atom, observedIdentity.symm⟩
  cases reverseIdentity : cursorPath.reverse with
  | nil =>
      have reverseLength : cursorPath.length = 0 := by
        have := congrArg List.length reverseIdentity
        simpa using this
      omega
  | cons right reverseTail =>
      cases reverseTail with
      | nil =>
          have reverseLength : cursorPath.length = 1 := by
            have := congrArg List.length reverseIdentity
            simpa using this
          omega
      | cons rightPartner more =>
          have rightPresent : right ∈ cursorPath := by
            have : right ∈ cursorPath.reverse := by simp [reverseIdentity]
            simpa using this
          have rightPartnerPresent : rightPartner ∈ cursorPath := by
            have : rightPartner ∈ cursorPath.reverse := by simp [reverseIdentity]
            simpa using this
          obtain ⟨rightAtom, rightObserved⟩ := currentSome right rightPresent
          obtain ⟨rightPartnerAtom, rightPartnerObserved⟩ :=
            currentSome rightPartner rightPartnerPresent
          have fullReverse : (initial.leftCursor :: cursorPath).reverse =
              right :: rightPartner :: (more ++ [initial.leftCursor]) := by
            simp [reverseIdentity]
          have reverseIncoming : cursorPath.reverse.IsChain
              (fun later earlier =>
                later.previous? = some earlier.occurrence) := by
            exact List.isChain_reverse.mpr embedding.incoming
          rw [reverseIdentity] at reverseIncoming
          have rightPrevious : right.previous? = some rightPartner.occurrence :=
            reverseIncoming.rel_head
          let frame : input.LocalizedRule3CumulatedEndpointCursorFrame carrierFuel :=
            { initial := initial
              rightward := cursorPath
              rightPartnerCursor := rightPartner
              rightCursor := right
              rightPartner := rightPartnerAtom
              right := rightAtom }
          refine ⟨frame, embedding, ?_, rfl, rfl, rightPresent,
            rightPartnerPresent, rightPrevious⟩
          change input.walkLocalizedRule3CumulatedAxis? traversalFuel
              initial.rightCursor = some cursorPath at walkComputed
          simp [localizedRule3CumulatedEndpointCursorFrame?,
            input.localizedRule3CumulatedAxisEntry?_evenAxialFirstChild
              carrierFuel axis,
            walkComputed, reverseIdentity, rightPartnerObserved, rightObserved,
            frame, initial, traversalFuel, carrierFuel]

/-- The generic terminal-to-terminal cumulated endpoint constructor is total on the canonical
first child of every perceived open even axis at atom-count depth. -/
theorem exists_localizedRule3CumulatedEndpointCursorFrame_evenAxial_at_atomCount
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedEvenAxialChain) :
    ∃ frame,
      input.localizedRule3CumulatedEndpointCursorFrame?
          (input.localizedRule3CumulatedTraversalFuel
            input.certified.input.molecule.atomCount)
          (input.localizedEvenAxialFirstChildOccurrence
            input.certified.input.molecule.atomCount axis) = some frame ∧
      frame.rightward.map
          (fun cursor => cursor.occurrence.1.node.current?) =
        axis.1.path.tail.map some := by
  obtain ⟨frame, embedding, computed, _initial, rightward, _rightPresent,
      _rightPartnerPresent, _rightPrevious⟩ :=
    input.exists_localizedRule3CumulatedEndpointCursorFrameWithEmbedding_evenAxial_at_atomCount
      axis
  refine ⟨frame, computed, ?_⟩
  rw [rightward]
  exact embedding.atoms

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
