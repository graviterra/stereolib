import TetraStereo.OneCenter.IR9PolyhedralSemantics
import TetraStereo.OneCenter.LocalizedScheduledChemicalCompleteness
import TetraStereo.OneCenter.CIPObservedPlanarSpatialConformance
import TetraStereo.OneCenter.P94CoordinateRingGeometry
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Authority-level P-93 physical units and citations

P-93 configuration clauses cannot use one bare natural number as both a graph vertex and an IUPAC
locant.  This module keeps three layers distinct:

1. a decoration-free physical stereogenic unit certified against the chemical input;
2. a source citation token, including compound locants and prime decoration; and
3. an audited relation authorizing that citation for that physical unit.

Descriptor vocabularies remain a type parameter.  A proof-carrying involution supplies mirror
behavior, so relative configuration is an actual equivalence relation rather than a relation built
from an arbitrary function.
-/

namespace TetraStereo.OneCenter

/-! ## Chemical-unit evidence -/

/-- Binary constitutional interactions.  Multicenter records are intentionally absent: their
participants are incident to one hyperedge, not pairwise bonded as a clique. -/
def P93AuthorityBinaryInteractionKind : SemanticInteractionKind → Prop
  | .unspecifiedCovalent
  | .covalent _
  | .aromatic
  | .delocalized _
  | .coordinate => True
  | .multicenter _
  | .ionic
  | .metallic
  | .hydrogenBond
  | .other _ => False

def P93AuthorityBinaryBond
    (source : AuthoritativeChemicalInput) (left right : Nat) : Prop :=
  left ≠ right ∧
    ∃ interaction ∈ source.molecule.interactions,
      P93AuthorityBinaryInteractionKind interaction.kind ∧
        (interaction.participants = [left, right] ∨
          interaction.participants = [right, left])

/-- Center-to-participant incidence for a genuine multicenter interaction.  This relation is kept
separate from binary adjacency and is consumed only by family semantics that allow such units. -/
def P93AuthorityMulticenterIncidence
    (source : AuthoritativeChemicalInput) (center participant : Nat) : Prop :=
  center ≠ participant ∧
    ∃ interaction ∈ source.molecule.interactions, ∃ electrons,
      interaction.kind = .multicenter electrons ∧
        center ∈ interaction.participants ∧ participant ∈ interaction.participants

def P93AuthorityAtomsBounded
    (source : AuthoritativeChemicalInput) (atoms : List Nat) : Prop :=
  ∀ atom ∈ atoms, atom < source.molecule.atomCount

def P93AuthorityConnectedPath
    (source : AuthoritativeChemicalInput) : List Nat → Prop
  | [] | [_] => True
  | first :: second :: remaining =>
      P93AuthorityBinaryBond source first second ∧
        P93AuthorityConnectedPath source (second :: remaining)

def P93AuthorityCanonicalDirectedPath (path : List Nat) : Prop :=
  2 ≤ path.length ∧ path.Nodup ∧
    ∃ first last,
      path.head? = some first ∧ path.getLast? = some last ∧ first < last

/-- One exact physical order-two bond in the format-neutral semantic constitution.  This uses the
normalized localized record already checked by `CertifiedLocalizedCIPInput`, but does not require
or store a production analyzer certificate at the source-observation boundary. -/
def P93AuthorityExactDoubleBond
    (source : AuthoritativeChemicalInput) (left right : Nat) : Prop :=
  left ≠ right ∧
    (semanticEdgeKey left right, 2) ∈ source.molecule.localizedCovalentRecords

/-- A terminal of a source-level cumulene axis has exactly one bounded order-two neighbor.  This
is stated directly over the semantic constitution, without importing a production analyzer
certificate into source data. -/
def P93AuthorityCumuleneTerminal
    (source : AuthoritativeChemicalInput) (terminal : Nat) : Prop :=
  terminal < source.molecule.atomCount ∧
    ∃ neighbor, neighbor < source.molecule.atomCount ∧
      P93AuthorityExactDoubleBond source terminal neighbor ∧
      ∀ other, other < source.molecule.atomCount →
        P93AuthorityExactDoubleBond source terminal other → other = neighbor

/-- An internal atom of a source-level cumulene axis has exactly two distinct bounded order-two
neighbors.  Thus no unrecorded third branch can be ignored by a selected terminal-to-terminal
path. -/
def P93AuthorityCumuleneInternal
    (source : AuthoritativeChemicalInput) (atom : Nat) : Prop :=
  atom < source.molecule.atomCount ∧
    ∃ previous next,
      previous < source.molecule.atomCount ∧
      next < source.molecule.atomCount ∧ previous ≠ next ∧
      P93AuthorityExactDoubleBond source atom previous ∧
      P93AuthorityExactDoubleBond source atom next ∧
      ∀ other, other < source.molecule.atomCount →
        P93AuthorityExactDoubleBond source atom other →
          other = previous ∨ other = next

/-- A source-independent canonical cumulene axis is a bounded simple maximal chain of at least
two exact order-two constitutional bonds, canonically oriented from its lower-numbered terminal.
Both endpoints must be genuine degree-one order-two terminals, so a proper subchain cannot pass
as a complete axis.  Existing molecule-wide perception proves this relation for every computed
even or odd cumulene; source data itself need not contain a `CertifiedLocalizedCIPInput` or an
analyzer result. -/
def P93AuthorityCanonicalCumuleneAxisPerceived
    (source : AuthoritativeChemicalInput) (path : List Nat) : Prop :=
  3 ≤ path.length ∧
    P93AuthorityAtomsBounded source path ∧
    P93AuthorityCanonicalDirectedPath path ∧
    path.IsChain (P93AuthorityExactDoubleBond source) ∧
    ∃ first last,
      path.head? = some first ∧ path.getLast? = some last ∧
        P93AuthorityCumuleneTerminal source first ∧
        P93AuthorityCumuleneTerminal source last ∧
        ∀ atom ∈ path, atom ≠ first → atom ≠ last →
          P93AuthorityCumuleneInternal source atom

/-- Source-level even cumulene perception includes the exact parity of its double-bond count. -/
def P93AuthorityCanonicalEvenCumuleneAxisPerceived
    (source : AuthoritativeChemicalInput) (path : List Nat) : Prop :=
  P93AuthorityCanonicalCumuleneAxisPerceived source path ∧ Even (path.length - 1)

/-- Source-level odd cumulene perception includes the exact parity of its double-bond count. -/
def P93AuthorityCanonicalOddCumuleneAxisPerceived
    (source : AuthoritativeChemicalInput) (path : List Nat) : Prop :=
  P93AuthorityCanonicalCumuleneAxisPerceived source path ∧ Odd (path.length - 1)

theorem CertifiedLocalizedCIPInput.p93AuthorityExactDoubleBond_of_graphOrderTwo
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (orderTwo : input.moleculeGraph.bond left right = 2) :
    P93AuthorityExactDoubleBond input.certified.input left.1 right.1 := by
  have distinct : left ≠ right := by
    intro same
    subst right
    rw [input.moleculeGraph.bond_self] at orderTwo
    simp at orderTwo
  have adjacent : input.moleculeGraph.Adj left right := by
    simp [MoleculeGraph.Adj, orderTwo]
  rcases (input.certified.input.molecule.toLocalizedMoleculeGraph_adj_iff_record
    input.graphReady left right distinct).mp adjacent with ⟨order, recordMem, positive⟩
  have recovered := input.certified.input.molecule.toLocalizedMoleculeGraph_bond_eq_of_record
    left right order input.graphReady distinct recordMem
  have orderEq : order = 2 := by
    change input.moleculeGraph.bond left right = order at recovered
    exact recovered.symm.trans orderTwo
  rw [orderEq] at recordMem
  exact ⟨fun valueEq => distinct (Fin.ext valueEq), recordMem⟩

/-- Conversely, an exact source record between bounded atoms is reflected by the certified
localized graph with the same order. -/
theorem CertifiedLocalizedCIPInput.graphOrderTwo_of_p93AuthorityExactDoubleBond
    (input : CertifiedLocalizedCIPInput) (left right : Nat)
    (leftBound : left < input.certified.input.molecule.atomCount)
    (rightBound : right < input.certified.input.molecule.atomCount)
    (exact : P93AuthorityExactDoubleBond input.certified.input left right) :
    input.moleculeGraph.bond ⟨left, leftBound⟩ ⟨right, rightBound⟩ = 2 := by
  exact input.certified.input.molecule.toLocalizedMoleculeGraph_bond_eq_of_record
    ⟨left, leftBound⟩ ⟨right, rightBound⟩ 2 input.graphReady
      (fun same => exact.1 (congrArg Fin.val same)) exact.2

theorem CertifiedLocalizedCIPInput.p93AuthorityExactDoubleBondChain_of_graphOrderTwo
    (input : CertifiedLocalizedCIPInput) (path : List input.Atom)
    (chain : path.IsChain fun left right => input.moleculeGraph.bond left right = 2) :
    (path.map fun atom => atom.1).IsChain
      (P93AuthorityExactDoubleBond input.certified.input) := by
  induction chain with
  | nil => simp
  | singleton atom => simp
  | cons_cons orderTwo remaining inductionHypothesis =>
      simp only [List.map_cons, List.isChain_cons_cons]
      exact ⟨input.p93AuthorityExactDoubleBond_of_graphOrderTwo _ _ orderTwo,
        inductionHypothesis⟩

private theorem CertifiedLocalizedCIPInput.p93AuthorityAtomsBounded_map_val
    (input : CertifiedLocalizedCIPInput) (path : List input.Atom) :
    P93AuthorityAtomsBounded input.certified.input (path.map fun atom => atom.1) := by
  intro atom atomMem
  rw [List.mem_map] at atomMem
  rcases atomMem with ⟨bounded, _boundedMem, rfl⟩
  exact bounded.2

/-- A completed declarative axial walk ends at a terminal with exactly one order-two neighbor. -/
private theorem CertifiedLocalizedCIPInput.DeclarativeLocalizedAxialChainWalk.last_terminal
    (input : CertifiedLocalizedCIPInput)
    {previous current : input.Atom} {seen path : List input.Atom}
    (derived : input.DeclarativeLocalizedAxialChainWalk previous current seen path)
    (incoming : input.moleculeGraph.bond previous current = 2) :
    ∃ terminal partner,
      path.getLast? = some terminal ∧
      input.moleculeGraph.bond terminal partner = 2 ∧
      ∀ neighbor, input.moleculeGraph.bond terminal neighbor = 2 → neighbor = partner := by
  induction derived with
  | @terminal previous current seen forward =>
      refine ⟨current, previous, rfl, ?_, ?_⟩
      · simpa [input.moleculeGraph.bond_symm] using incoming
      · intro neighbor doubleBond
        by_cases identity : neighbor = previous
        · exact identity
        · have present : neighbor ∈
              input.localizedAxialForwardNeighbors previous current :=
            (input.mem_localizedAxialForwardNeighbors_iff
              previous current neighbor).mpr ⟨doubleBond, identity⟩
          rw [forward] at present
          simp at present
  | @linear previous current seen next tail forward fresh rest inductionHypothesis =>
      have nextPresent : next ∈
          input.localizedAxialForwardNeighbors previous current := by
        simp [forward]
      have nextDouble : input.moleculeGraph.bond current next = 2 :=
        (input.mem_localizedAxialForwardNeighbors_iff previous current next).mp
          nextPresent |>.1
      obtain ⟨terminal, partner, lastEq, terminalDouble, terminalUnique⟩ :=
        inductionHypothesis nextDouble
      refine ⟨terminal, partner, ?_, terminalDouble, terminalUnique⟩
      cases tail with
      | nil =>
          have tailHead := rest.head?_eq_current input
          simp at tailHead
      | cons head remaining => simpa using lastEq

/-- Every nonterminal atom returned by a completed declarative walk has exactly its incoming and
outgoing order-two neighbors.  The singleton-forward premise is the branch-rejection fact used by
the executable analyzer. -/
private theorem CertifiedLocalizedCIPInput.DeclarativeLocalizedAxialChainWalk.nonterminal_degree_two
    (input : CertifiedLocalizedCIPInput)
    {previous current : input.Atom} {seen path : List input.Atom}
    (derived : input.DeclarativeLocalizedAxialChainWalk previous current seen path)
    (incoming : input.moleculeGraph.bond previous current = 2)
    {last : input.Atom} (lastEq : path.getLast? = some last) :
    ∀ atom ∈ path, atom ≠ last →
      ∃ incomingNeighbor outgoingNeighbor,
        incomingNeighbor ≠ outgoingNeighbor ∧
        input.moleculeGraph.bond atom incomingNeighbor = 2 ∧
        input.moleculeGraph.bond atom outgoingNeighbor = 2 ∧
        ∀ neighbor, input.moleculeGraph.bond atom neighbor = 2 →
          neighbor = incomingNeighbor ∨ neighbor = outgoingNeighbor := by
  induction derived with
  | @terminal previous current seen forward =>
      intro atom atomMem atomNeLast
      have atomEq : atom = current := by simpa using atomMem
      have lastIdentity : last = current := by
        exact (Option.some.inj lastEq).symm
      exact False.elim (atomNeLast (atomEq.trans lastIdentity.symm))
  | @linear previous current seen next tail forward fresh rest inductionHypothesis =>
      have nextPresent : next ∈
          input.localizedAxialForwardNeighbors previous current := by
        simp [forward]
      have nextFacts :=
        (input.mem_localizedAxialForwardNeighbors_iff previous current next).mp nextPresent
      have nextDouble : input.moleculeGraph.bond current next = 2 := nextFacts.1
      have nextNePrevious : next ≠ previous := nextFacts.2
      have tailNonempty : tail ≠ [] := by
        intro tailEmpty
        have tailHead := rest.head?_eq_current input
        simp [tailEmpty] at tailHead
      have tailLastEq : tail.getLast? = some last := by
        cases tail with
        | nil => exact False.elim (tailNonempty rfl)
        | cons head remaining => simpa using lastEq
      intro atom atomMem atomNeLast
      rw [List.mem_cons] at atomMem
      rcases atomMem with atomEq | atomTail
      · subst atom
        refine ⟨previous, next, nextNePrevious.symm, ?_, nextDouble, ?_⟩
        · simpa [input.moleculeGraph.bond_symm] using incoming
        · intro neighbor neighborDouble
          by_cases neighborPrevious : neighbor = previous
          · exact Or.inl neighborPrevious
          · have neighborForward : neighbor ∈
                input.localizedAxialForwardNeighbors previous current :=
              (input.mem_localizedAxialForwardNeighbors_iff
                previous current neighbor).mpr ⟨neighborDouble, neighborPrevious⟩
            have neighborNext : neighbor = next := by simpa [forward] using neighborForward
            exact Or.inr neighborNext
      · exact inductionHypothesis nextDouble tailLastEq atom atomTail atomNeLast

/-- A unique graph-level order-two neighbor transports to the source-only terminal relation. -/
private theorem CertifiedLocalizedCIPInput.p93AuthorityCumuleneTerminal_of_uniqueGraphNeighbor
    (input : CertifiedLocalizedCIPInput) (terminal partner : input.Atom)
    (doubleBond : input.moleculeGraph.bond terminal partner = 2)
    (unique : ∀ neighbor, input.moleculeGraph.bond terminal neighbor = 2 →
      neighbor = partner) :
    P93AuthorityCumuleneTerminal input.certified.input terminal.1 := by
  refine ⟨terminal.2, partner.1, partner.2,
    input.p93AuthorityExactDoubleBond_of_graphOrderTwo terminal partner doubleBond, ?_⟩
  intro other otherBound exact
  exact congrArg Fin.val (unique ⟨other, otherBound⟩
    (input.graphOrderTwo_of_p93AuthorityExactDoubleBond
      terminal.1 other terminal.2 otherBound exact))

/-- Exact graph degree two transports to the source-only internal-axis relation. -/
private theorem CertifiedLocalizedCIPInput.p93AuthorityCumuleneInternal_of_uniqueGraphNeighbors
    (input : CertifiedLocalizedCIPInput) (atom previous next : input.Atom)
    (different : previous ≠ next)
    (previousDouble : input.moleculeGraph.bond atom previous = 2)
    (nextDouble : input.moleculeGraph.bond atom next = 2)
    (unique : ∀ neighbor, input.moleculeGraph.bond atom neighbor = 2 →
      neighbor = previous ∨ neighbor = next) :
    P93AuthorityCumuleneInternal input.certified.input atom.1 := by
  refine ⟨atom.2, previous.1, next.1, previous.2, next.2, ?_,
    input.p93AuthorityExactDoubleBond_of_graphOrderTwo atom previous previousDouble,
    input.p93AuthorityExactDoubleBond_of_graphOrderTwo atom next nextDouble, ?_⟩
  · intro valueEq
    exact different (Fin.ext valueEq)
  · intro other otherBound exact
    rcases unique ⟨other, otherBound⟩
        (input.graphOrderTwo_of_p93AuthorityExactDoubleBond
          atom.1 other atom.2 otherBound exact) with previousEq | nextEq
    · exact Or.inl (congrArg Fin.val previousEq)
    · exact Or.inr (congrArg Fin.val nextEq)

/-- The complete declarative analyzer path transports to the strengthened source-only maximal
axis relation. -/
private theorem CertifiedLocalizedCIPInput.p93AuthorityAxisPerceived_of_declarative
    (input : CertifiedLocalizedCIPInput)
    (root : input.LocalizedAxialRootCandidate) (path : List input.Atom)
    (derived : input.DeclarativeLocalizedAxialChainFromRoot root path)
    (longer : 1 < path.length - 1)
    (oppositeTerminal : input.Atom)
    (lastEq : path.getLast? = some oppositeTerminal)
    (lower : root.terminal < oppositeTerminal) :
    P93AuthorityCanonicalCumuleneAxisPerceived input.certified.input
      (path.map fun atom => atom.1) := by
  have chain := derived.path_isChain_doubleBond input
  have pathNodup := derived.path_nodup input
  rcases derived with ⟨rootValid, tail, pathEq, walk⟩
  obtain ⟨walkTerminal, walkPartner, walkLast, walkDouble, walkUnique⟩ :=
    walk.last_terminal input rootValid.1
  have tailNonempty : tail ≠ [] := by
    intro tailEmpty
    have tailHead := walk.head?_eq_current input
    simp [tailEmpty] at tailHead
  have walkLastFull : path.getLast? = some walkTerminal := by
    rw [pathEq]
    cases tail with
    | nil => exact False.elim (tailNonempty rfl)
    | cons head remaining => simpa using walkLast
  have terminalEq : walkTerminal = oppositeTerminal := by
    exact Option.some.inj (walkLastFull.symm.trans lastEq)
  subst walkTerminal
  refine ⟨?_, input.p93AuthorityAtomsBounded_map_val path, ?_,
    input.p93AuthorityExactDoubleBondChain_of_graphOrderTwo path chain, ?_⟩
  · simp only [List.length_map]
    omega
  · refine ⟨?_, ?_, root.terminal.1, oppositeTerminal.1, ?_, ?_, lower⟩
    · simp only [List.length_map]
      omega
    · exact pathNodup.map (by
        intro left right valueEq
        exact Fin.ext valueEq)
    · rw [pathEq]
      rfl
    · simpa using congrArg (Option.map fun atom : input.Atom => atom.1) lastEq
  · refine ⟨root.terminal.1, oppositeTerminal.1, ?_, ?_, ?_, ?_, ?_⟩
    · rw [pathEq]
      rfl
    · simpa using congrArg (Option.map fun atom : input.Atom => atom.1) lastEq
    · exact input.p93AuthorityCumuleneTerminal_of_uniqueGraphNeighbor
        root.terminal root.firstAxis rootValid.1 rootValid.2
    · exact input.p93AuthorityCumuleneTerminal_of_uniqueGraphNeighbor
        oppositeTerminal walkPartner walkDouble walkUnique
    · intro atom atomMem atomNeFirst atomNeLast
      rw [List.mem_map] at atomMem
      rcases atomMem with ⟨sourceAtom, sourceAtomMem, rfl⟩
      have sourceAtomNeRoot : sourceAtom ≠ root.terminal := by
        intro identity
        exact atomNeFirst (congrArg Fin.val identity)
      have sourceAtomTailMem : sourceAtom ∈ tail := by
        rw [pathEq] at sourceAtomMem
        simp only [List.mem_cons] at sourceAtomMem
        exact sourceAtomMem.resolve_left sourceAtomNeRoot
      have sourceAtomNeLast : sourceAtom ≠ oppositeTerminal := by
        intro identity
        exact atomNeLast (congrArg Fin.val identity)
      obtain ⟨incomingNeighbor, outgoingNeighbor, different,
          incomingDouble, outgoingDouble, unique⟩ :=
        walk.nonterminal_degree_two input rootValid.1 walkLast
          sourceAtom sourceAtomTailMem sourceAtomNeLast
      exact input.p93AuthorityCumuleneInternal_of_uniqueGraphNeighbors
        sourceAtom incomingNeighbor outgoingNeighbor different
          incomingDouble outgoingDouble unique

theorem CertifiedLocalizedCIPInput.LocalizedEvenAxialChain.p93AuthorityEvenAxisPerceived
    (input : CertifiedLocalizedCIPInput) (axis : input.LocalizedEvenAxialChain) :
    P93AuthorityCanonicalEvenCumuleneAxisPerceived input.certified.input
      (axis.1.path.map fun atom => atom.1) := by
  have derived := input.mem_localizedEvenAxialChains_implies_declarative axis.1 axis.2
  rcases derived.2.2.2 with ⟨oppositeTerminal, lastEq, lower⟩
  constructor
  · exact input.p93AuthorityAxisPerceived_of_declarative axis.1.root axis.1.path
      derived.1 derived.2.1 oppositeTerminal lastEq lower
  · simpa only [List.length_map, LocalizedEvenAxialChainFrame.doubleBondCount] using
      derived.2.2.1

theorem CertifiedLocalizedCIPInput.LocalizedOddCumuleneChain.p93AuthorityOddAxisPerceived
    (input : CertifiedLocalizedCIPInput) (axis : input.LocalizedOddCumuleneChain) :
    P93AuthorityCanonicalOddCumuleneAxisPerceived input.certified.input
      (axis.1.path.map fun atom => atom.1) := by
  have derived := input.mem_localizedOddCumuleneChains_implies_declarative axis.1 axis.2
  rcases derived.2.2.2 with ⟨oppositeTerminal, lastEq, lower⟩
  constructor
  · exact input.p93AuthorityAxisPerceived_of_declarative axis.1.root axis.1.path
      derived.1 derived.2.1 oppositeTerminal lastEq lower
  · simpa only [List.length_map, LocalizedOddCumuleneChainFrame.doubleBondCount] using
      derived.2.2.1

/-- Typed identified-helix frame.  Its path and terminal references are validated against the
same source and exact spatial handedness relation below. -/
structure P93AuthorityHelixFrame where
  record : IndexedHelicalGeometryObservation
  descriptor : HelicalDescriptor
  deriving DecidableEq, Repr

def P93AuthorityTorsionSignAgrees
    (angle : BlueBookP94.TorsionAngle) : StereoSense → Prop
  | .positive => 0 < angle.degrees
  | .negative => angle.degrees < 0

/-- Every consecutive four-atom window has the same nonzero exact torsion sign. -/
def P93AuthorityCoherentHelicalWinding
    (spatial : SpatialConfiguration) : List Nat → StereoSense → Prop
  | first :: second :: third :: fourth :: remaining, sense =>
      ∃ angle,
        BlueBookP94.CoordinateTorsion.SpatialTorsionAngleJudgment
          spatial first second third fourth angle ∧
        P93AuthorityTorsionSignAgrees angle sense ∧
        P93AuthorityCoherentHelicalWinding spatial
          (second :: third :: fourth :: remaining) sense
  | _, _ => True

def P93AuthorityHelixFrame.ValidFor
    (source : AuthoritativeChemicalInput) (path : List Nat)
    (frame : P93AuthorityHelixFrame) : Prop :=
  frame.record.helixPath = path ∧
    frame.descriptor = HelicalDescriptor.ofSense frame.record.sense ∧
    4 ≤ path.length ∧
    P93AuthorityAtomsBounded source
      (frame.record.frontReference :: frame.record.backReference :: path) ∧
    P93AuthorityCanonicalDirectedPath path ∧
    P93AuthorityConnectedPath source path ∧
    ∃ front back spatial windingSense,
      BlueBookP93.GeometryIngress.HelicalPathEndpoints path front back ∧
        P93AuthorityBinaryBond source front frame.record.frontReference ∧
        P93AuthorityBinaryBond source back frame.record.backReference ∧
        source.spatial? = some spatial ∧
        BlueBookP93.GeometryIngress.RationalHelicalObservationJudgment
          spatial frame.record frame.descriptor ∧
        windingSense = frame.record.sense ∧
        P93AuthorityCoherentHelicalWinding spatial path windingSense

/-- Point-level certificate for an oriented stereogenic plane. -/
def P93AuthorityPlanePointsResolved
    (points : List CartesianPoint3) (pilotPoint : CartesianPoint3) : Prop :=
  match points with
  | first :: second :: third :: _ =>
      let plane : BlueBookP94.CoordinateRing.ExactPlane :=
        { first, second, third }
      plane.Nondegenerate ∧
        (∀ point ∈ points,
          plane.PointHasSide point .onPlane) ∧
        (plane.PointHasSide pilotPoint .positive ∨
          plane.PointHasSide pilotPoint .negative)
  | _ => False

/-- Exact coordinates prove coplanarity of every member and prove that the designated
out-of-plane atom lies strictly off the oriented plane. -/
def P93AuthorityPlaneSpatiallyResolved
    (source : AuthoritativeChemicalInput)
    (members : List Nat) (offPlane reference : Nat) : Prop :=
  reference ∈ members ∧ offPlane ∉ members ∧
    ∃ spatial points offPlanePoint,
      source.spatial? = some spatial ∧
        BlueBookP94.CoordinateRing.SpatialPointsAt spatial members points ∧
        BlueBookP94.CoordinateRing.SpatialPointAt spatial offPlane offPlanePoint ∧
        P93AuthorityPlanePointsResolved points offPlanePoint

/-- Source-shaped planar frame.  The physical identity below stores only the normalized member
set; traversal and pilot/reference roles live here and must satisfy molecule topology. -/
structure P93AuthorityPlaneFrame where
  record : IndexedPlanarDerivedTetrahedronObservation
  deriving DecidableEq, Repr

def P93AuthorityPlaneFrame.ValidFor
    (source : AuthoritativeChemicalInput) (members : Finset Nat)
    (frame : P93AuthorityPlaneFrame) : Prop :=
  frame.record.planeAtoms.toFinset = members ∧
    3 ≤ frame.record.planeAtoms.length ∧ frame.record.planeAtoms.Nodup ∧
    P93AuthorityAtomsBounded source
      (frame.record.pilotAtom :: frame.record.firstReference ::
        frame.record.secondReference :: frame.record.inPlaneBondAtom ::
        frame.record.outOfPlaneAtom :: frame.record.planeAtoms) ∧
    frame.record.pilotAtom ∈ frame.record.planeAtoms ∧
    frame.record.firstReference ∈ frame.record.planeAtoms ∧
    frame.record.secondReference ∈ frame.record.planeAtoms ∧
    frame.record.inPlaneBondAtom ∈ frame.record.planeAtoms ∧
    frame.record.outOfPlaneAtom ∉ frame.record.planeAtoms ∧
    [frame.record.pilotAtom, frame.record.firstReference,
      frame.record.secondReference, frame.record.inPlaneBondAtom].Nodup ∧
    P93AuthorityBinaryBond source frame.record.pilotAtom
      frame.record.firstReference ∧
    P93AuthorityBinaryBond source frame.record.pilotAtom
      frame.record.secondReference ∧
    P93AuthorityBinaryBond source frame.record.pilotAtom
      frame.record.inPlaneBondAtom ∧
    P93AuthorityBinaryBond source frame.record.inPlaneBondAtom
      frame.record.outOfPlaneAtom ∧
    frame.record.torsionRestricted = true ∧
    frame.record.planeCannotBeSymmetryPlane = true ∧
    P93AuthorityPlaneSpatiallyResolved source frame.record.planeAtoms
      frame.record.outOfPlaneAtom frame.record.firstReference

/-- Polyhedral evidence binds the typed IR-9 observation to the exact source center, ligand set,
and coordinate frame.  Qualitative IR-9 words remain observation evidence, but cannot be reused
for a different coordination unit. -/
structure P93AuthorityPolyhedralFrame where
  record : IndexedPolyhedralGeometryObservation
  spatial : SpatialConfiguration
  centerPoint : CartesianPoint3
  positionPoints : List CartesianPoint3
  deriving DecidableEq, Repr

/-- Geometry-specific completeness of the configuration-role frame.  Most IR-9 observations name
only the positions distinguished by the rule, so their routed lists are intentionally partial.
Trigonal-prismatic and high-coordinate bipyramidal observations instead enumerate the entire
coordination frame; requiring full arity here prevents an audited cycle from being truncated while
remaining unique and in bounds. -/
def P93AuthorityConfigurationRoleFrameComplete
    (observation : RedBookIR9.ConfigurationPositionObservation)
    (geometry : BlueBookP93.Geometry) (rolePositions : List Nat) : Prop :=
  RedBookIR9.ConfigurationPositionsRecognized observation geometry rolePositions ∧
    rolePositions.Nodup ∧
    (∀ role ∈ rolePositions, role < geometry.coordinationNumber) ∧
    match observation with
    | .trigonalPrism _ _
    | .pentagonalBipyramid _ _ _
    | .hexagonalBipyramid _ _ _
    | .heptagonalBipyramid _ _ _ =>
        rolePositions.length = geometry.coordinationNumber
    | _ => True

def P93AuthorityPolyhedralFrame.ValidFor
    (source : AuthoritativeChemicalInput) (center : Nat)
    (positions : Finset Nat) (geometry : BlueBookP93.Geometry)
    (frame : P93AuthorityPolyhedralFrame) : Prop :=
  frame.record.center = center ∧
    frame.record.ligands.toFinset = positions ∧ frame.record.ligands.Nodup ∧
    geometry = BlueBookP93.geometryOfProduction frame.record.geometry ∧
    RedBookIR9.GeometryRecognized frame.record.recognition geometry ∧
    source.spatial? = some frame.spatial ∧
    BlueBookP94.CoordinateRing.SpatialPointAt frame.spatial center frame.centerPoint ∧
    BlueBookP94.CoordinateRing.SpatialPointsAt
      frame.spatial frame.record.ligands frame.positionPoints ∧
    frame.record.ligands.length = geometry.coordinationNumber ∧
    (∀ position ∈ frame.record.ligands,
      P93AuthorityBinaryBond source center position ∨
        P93AuthorityMulticenterIncidence source center position) ∧
    (∃ rolePositions,
      P93AuthorityConfigurationRoleFrameComplete
        frame.record.configurationPositions geometry rolePositions) ∧
    ∃ rotation?,
      RedBookIR9.AbsoluteOrientationRecognized
        frame.record.absoluteOrientation geometry rotation?

/-- Audited boundary for source observations that are not derivable from finite exact coordinates
alone.  The reviewed provision corpus must instantiate these relations; the carrier never treats
raw Boolean or qualitative fields as self-authenticating. -/
structure P93AuthorityPhysicalObservationPolicy where
  HelixIdentified :
    AuthoritativeChemicalInput → List Nat → P93AuthorityHelixFrame → Prop
  PlanarRestrictionAndAsymmetryObserved :
    AuthoritativeChemicalInput → Finset Nat → P93AuthorityPlaneFrame → Prop
  PolyhedralQualitativeFrameObserved :
    AuthoritativeChemicalInput → Nat → Finset Nat → BlueBookP93.Geometry →
      P93AuthorityPolyhedralFrame → Prop

/-- Decoration-free physical identity.  Traversal order is retained where it carries chemical
meaning.  Polyhedral geometry is deliberately evidence rather than identity, so one coordination
unit cannot evade `Nodup` by carrying two geometry labels. -/
inductive P93AuthorityPhysicalUnit where
  | atomCenter (center : Nat)
  | bond (first second : Nat)
  | axis (path : List Nat)
  | plane (members : Finset Nat)
  | helix (path : List Nat)
  | polyhedron (center : Nat) (positions : Finset Nat)
  deriving DecidableEq

namespace P93AuthorityPhysicalUnit

/-- Mechanical source certificate plus the explicit audited observation boundary where required. -/
def ValidFor (policy : P93AuthorityPhysicalObservationPolicy)
    (source : AuthoritativeChemicalInput) : P93AuthorityPhysicalUnit → Prop
  | .atomCenter center =>
      center < source.molecule.atomCount ∧
        ∃ neighbors : List Nat,
          3 ≤ neighbors.length ∧ neighbors.Nodup ∧
            P93AuthorityAtomsBounded source neighbors ∧
            ∀ neighbor ∈ neighbors,
              P93AuthorityBinaryBond source center neighbor ∨
                P93AuthorityMulticenterIncidence source center neighbor
  | .bond first second =>
      first < source.molecule.atomCount ∧
        second < source.molecule.atomCount ∧
        first < second ∧
        P93AuthorityBinaryBond source first second
  | .axis path =>
      P93AuthorityCanonicalCumuleneAxisPerceived source path
  | .plane members =>
      ∃ frame : P93AuthorityPlaneFrame,
        frame.ValidFor source members ∧
          policy.PlanarRestrictionAndAsymmetryObserved source members frame
  | .helix path =>
      ∃ frame : P93AuthorityHelixFrame,
        frame.ValidFor source path ∧
          policy.HelixIdentified source path frame
  | .polyhedron center positions =>
      ∃ geometry frame,
        P93AuthorityPolyhedralFrame.ValidFor
          source center positions geometry frame ∧
        policy.PolyhedralQualitativeFrameObserved
          source center positions geometry frame

end P93AuthorityPhysicalUnit

/-! ## Source citation layer -/

/-- One printed numeric component such as `4` or `4''`.  It is nomenclature data and is never
interpreted as a semantic graph vertex. -/
structure P93AuthorityCitationComponent where
  value : Nat
  primes : Nat := 0
  deriving DecidableEq, Repr

/-- A possibly compound locant.  Examples include one atom citation, a bond pair, or the ordered
sequence identifying an axis/plane/helix under the applicable source rule. -/
structure P93AuthorityCitationToken where
  components : List P93AuthorityCitationComponent
  deriving DecidableEq, Repr

namespace P93AuthorityCitationToken

def Valid (token : P93AuthorityCitationToken) : Prop :=
  token.components ≠ []

def key (token : P93AuthorityCitationToken) : List Nat :=
  token.components.flatMap fun component =>
    [component.value, component.primes]

end P93AuthorityCitationToken

/-- Standard non-strict lexicographic order on actual citation components. -/
def P93AuthorityNatListLexLE : List Nat → List Nat → Prop
  | [], _ => True
  | _ :: _, [] => False
  | left :: leftTail, right :: rightTail =>
      left < right ∨
        (left = right ∧ P93AuthorityNatListLexLE leftTail rightTail)

def P93AuthorityCitationToken.CitationLE
    (left right : P93AuthorityCitationToken) : Prop :=
  P93AuthorityNatListLexLE left.key right.key

/-! ## Generic configuration language -/

/-- One descriptor-bearing unit and the distinct source citation used to name it. -/
structure P93AuthorityLocatedAssignment (Descriptor : Type*) where
  unit : P93AuthorityPhysicalUnit
  citation : P93AuthorityCitationToken
  descriptor : Descriptor

/-- Configuration data itself is proof-free.  Its validity is judged against the chemical input
and the audited citation relation below. -/
@[ext] structure P93AuthorityConfiguration (Descriptor : Type*) where
  assignments : List (P93AuthorityLocatedAssignment Descriptor)

namespace P93AuthorityConfiguration

variable {Descriptor : Type*}

/-- `CitationAuthorized` is the molecule-specific, source-audited numbering relation.  Keeping it
as an explicit reference-program argument prevents both graph enumeration and caller decoration
from silently becoming IUPAC nomenclature. -/
def InputFaithful
    (source : AuthoritativeChemicalInput)
    (observationPolicy : P93AuthorityPhysicalObservationPolicy)
    (CitationAuthorized :
      P93AuthorityCitationToken → P93AuthorityPhysicalUnit → Prop)
    (configuration : P93AuthorityConfiguration Descriptor) : Prop :=
  configuration.assignments ≠ [] ∧
    (configuration.assignments.map fun assignment => assignment.unit).Nodup ∧
    (configuration.assignments.map fun assignment => assignment.citation).Nodup ∧
    ∀ assignment ∈ configuration.assignments,
      assignment.unit.ValidFor observationPolicy source ∧
        assignment.citation.Valid ∧
        CitationAuthorized assignment.citation assignment.unit

def IsCanonicalNamedRepresentative
    (preferred : Descriptor → Prop)
    (configuration : P93AuthorityConfiguration Descriptor) : Prop :=
  ∃ leading ∈ configuration.assignments,
    (∀ assignment ∈ configuration.assignments,
      leading.citation.CitationLE assignment.citation) ∧
    preferred leading.descriptor

/-- A certified descriptor mirror action. -/
structure MirrorAction (Descriptor : Type*) where
  mirror : Descriptor → Descriptor
  involutive : ∀ descriptor, mirror (mirror descriptor) = descriptor

def globallyMirrored
    (action : MirrorAction Descriptor)
    (configuration : P93AuthorityConfiguration Descriptor) :
    P93AuthorityConfiguration Descriptor where
  assignments := configuration.assignments.map fun assignment =>
    { unit := assignment.unit
      citation := assignment.citation
      descriptor := action.mirror assignment.descriptor }

theorem globallyMirrored_involutive
    (action : MirrorAction Descriptor)
    (configuration : P93AuthorityConfiguration Descriptor) :
    (configuration.globallyMirrored action).globallyMirrored action = configuration := by
  ext
  simp [globallyMirrored, List.map_map, Function.comp_def, action.involutive]

def RelativeEquivalent
    (action : MirrorAction Descriptor)
    (left right : P93AuthorityConfiguration Descriptor) : Prop :=
  right = left ∨ right = left.globallyMirrored action

theorem relativeEquivalent_refl
    (action : MirrorAction Descriptor)
    (configuration : P93AuthorityConfiguration Descriptor) :
    RelativeEquivalent action configuration configuration :=
  Or.inl rfl

theorem relativeEquivalent_symm
    (action : MirrorAction Descriptor)
    {left right : P93AuthorityConfiguration Descriptor}
    (related : RelativeEquivalent action left right) :
    RelativeEquivalent action right left := by
  rcases related with same | mirror
  · exact Or.inl same.symm
  · right
    calc
      left = (left.globallyMirrored action).globallyMirrored action :=
        (globallyMirrored_involutive action left).symm
      _ = right.globallyMirrored action :=
        (congrArg (globallyMirrored action) mirror).symm

theorem relativeEquivalent_trans
    (action : MirrorAction Descriptor)
    {first second third : P93AuthorityConfiguration Descriptor}
    (firstSecond : RelativeEquivalent action first second)
    (secondThird : RelativeEquivalent action second third) :
    RelativeEquivalent action first third := by
  rcases firstSecond with same | mirrorFirst
  · subst second
    exact secondThird
  · rcases secondThird with same | mirrorSecond
    · exact Or.inr (same.trans mirrorFirst)
    · left
      calc
        third = second.globallyMirrored action := mirrorSecond
        _ = (first.globallyMirrored action).globallyMirrored action :=
          congrArg (globallyMirrored action) mirrorFirst
        _ = first := globallyMirrored_involutive action first

end P93AuthorityConfiguration

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.P93AuthorityPhysicalUnit.ValidFor
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedEvenAxialChain.p93AuthorityEvenAxisPerceived
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedOddCumuleneChain.p93AuthorityOddAxisPerceived
assert_kernel_only TetraStereo.OneCenter.P93AuthorityConfiguration.globallyMirrored_involutive
assert_kernel_only TetraStereo.OneCenter.P93AuthorityConfiguration.relativeEquivalent_trans
