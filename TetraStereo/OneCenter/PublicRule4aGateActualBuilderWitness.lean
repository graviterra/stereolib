import TetraStereo.OneCenter.PublicParametricRule45Availability
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceCompoundRule4bc
import TetraStereo.OneCenter.PublicRule4aPrefixedDescriptorBackend
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

/-!
# Actual public-builder witness for the omitted Rule-4a gate

This module constructs one small, structurally admitted `AuthoritativeChemicalInput`: a symmetric
single-bond tree whose center atom carries two constitutionally identical branches, and whose two
branches each carry two constitutionally identical terminal child subtrees.  An explicit total
label reader assigns

* `none` to the root and to both branch roots;
* `R` and `S` to the two left-branch children;
* `R` and lowercase pseudoasymmetric `r` to the two right-branch children.

All keys below are produced by the actual public parametric builders on the actual
source-canonical occurrence carrier; no key value is postulated.  The statements expose:

* the actual cumulative `.rule4a` comparison is `gt` (chiral sources precede the
  pseudoasymmetric source);
* the actual P-92.5.2.1 reference selection is `[R,S]` on the left and `[R]` on the right, hence
  the actual count priorities are `1` and `2`;
* both actual compound Rules-4b/4c builders succeed;
* the shipped public compound comparator returns `lt`, because it reads the reference count
  before (and without) the Rule-4a key.

The label reader is an explicit independent input.  Nothing below claims that these labels are
derived from a self-consistent chemical configuration, nor that any molecular descriptor is
wrong.  The result is the exact behaviour of the shipped compiler on actual builder outputs.
-/

namespace TetraStereo.OneCenter
namespace PublicRule4aGateActualBuilderWitness

open AuthoritativeChemicalInput
open CertifiedLocalizedCIPInput

/-! ## The symmetric single-bond source -/

/-- The single element used by the witness molecule. -/
def carbon : PeriodicElement := ⟨6, by decide, by decide⟩

/-- One ordinary carbon atom with default isotope/charge state. -/
def carbonAtom : SemanticAtom := { element := carbon }

/-- One single covalent bond. -/
def singleBond (left right : Nat) : SemanticInteraction :=
  { participants := [left, right], kind := .covalent 1 }

/-- Seven carbon atoms: center `0`, branches `1` and `2`, and two children `3,4` below branch `1`
and `5,6` below branch `2`.  Six single bonds form the symmetric tree. -/
def source : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := [carbonAtom, carbonAtom, carbonAtom, carbonAtom,
          carbonAtom, carbonAtom, carbonAtom]
        interactions :=
          [ singleBond 0 1, singleBond 0 2
          , singleBond 1 3, singleBond 1 4
          , singleBond 2 5, singleBond 2 6 ] } }

/-- The fixture passes the Boolean structural admission gate. -/
theorem source_structurallyWellFormed? :
    source.structurallyWellFormed? = true := by
  decide

/-- The fixture satisfies the structural well-formedness proposition. -/
theorem source_structurallyWellFormed : source.StructurallyWellFormed :=
  (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff source).mp
    source_structurallyWellFormed?

/-! ## Concrete atoms and occurrence frames -/

def atom0 : source.AromaticCanonicalAtom := ⟨0, by decide⟩
def atom1 : source.AromaticCanonicalAtom := ⟨1, by decide⟩
def atom2 : source.AromaticCanonicalAtom := ⟨2, by decide⟩
def atom3 : source.AromaticCanonicalAtom := ⟨3, by decide⟩
def atom4 : source.AromaticCanonicalAtom := ⟨4, by decide⟩
def atom5 : source.AromaticCanonicalAtom := ⟨5, by decide⟩
def atom6 : source.AromaticCanonicalAtom := ⟨6, by decide⟩

/-- The carrier fuel used by the witness: depth two below each final center. -/
def carrierFuel : Nat := 1

/-- The structural evaluation fuel from the actual public availability theorem. -/
def evaluationFuel : Nat := 2 * (carrierFuel + 1)

theorem evaluationFuel_eq : evaluationFuel = 4 := rfl

/-- Root node at the center atom. -/
def rootNode : OfficialCIPNode source.AromaticCanonicalAtom :=
  OfficialCIPNode.root atom0

/-- Node at the left branch root (the center extended to atom `1`). -/
def leftBranchNode : OfficialCIPNode source.AromaticCanonicalAtom :=
  rootNode.extend atom1 0

/-- Node at the right branch root (the center extended to atom `2`). -/
def rightBranchNode : OfficialCIPNode source.AromaticCanonicalAtom :=
  rootNode.extend atom2 0

def leftChild0Node : OfficialCIPNode source.AromaticCanonicalAtom :=
  leftBranchNode.extend atom3 0

def leftChild1Node : OfficialCIPNode source.AromaticCanonicalAtom :=
  leftBranchNode.extend atom4 0

def rightChild0Node : OfficialCIPNode source.AromaticCanonicalAtom :=
  rightBranchNode.extend atom5 0

def rightChild1Node : OfficialCIPNode source.AromaticCanonicalAtom :=
  rightBranchNode.extend atom6 0

def rootFrame : source.AromaticCanonicalOccurrenceFrame :=
  { root := atom0, address := [], node := rootNode, remaining := carrierFuel + 1 }

def leftBranchFrame : source.AromaticCanonicalOccurrenceFrame :=
  { root := atom0, address := [0], node := leftBranchNode, remaining := carrierFuel }

def rightBranchFrame : source.AromaticCanonicalOccurrenceFrame :=
  { root := atom0, address := [1], node := rightBranchNode, remaining := carrierFuel }

def leftChild0Frame : source.AromaticCanonicalOccurrenceFrame :=
  { root := atom0, address := [0, 0], node := leftChild0Node, remaining := 0 }

def leftChild1Frame : source.AromaticCanonicalOccurrenceFrame :=
  { root := atom0, address := [0, 1], node := leftChild1Node, remaining := 0 }

def rightChild0Frame : source.AromaticCanonicalOccurrenceFrame :=
  { root := atom0, address := [1, 0], node := rightChild0Node, remaining := 0 }

def rightChild1Frame : source.AromaticCanonicalOccurrenceFrame :=
  { root := atom0, address := [1, 1], node := rightChild1Node, remaining := 0 }

/-! ### Carrier membership

Each membership is a closed finite fact about the executable source-canonical enumeration. -/

theorem rootFrame_mem :
    rootFrame ∈ source.aromaticCanonicalOccurrences carrierFuel := by
  decide

theorem leftBranchFrame_mem :
    leftBranchFrame ∈ source.aromaticCanonicalOccurrences carrierFuel := by
  decide

theorem rightBranchFrame_mem :
    rightBranchFrame ∈ source.aromaticCanonicalOccurrences carrierFuel := by
  decide

theorem leftChild0Frame_mem :
    leftChild0Frame ∈ source.aromaticCanonicalOccurrences carrierFuel := by
  decide

theorem leftChild1Frame_mem :
    leftChild1Frame ∈ source.aromaticCanonicalOccurrences carrierFuel := by
  decide

theorem rightChild0Frame_mem :
    rightChild0Frame ∈ source.aromaticCanonicalOccurrences carrierFuel := by
  decide

theorem rightChild1Frame_mem :
    rightChild1Frame ∈ source.aromaticCanonicalOccurrences carrierFuel := by
  decide

def rootOccurrence : source.AromaticCanonicalOccurrence carrierFuel :=
  ⟨rootFrame, rootFrame_mem⟩

def leftBranchOccurrence : source.AromaticCanonicalOccurrence carrierFuel :=
  ⟨leftBranchFrame, leftBranchFrame_mem⟩

def rightBranchOccurrence : source.AromaticCanonicalOccurrence carrierFuel :=
  ⟨rightBranchFrame, rightBranchFrame_mem⟩

def leftChild0Occurrence : source.AromaticCanonicalOccurrence carrierFuel :=
  ⟨leftChild0Frame, leftChild0Frame_mem⟩

def leftChild1Occurrence : source.AromaticCanonicalOccurrence carrierFuel :=
  ⟨leftChild1Frame, leftChild1Frame_mem⟩

def rightChild0Occurrence : source.AromaticCanonicalOccurrence carrierFuel :=
  ⟨rightChild0Frame, rightChild0Frame_mem⟩

def rightChild1Occurrence : source.AromaticCanonicalOccurrence carrierFuel :=
  ⟨rightChild1Frame, rightChild1Frame_mem⟩

/-! ## Concrete reroot cursors -/

def rootCursor : source.AromaticCanonicalRerootCursor carrierFuel :=
  { occurrence := rootOccurrence, previous? := none }

def leftBranchCursor : source.AromaticCanonicalRerootCursor carrierFuel :=
  { occurrence := leftBranchOccurrence, previous? := some rootOccurrence }

def rightBranchCursor : source.AromaticCanonicalRerootCursor carrierFuel :=
  { occurrence := rightBranchOccurrence, previous? := some rootOccurrence }

def leftChild0Cursor : source.AromaticCanonicalRerootCursor carrierFuel :=
  { occurrence := leftChild0Occurrence, previous? := some leftBranchOccurrence }

def leftChild1Cursor : source.AromaticCanonicalRerootCursor carrierFuel :=
  { occurrence := leftChild1Occurrence, previous? := some leftBranchOccurrence }

def rightChild0Cursor : source.AromaticCanonicalRerootCursor carrierFuel :=
  { occurrence := rightChild0Occurrence, previous? := some rightBranchOccurrence }

def rightChild1Cursor : source.AromaticCanonicalRerootCursor carrierFuel :=
  { occurrence := rightChild1Occurrence, previous? := some rightBranchOccurrence }

@[simp] theorem leftBranchCursor_node :
    leftBranchCursor.occurrence.1.node = leftBranchNode := rfl

@[simp] theorem rightBranchCursor_node :
    rightBranchCursor.occurrence.1.node = rightBranchNode := rfl

/-! ### Actual zipper expansions -/

theorem rootCursor_children :
    source.aromaticCanonicalRerootChildren rootCursor =
      [leftBranchCursor, rightBranchCursor] := by
  rfl

theorem leftBranchCursor_children :
    source.aromaticCanonicalRerootChildren leftBranchCursor =
      [leftChild0Cursor, leftChild1Cursor] := by
  rfl

theorem rightBranchCursor_children :
    source.aromaticCanonicalRerootChildren rightBranchCursor =
      [rightChild0Cursor, rightChild1Cursor] := by
  rfl

theorem leftChild0Cursor_children :
    source.aromaticCanonicalRerootChildren leftChild0Cursor = [] := by
  rfl

theorem leftChild1Cursor_children :
    source.aromaticCanonicalRerootChildren leftChild1Cursor = [] := by
  rfl

theorem rightChild0Cursor_children :
    source.aromaticCanonicalRerootChildren rightChild0Cursor = [] := by
  rfl

theorem rightChild1Cursor_children :
    source.aromaticCanonicalRerootChildren rightChild1Cursor = [] := by
  rfl

/-- Path validity at the root cursor. -/
theorem rootCursor_valid :
    source.AromaticCanonicalRerootCursorValid rootCursor := by
  trivial

/-- Path validity at the left branch cursor. -/
theorem leftBranchCursor_valid :
    source.AromaticCanonicalRerootCursorValid leftBranchCursor := by
  unfold AuthoritativeChemicalInput.AromaticCanonicalRerootCursorValid
  change leftBranchFrame ∈ source.aromaticCanonicalRerootNeighborFrames
    (fuel := carrierFuel) rootFrame
  -- The incoming coordinate is the root frame, which is the tree parent of address `[0]`.
  exact (source.mem_aromaticCanonicalRerootNeighborFrames_iff
    (fuel := carrierFuel) rootFrame leftBranchFrame).mpr
    ⟨leftBranchFrame_mem, ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩⟩

/-- Path validity at the right branch cursor. -/
theorem rightBranchCursor_valid :
    source.AromaticCanonicalRerootCursorValid rightBranchCursor := by
  unfold AuthoritativeChemicalInput.AromaticCanonicalRerootCursorValid
  change rightBranchFrame ∈ source.aromaticCanonicalRerootNeighborFrames
    (fuel := carrierFuel) rootFrame
  exact (source.mem_aromaticCanonicalRerootNeighborFrames_iff
    (fuel := carrierFuel) rootFrame rightBranchFrame).mpr
    ⟨rightBranchFrame_mem, ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩⟩

/-! ## Explicit label reader -/

/-- The explicit witness reader.  Branch roots and the center are unlabelled; the left branch
children receive uppercase `R` and `S`; the right branch children receive uppercase `R` and
lowercase pseudoasymmetric `r`. -/
def read (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    Option AromaticCanonicalAuxiliaryLabel :=
  if cursor.occurrence.1.address = [0, 0] then some (.chiral .R)
  else if cursor.occurrence.1.address = [0, 1] then some (.chiral .S)
  else if cursor.occurrence.1.address = [1, 0] then some (.chiral .R)
  else if cursor.occurrence.1.address = [1, 1] then some (.pseudoasymmetric .r)
  else none

@[simp] theorem read_root : read rootCursor = none := by
  simp [read, rootCursor, rootOccurrence, rootFrame]

@[simp] theorem read_leftBranch : read leftBranchCursor = none := by
  simp [read, leftBranchCursor, leftBranchOccurrence, leftBranchFrame]

@[simp] theorem read_rightBranch : read rightBranchCursor = none := by
  simp [read, rightBranchCursor, rightBranchOccurrence, rightBranchFrame]

@[simp] theorem read_leftChild0 : read leftChild0Cursor = some (.chiral .R) := by
  simp [read, leftChild0Cursor, leftChild0Occurrence, leftChild0Frame]

@[simp] theorem read_leftChild1 : read leftChild1Cursor = some (.chiral .S) := by
  simp [read, leftChild1Cursor, leftChild1Occurrence, leftChild1Frame]

@[simp] theorem read_rightChild0 : read rightChild0Cursor = some (.chiral .R) := by
  simp [read, rightChild0Cursor, rightChild0Occurrence, rightChild0Frame]

@[simp] theorem read_rightChild1 :
    read rightChild1Cursor = some (.pseudoasymmetric .r) := by
  simp [read, rightChild1Cursor, rightChild1Occurrence, rightChild1Frame]

/-! ## Terminal cumulative keys -/

/-- The exact cumulative key emitted at a terminal cursor. -/
def terminalKey (node : OfficialCIPNode source.AromaticCanonicalAtom)
    (stage : LocalizedCumulativeRule45Stage)
    (label : Option AromaticCanonicalAuxiliaryLabel) :
    source.AromaticCanonicalCumulativeRule45Key :=
  { constitutional := MoleculeGraph.exactOfficialRuleMajorRootKey node true
    descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
    labels := [[([], label)]]
    rankedLabels := [[([], label)]] }

/-- The actual cumulative builder at a terminal cursor emits exactly `terminalKey`. -/
theorem build_terminal
    (stage : LocalizedCumulativeRule45Stage)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (label : Option AromaticCanonicalAuxiliaryLabel)
    (childrenEq : source.aromaticCanonicalRerootChildren cursor = [])
    (readEq : read cursor = label) :
    ∀ fuel,
      source.buildAromaticCanonicalCumulativeRule45KeyWithRead? stage read fuel cursor =
        some (terminalKey cursor.occurrence.1.node stage label)
  | 0 => by
      simp [AuthoritativeChemicalInput.buildAromaticCanonicalCumulativeRule45KeyWithRead?,
        AuthoritativeChemicalInput.aromaticCanonicalRerootChildren?, childrenEq, readEq,
        terminalKey]
  | fuel + 1 => by
      simp [AuthoritativeChemicalInput.buildAromaticCanonicalCumulativeRule45KeyWithRead?,
        AuthoritativeChemicalInput.aromaticCanonicalRerootChildren?, childrenEq, readEq,
        terminalKey]

def leftChild0Rule4aKey : source.AromaticCanonicalCumulativeRule45Key :=
  terminalKey leftChild0Node .rule4a (some (.chiral .R))

def leftChild1Rule4aKey : source.AromaticCanonicalCumulativeRule45Key :=
  terminalKey leftChild1Node .rule4a (some (.chiral .S))

def rightChild0Rule4aKey : source.AromaticCanonicalCumulativeRule45Key :=
  terminalKey rightChild0Node .rule4a (some (.chiral .R))

def rightChild1Rule4aKey : source.AromaticCanonicalCumulativeRule45Key :=
  terminalKey rightChild1Node .rule4a (some (.pseudoasymmetric .r))

/-! The merge helpers only inspect the descriptor, label, and ranked-label projections of a child
key.  Keeping those projections opaque as named child keys lets the already-proved comparison
lemmas fire before the key structures are unfolded. -/

@[simp] theorem leftChild0Rule4aKey_descriptor :
    leftChild0Rule4aKey.descriptor = [[([], [2])]] := rfl
@[simp] theorem leftChild0Rule4aKey_labels :
    leftChild0Rule4aKey.labels = [[([], some (.chiral .R))]] := rfl
@[simp] theorem leftChild0Rule4aKey_rankedLabels :
    leftChild0Rule4aKey.rankedLabels = [[([], some (.chiral .R))]] := rfl

@[simp] theorem leftChild1Rule4aKey_descriptor :
    leftChild1Rule4aKey.descriptor = [[([], [2])]] := rfl
@[simp] theorem leftChild1Rule4aKey_labels :
    leftChild1Rule4aKey.labels = [[([], some (.chiral .S))]] := rfl
@[simp] theorem leftChild1Rule4aKey_rankedLabels :
    leftChild1Rule4aKey.rankedLabels = [[([], some (.chiral .S))]] := rfl

@[simp] theorem rightChild0Rule4aKey_descriptor :
    rightChild0Rule4aKey.descriptor = [[([], [2])]] := rfl
@[simp] theorem rightChild0Rule4aKey_labels :
    rightChild0Rule4aKey.labels = [[([], some (.chiral .R))]] := rfl
@[simp] theorem rightChild0Rule4aKey_rankedLabels :
    rightChild0Rule4aKey.rankedLabels = [[([], some (.chiral .R))]] := rfl

@[simp] theorem rightChild1Rule4aKey_descriptor :
    rightChild1Rule4aKey.descriptor = [[([], [1])]] := rfl
@[simp] theorem rightChild1Rule4aKey_labels :
    rightChild1Rule4aKey.labels = [[([], some (.pseudoasymmetric .r))]] := rfl
@[simp] theorem rightChild1Rule4aKey_rankedLabels :
    rightChild1Rule4aKey.rankedLabels =
      [[([], some (.pseudoasymmetric .r))]] := rfl

/-! ## Constitutional comparison of the terminal children

The exact-atomic-number comparison is not kernel-reducible through the opaque rational
implementation, so the equal-value case is proved from order reflexivity rather than by
`decide`.  The remaining observations of the four terminal carbon children are finite
natural-number facts. -/

theorem compareExactAtomicNumber_eq_self
    (value : DeclarativeCIP.ExactAtomicNumber) :
    ExactOfficialRuleMajorKey.compareExactAtomicNumber value value = Ordering.eq := by
  unfold ExactOfficialRuleMajorKey.compareExactAtomicNumber Ordering.byKey
  simp

/-- Comparison of two explicit singleton layers is a tie whenever the two observed values tie. -/
theorem compareSparseLayers_singleton_eq {α : Type*}
    (compareObservation : α → α → Ordering)
    (left right : α)
    (comparison : compareObservation left right = Ordering.eq) :
    OfficialRuleMajorKey.compareSparseLayers compareObservation
      [[([], left)]] [[([], right)]] = Ordering.eq := by
  simp [OfficialRuleMajorKey.compareSparseLayers, OfficialRuleMajorKey.compareSparseLayer,
    OfficialRuleMajorKey.compareSparseEntry, compareLex, Ordering.byKey, List.compareLex,
    OfficialRuleMajorKey.compareNat, flip, comparison]

theorem compareNat_eq_self (value : Nat) :
    OfficialRuleMajorKey.compareNat value value = Ordering.eq := by
  unfold OfficialRuleMajorKey.compareNat
  exact Std.ReflCmp.compare_self

theorem compareRule1b_eq_self (value : Nat) :
    OfficialRuleMajorKey.compareRule1b value value = Ordering.eq := by
  unfold OfficialRuleMajorKey.compareRule1b
  exact compareNat_eq_self value

theorem listCompareNat_self : ∀ values : List Nat,
    List.compareLex OfficialRuleMajorKey.compareNat values values = Ordering.eq
  | [] => rfl
  | value :: values => by
      rw [List.compareLex_cons_cons, compareNat_eq_self, listCompareNat_self values]
      rfl

theorem compareSparseEntry_eq_self {α : Type*} (compareObservation : α → α → Ordering)
    (reflexive : ∀ value, compareObservation value value = Ordering.eq)
    (entry : OfficialSparseEntry α) :
    OfficialRuleMajorKey.compareSparseEntry compareObservation entry entry = Ordering.eq := by
  rcases entry with ⟨address, value⟩
  unfold OfficialRuleMajorKey.compareSparseEntry
  simp only [compareLex, Ordering.byKey, flip]
  rw [listCompareNat_self address, reflexive value]
  rfl

theorem compareSparseLayer_eq_self {α : Type*} (compareObservation : α → α → Ordering)
    (reflexive : ∀ value, compareObservation value value = Ordering.eq) :
    ∀ layer : List (OfficialSparseEntry α),
      OfficialRuleMajorKey.compareSparseLayer compareObservation layer layer = Ordering.eq
  | [] => rfl
  | entry :: entries => by
      rw [OfficialRuleMajorKey.compareSparseLayer, List.compareLex_cons_cons,
        compareSparseEntry_eq_self compareObservation reflexive entry]
      simpa [OfficialRuleMajorKey.compareSparseLayer] using
        compareSparseLayer_eq_self compareObservation reflexive entries

theorem compareSparseLayers_eq_self {α : Type*} (compareObservation : α → α → Ordering)
    (reflexive : ∀ value, compareObservation value value = Ordering.eq) :
    ∀ layers : List (List (OfficialSparseEntry α)),
      OfficialRuleMajorKey.compareSparseLayers compareObservation layers layers = Ordering.eq
  | [] => rfl
  | layer :: layers => by
      rw [OfficialRuleMajorKey.compareSparseLayers, List.compareLex_cons_cons,
        compareSparseLayer_eq_self compareObservation reflexive layer]
      simpa [OfficialRuleMajorKey.compareSparseLayers] using
        compareSparseLayers_eq_self compareObservation reflexive layers

/-- The constitutional comparator of two terminal root keys ties when Rule 1a, Rule 1b and Rule 2
readings all tie.  This is the actual `compareObserved` path, not a fabricated key comparison. -/
theorem compareObserved_rootKeys_eq
    (leftNode rightNode : OfficialCIPNode source.AromaticCanonicalAtom)
    (rule1a :
      source.molecule.semanticExactOfficialRule1aObservation leftNode =
        source.molecule.semanticExactOfficialRule1aObservation rightNode)
    (rule1b : leftNode.rule1bRootDistance = rightNode.rule1bRootDistance)
    (rule2 :
      (ofLex (source.molecule.toLocalizedMoleculeGraph.officialNodeAtomLabel leftNode)).2 =
        (ofLex (source.molecule.toLocalizedMoleculeGraph.officialNodeAtomLabel rightNode)).2) :
    ExactOfficialRuleMajorKey.compareObserved
      source.molecule.toLocalizedMoleculeGraph
      source.molecule.semanticExactOfficialRule1aObservation
      (MoleculeGraph.exactOfficialRuleMajorRootKey leftNode true)
      (MoleculeGraph.exactOfficialRuleMajorRootKey rightNode true) = Ordering.eq := by
  unfold ExactOfficialRuleMajorKey.compareObserved
    ExactOfficialRuleMajorKey.compareAddressedSourcesObserved
    ExactOfficialRuleMajorKey.observedRule1aLayers
    ExactOfficialRuleMajorKey.rule1bLayers
    ExactOfficialRuleMajorKey.rule2Layers
    MoleculeGraph.exactOfficialRuleMajorRootKey
    OfficialRuleMajorKey.mapSourceLayers
  simp [compareLex, Ordering.byKey, List.compareLex, OfficialRuleMajorKey.compareNat, flip,
    OfficialRuleMajorKey.mapObservation, compareExactAtomicNumber_eq_self,
    compareSparseLayers_singleton_eq, rule1a, rule1b, rule2]
  exact compareSparseLayers_singleton_eq _
    _ _ (compareRule1b_eq_self _)

theorem leftChildren_rule1a_tie :
    source.molecule.semanticExactOfficialRule1aObservation leftChild0Node =
      source.molecule.semanticExactOfficialRule1aObservation leftChild1Node := by
  decide

theorem leftChildren_rule1b_tie :
    leftChild0Node.rule1bRootDistance = leftChild1Node.rule1bRootDistance := by
  decide

theorem leftChildren_rule2_tie :
    (ofLex (source.molecule.toLocalizedMoleculeGraph.officialNodeAtomLabel
        leftChild0Node)).2 =
      (ofLex (source.molecule.toLocalizedMoleculeGraph.officialNodeAtomLabel
        leftChild1Node)).2 := by
  decide

theorem rightChildren_rule1a_tie :
    source.molecule.semanticExactOfficialRule1aObservation rightChild0Node =
      source.molecule.semanticExactOfficialRule1aObservation rightChild1Node := by
  decide

theorem rightChildren_rule1b_tie :
    rightChild0Node.rule1bRootDistance = rightChild1Node.rule1bRootDistance := by
  decide

theorem rightChildren_rule2_tie :
    (ofLex (source.molecule.toLocalizedMoleculeGraph.officialNodeAtomLabel
        rightChild0Node)).2 =
      (ofLex (source.molecule.toLocalizedMoleculeGraph.officialNodeAtomLabel
        rightChild1Node)).2 := by
  decide

theorem leftChildren_constitutional_tie :
    ExactOfficialRuleMajorKey.compareObserved
      source.molecule.toLocalizedMoleculeGraph
      source.molecule.semanticExactOfficialRule1aObservation
      leftChild0Rule4aKey.constitutional leftChild1Rule4aKey.constitutional =
        Ordering.eq :=
  compareObserved_rootKeys_eq leftChild0Node leftChild1Node
    leftChildren_rule1a_tie leftChildren_rule1b_tie leftChildren_rule2_tie

theorem rightChildren_constitutional_tie :
    ExactOfficialRuleMajorKey.compareObserved
      source.molecule.toLocalizedMoleculeGraph
      source.molecule.semanticExactOfficialRule1aObservation
      rightChild0Rule4aKey.constitutional rightChild1Rule4aKey.constitutional =
        Ordering.eq :=
  compareObserved_rootKeys_eq rightChild0Node rightChild1Node
    rightChildren_rule1a_tie rightChildren_rule1b_tie rightChildren_rule2_tie

/-- The two left children are constitutionally equal and both chiral, so their actual Rule-4a
cumulative comparison is an exact tie. -/
theorem compare_leftChildren_rule4a :
    source.compareAromaticCanonicalCumulativeRule45Keys
      leftChild0Rule4aKey leftChild1Rule4aKey = .eq := by
  unfold compareAromaticCanonicalCumulativeRule45Keys
  unfold compareLex Ordering.byKey
  rw [show ExactOfficialRuleMajorKey.compareObserved
      source.molecule.toLocalizedMoleculeGraph
      source.molecule.semanticExactOfficialRule1aObservation
      leftChild0Rule4aKey.constitutional leftChild1Rule4aKey.constitutional =
        Ordering.eq from leftChildren_constitutional_tie]
  simp [leftChild0Rule4aKey, leftChild1Rule4aKey, terminalKey,
    OfficialRuleMajorKey.compareSparseLayers, OfficialRuleMajorKey.compareSparseLayer,
    OfficialRuleMajorKey.compareSparseEntry, compareLex, Ordering.byKey, List.compareLex,
    OfficialRuleMajorKey.compareNat, flip, localizedCumulativeRule45Priority,
    compareLocalizedCumulativeRule45Priority, localizedRule4aPriority]

/-- The two right children are constitutionally equal, the first is chiral and the second is
pseudoasymmetric, so the actual Rule-4a cumulative comparison is strict `gt`. -/
theorem compare_rightChildren_rule4a :
    source.compareAromaticCanonicalCumulativeRule45Keys
      rightChild0Rule4aKey rightChild1Rule4aKey = .gt := by
  unfold compareAromaticCanonicalCumulativeRule45Keys
  unfold compareLex Ordering.byKey
  rw [show ExactOfficialRuleMajorKey.compareObserved
      source.molecule.toLocalizedMoleculeGraph
      source.molecule.semanticExactOfficialRule1aObservation
      rightChild0Rule4aKey.constitutional rightChild1Rule4aKey.constitutional =
        Ordering.eq from rightChildren_constitutional_tie]
  simp [rightChild0Rule4aKey, rightChild1Rule4aKey, terminalKey,
    OfficialRuleMajorKey.compareSparseLayers, OfficialRuleMajorKey.compareSparseLayer,
    OfficialRuleMajorKey.compareSparseEntry, compareLex, Ordering.byKey, List.compareLex,
    OfficialRuleMajorKey.compareNat, flip, localizedCumulativeRule45Priority,
    compareLocalizedCumulativeRule45Priority, localizedRule4aPriority]
  decide

/-! ## Actual branch cumulative keys -/

/-- Expected closed form of the actual cumulative `.rule4a` key at the left branch. -/
def leftBranchRule4aKey : source.AromaticCanonicalCumulativeRule45Key :=
  { constitutional := ExactOfficialRuleMajorKey.assemble
      (MoleculeGraph.exactOfficialRuleMajorRootKey leftBranchNode false)
      [leftChild0Rule4aKey.constitutional, leftChild1Rule4aKey.constitutional]
    descriptor := [[([], [0])]] ++ [[([0], [2]), ([1], [2])]]
    labels := [[([], none)]] ++
      [[([0], some (.chiral .R)), ([1], some (.chiral .S))]]
    rankedLabels := [[([], none)]] ++
      [[([0], some (.chiral .R)), ([0], some (.chiral .S))]] }

/-- Expected closed form of the actual cumulative `.rule4a` key at the right branch. -/
def rightBranchRule4aKey : source.AromaticCanonicalCumulativeRule45Key :=
  { constitutional := ExactOfficialRuleMajorKey.assemble
      (MoleculeGraph.exactOfficialRuleMajorRootKey rightBranchNode false)
      [rightChild0Rule4aKey.constitutional, rightChild1Rule4aKey.constitutional]
    descriptor := [[([], [0])]] ++ [[([0], [2]), ([1], [1])]]
    labels := [[([], none)]] ++
      [[([0], some (.chiral .R)), ([1], some (.pseudoasymmetric .r))]]
    rankedLabels := [[([], none)]] ++
      [[([0], some (.chiral .R)), ([1], some (.pseudoasymmetric .r))]] }

/-- Reverse-direction comparison of the left children; used by the actual ranked-label merge. -/
theorem compare_leftChildren_rule4a_swap :
    source.compareAromaticCanonicalCumulativeRule45Keys
      leftChild1Rule4aKey leftChild0Rule4aKey = .eq := by
  letI : Std.TransCmp source.compareAromaticCanonicalCumulativeRule45Keys :=
    source.compareAromaticCanonicalCumulativeRule45Keys_transCmp
  have oriented := Std.OrientedCmp.eq_swap
    (cmp := source.compareAromaticCanonicalCumulativeRule45Keys)
    (a := leftChild1Rule4aKey) (b := leftChild0Rule4aKey)
  rw [oriented, compare_leftChildren_rule4a]
  rfl

/-- Reverse-direction comparison of the right children; the chiral child is strictly senior, so
the reverse direction is `lt`.  This is the comparison consumed by ranked-sibling assignment. -/
theorem compare_rightChildren_rule4a_swap :
    source.compareAromaticCanonicalCumulativeRule45Keys
      rightChild1Rule4aKey rightChild0Rule4aKey = .lt := by
  letI : Std.TransCmp source.compareAromaticCanonicalCumulativeRule45Keys :=
    source.compareAromaticCanonicalCumulativeRule45Keys_transCmp
  have oriented := Std.OrientedCmp.eq_swap
    (cmp := source.compareAromaticCanonicalCumulativeRule45Keys)
    (a := rightChild1Rule4aKey) (b := rightChild0Rule4aKey)
  rw [oriented, compare_rightChildren_rule4a]
  rfl

theorem build_leftChild0_rule4a :
    source.buildAromaticCanonicalCumulativeRule45KeyWithRead? .rule4a read 3
        leftChild0Cursor = some leftChild0Rule4aKey :=
  build_terminal .rule4a leftChild0Cursor _ leftChild0Cursor_children
    read_leftChild0 3

theorem build_leftChild1_rule4a :
    source.buildAromaticCanonicalCumulativeRule45KeyWithRead? .rule4a read 3
        leftChild1Cursor = some leftChild1Rule4aKey :=
  build_terminal .rule4a leftChild1Cursor _ leftChild1Cursor_children
    read_leftChild1 3

theorem build_rightChild0_rule4a :
    source.buildAromaticCanonicalCumulativeRule45KeyWithRead? .rule4a read 3
        rightChild0Cursor = some rightChild0Rule4aKey :=
  build_terminal .rule4a rightChild0Cursor _ rightChild0Cursor_children
    read_rightChild0 3

theorem build_rightChild1_rule4a :
    source.buildAromaticCanonicalCumulativeRule45KeyWithRead? .rule4a read 3
        rightChild1Cursor = some rightChild1Rule4aKey :=
  build_terminal .rule4a rightChild1Cursor _ rightChild1Cursor_children
    read_rightChild1 3

/-- Two successful `mapM` actions form a successful pair.  This is deliberately phrased with an
abstract action so that unfolding the recursive compiler cannot obscure the two concrete
applications. -/
private theorem list_mapM_pair {α β : Type*} (action : α → Option β)
    (first second : α) (firstResult secondResult : β)
    (firstEq : action first = some firstResult)
    (secondEq : action second = some secondResult) :
    ([first, second] : List α).mapM action = some [firstResult, secondResult] := by
  simp [List.mapM_cons, firstEq, secondEq]

/-- The exact key assembled by one nonterminal compiler step. -/
def branchKey
    (stage : LocalizedCumulativeRule45Stage)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (sorted : List source.AromaticCanonicalCumulativeRule45Key) :
    source.AromaticCanonicalCumulativeRule45Key :=
  { constitutional := ExactOfficialRuleMajorKey.assemble
      (MoleculeGraph.exactOfficialRuleMajorRootKey cursor.occurrence.1.node false)
      (sorted.map fun child => child.constitutional)
    descriptor :=
      [[([], localizedCumulativeRule45Priority stage (read cursor))]] ++
        mergeAromaticCanonicalDescriptorChildren sorted
    labels := [[([], read cursor)]] ++ mergeAromaticCanonicalLabelChildren sorted
    rankedLabels := [[([], read cursor)]] ++
      mergeAromaticCanonicalRankedLabelChildren
        source.compareAromaticCanonicalCumulativeRule45Keys sorted }

/-- One actual compiler step at a nonterminal cursor, expressed in terms of the concrete child
list and the concrete child keys.  Keeping the recursive fuel abstract avoids reducing the child
calls during this step. -/
theorem build_succ_of_children
    (stage : LocalizedCumulativeRule45Stage)
    (fuel : Nat)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (children : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (childrenEq : source.aromaticCanonicalRerootChildren cursor = children)
    (nonempty : children ≠ [])
    (childKeys : List source.AromaticCanonicalCumulativeRule45Key)
    (childEq : children.mapM
        (source.buildAromaticCanonicalCumulativeRule45KeyWithRead? stage read fuel) =
      some childKeys) :
    source.buildAromaticCanonicalCumulativeRule45KeyWithRead? stage read (fuel + 1)
        cursor =
      some (branchKey stage cursor
        (sortAromaticCanonicalCumulativeRule45Keys
          source.compareAromaticCanonicalCumulativeRule45Keys childKeys)) := by
  simp [AuthoritativeChemicalInput.buildAromaticCanonicalCumulativeRule45KeyWithRead?,
    AuthoritativeChemicalInput.aromaticCanonicalRerootChildren?, childrenEq, nonempty,
    childEq, branchKey]

theorem leftChildren_mapM_rule4a :
    ([leftChild0Cursor, leftChild1Cursor] :
        List (source.AromaticCanonicalRerootCursor carrierFuel)).mapM
        (source.buildAromaticCanonicalCumulativeRule45KeyWithRead? .rule4a read 3) =
      some [leftChild0Rule4aKey, leftChild1Rule4aKey] :=
  list_mapM_pair _ _ _ _ _ build_leftChild0_rule4a build_leftChild1_rule4a

theorem rightChildren_mapM_rule4a :
    ([rightChild0Cursor, rightChild1Cursor] :
        List (source.AromaticCanonicalRerootCursor carrierFuel)).mapM
        (source.buildAromaticCanonicalCumulativeRule45KeyWithRead? .rule4a read 3) =
      some [rightChild0Rule4aKey, rightChild1Rule4aKey] :=
  list_mapM_pair _ _ _ _ _ build_rightChild0_rule4a build_rightChild1_rule4a

theorem sort_leftChildren_rule4a :
    sortAromaticCanonicalCumulativeRule45Keys
        source.compareAromaticCanonicalCumulativeRule45Keys
        [leftChild0Rule4aKey, leftChild1Rule4aKey] =
      [leftChild0Rule4aKey, leftChild1Rule4aKey] := by
  simp [sortAromaticCanonicalCumulativeRule45Keys,
    insertAromaticCanonicalCumulativeRule45Key, compare_leftChildren_rule4a]

theorem sort_rightChildren_rule4a :
    sortAromaticCanonicalCumulativeRule45Keys
        source.compareAromaticCanonicalCumulativeRule45Keys
        [rightChild0Rule4aKey, rightChild1Rule4aKey] =
      [rightChild0Rule4aKey, rightChild1Rule4aKey] := by
  simp [sortAromaticCanonicalCumulativeRule45Keys,
    insertAromaticCanonicalCumulativeRule45Key, compare_rightChildren_rule4a]

theorem leftBranch_branchKey :
    branchKey .rule4a leftBranchCursor
        [leftChild0Rule4aKey, leftChild1Rule4aKey] = leftBranchRule4aKey := by
  simp [branchKey, leftBranchRule4aKey, read_leftBranch,
    mergeAromaticCanonicalDescriptorChildren, aromaticCanonicalDescriptorChildLayerCount,
    mergeAromaticCanonicalLabelChildren, aromaticCanonicalLabelChildLayerCount,
    mergeAromaticCanonicalRankedLabelChildren, aromaticCanonicalRankedChildren,
    aromaticCanonicalRankedChildTail, aromaticCanonicalRankedLabelChildLayerCount,
    OfficialRuleMajorKey.prefixLayer, compare_leftChildren_rule4a_swap,
    localizedCumulativeRule45Priority, localizedRule4aPriority]

theorem rightBranch_branchKey :
    branchKey .rule4a rightBranchCursor
        [rightChild0Rule4aKey, rightChild1Rule4aKey] = rightBranchRule4aKey := by
  simp [branchKey, rightBranchRule4aKey, read_rightBranch,
    mergeAromaticCanonicalDescriptorChildren, aromaticCanonicalDescriptorChildLayerCount,
    mergeAromaticCanonicalLabelChildren, aromaticCanonicalLabelChildLayerCount,
    mergeAromaticCanonicalRankedLabelChildren, aromaticCanonicalRankedChildren,
    aromaticCanonicalRankedChildTail, aromaticCanonicalRankedLabelChildLayerCount,
    OfficialRuleMajorKey.prefixLayer, compare_rightChildren_rule4a_swap,
    localizedCumulativeRule45Priority, localizedRule4aPriority]

theorem build_leftBranch_rule4a :
    source.buildAromaticCanonicalCumulativeRule45KeyWithRead? .rule4a read 4
        leftBranchCursor = some leftBranchRule4aKey := by
  have step := build_succ_of_children .rule4a 3 leftBranchCursor
    [leftChild0Cursor, leftChild1Cursor] leftBranchCursor_children (by decide)
    [leftChild0Rule4aKey, leftChild1Rule4aKey] leftChildren_mapM_rule4a
  rw [step, sort_leftChildren_rule4a, leftBranch_branchKey]

theorem build_rightBranch_rule4a :
    source.buildAromaticCanonicalCumulativeRule45KeyWithRead? .rule4a read 4
        rightBranchCursor = some rightBranchRule4aKey := by
  have step := build_succ_of_children .rule4a 3 rightBranchCursor
    [rightChild0Cursor, rightChild1Cursor] rightBranchCursor_children (by decide)
    [rightChild0Rule4aKey, rightChild1Rule4aKey] rightChildren_mapM_rule4a
  rw [step, sort_rightChildren_rule4a, rightBranch_branchKey]

/-! ## Cross-branch constitutional and Rule 3 ties

Both branches are carbon vertices with two terminal carbon children joined by single bonds.  Their
constitutional observations therefore agree sphere by sphere, so the actual cumulative comparator
reaches the Rule 4a descriptor layer.  The layer comparison is a finite priority comparison and is
strict on the right branch. -/

theorem branches_rule1a_layers_tie :
    ExactOfficialRuleMajorKey.observedRule1aLayers
        source.molecule.semanticExactOfficialRule1aObservation
        leftBranchRule4aKey.constitutional.sourceNodes =
      ExactOfficialRuleMajorKey.observedRule1aLayers
        source.molecule.semanticExactOfficialRule1aObservation
        rightBranchRule4aKey.constitutional.sourceNodes := by
  decide

theorem branches_rule1b_layers_tie :
    ExactOfficialRuleMajorKey.rule1bLayers
        leftBranchRule4aKey.constitutional.sourceNodes =
      ExactOfficialRuleMajorKey.rule1bLayers
        rightBranchRule4aKey.constitutional.sourceNodes := by
  decide

theorem branches_rule2_layers_tie :
    ExactOfficialRuleMajorKey.rule2Layers source.molecule.toLocalizedMoleculeGraph
        leftBranchRule4aKey.constitutional.sourceNodes =
      ExactOfficialRuleMajorKey.rule2Layers source.molecule.toLocalizedMoleculeGraph
        rightBranchRule4aKey.constitutional.sourceNodes := by
  decide

/-- Every source interaction is an explicit single covalent bond.  In particular the source
contains no double-bond edge, so there is no Rule-3 geometric decision hidden in the reader-free
branch comparison. -/
theorem source_interactions_are_singleBonds :
    ∀ interaction ∈ source.molecule.interactions,
      ∃ left right, interaction = singleBond left right := by
  intro interaction present
  simp [source] at present
  rcases present with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨_, _, rfl⟩

theorem branches_constitutional_tie :
    ExactOfficialRuleMajorKey.compareObserved
        source.molecule.toLocalizedMoleculeGraph
        source.molecule.semanticExactOfficialRule1aObservation
        leftBranchRule4aKey.constitutional
        rightBranchRule4aKey.constitutional = Ordering.eq := by
  have rule1a := branches_rule1a_layers_tie
  have rule1b := branches_rule1b_layers_tie
  have rule2 := branches_rule2_layers_tie
  unfold ExactOfficialRuleMajorKey.compareObserved
    ExactOfficialRuleMajorKey.compareAddressedSourcesObserved
  simp only [compareLex, Ordering.byKey, flip]
  rw [rule1a, rule1b, rule2]
  rw [compareSparseLayers_eq_self _ compareExactAtomicNumber_eq_self _,
    compareSparseLayers_eq_self _ compareRule1b_eq_self _,
    compareSparseLayers_eq_self _ compareNat_eq_self _]
  rfl

/-- Cross-branch reader-free (constitutional) tie.  This is the comparison obtained without
consulting the auxiliary label reader; it is the tie that must hold before the Rule-4a layer can
expose an order reversal. -/
theorem branches_readerFree_rule3_tie :
    ExactOfficialRuleMajorKey.compareObserved
        source.molecule.toLocalizedMoleculeGraph
        source.molecule.semanticExactOfficialRule1aObservation
        leftBranchRule4aKey.constitutional
        rightBranchRule4aKey.constitutional = Ordering.eq :=
  branches_constitutional_tie

/-- The actual cumulative Rule 4a comparison of the two source-canonical branch outputs is strict:
the right branch's pseudoasymmetric child loses to the left branch's chiral child. -/
theorem compare_branches_rule4a :
    source.compareAromaticCanonicalCumulativeRule45Keys
        leftBranchRule4aKey rightBranchRule4aKey = .gt := by
  unfold compareAromaticCanonicalCumulativeRule45Keys
  simp only [compareLex, Ordering.byKey]
  rw [branches_constitutional_tie]
  simp [leftBranchRule4aKey, rightBranchRule4aKey, read_leftBranch, read_rightBranch,
    OfficialRuleMajorKey.compareSparseLayers, OfficialRuleMajorKey.compareSparseLayer,
    OfficialRuleMajorKey.compareSparseEntry, compareLex, List.compareLex, flip,
    OfficialRuleMajorKey.compareNat, compareLocalizedCumulativeRule45Priority,
    localizedRule4aPriority]
  decide

/-! ## Actual Rule-4b populations and reference-count priorities -/

theorem leftBranch_references :
    localizedRule4bReferencesFromRankedLabels leftBranchRule4aKey.rankedLabels =
      [RS.R, RS.S] := by
  decide

theorem rightBranch_references :
    localizedRule4bReferencesFromRankedLabels rightBranchRule4aKey.rankedLabels =
      [RS.R] := by
  decide

theorem leftBranch_referenceCountPriority :
    constitutionalRule4bReferenceCountPriority
        (localizedRule4bReferencesFromRankedLabels leftBranchRule4aKey.rankedLabels) = 1 := by
  decide

theorem rightBranch_referenceCountPriority :
    constitutionalRule4bReferenceCountPriority
        (localizedRule4bReferencesFromRankedLabels rightBranchRule4aKey.rankedLabels) = 2 := by
  decide

theorem referenceCountPriority_leftList :
    constitutionalRule4bReferenceCountPriority [RS.R, RS.S] = 1 := by
  decide

theorem referenceCountPriority_rightList :
    constitutionalRule4bReferenceCountPriority [RS.R] = 2 := by
  decide

/-! ## Actual compound outputs

The compound builder is run at the registered structural budget `evaluationFuel`.  Its Rule-4a
projection is the branch key proved above, its reference populations are the actual ones selected
from that projection, and its reference-count priorities are `1` and `2`.  The readings remain
existential because only the count gate is needed for the opposing comparisons. -/

def leftActualCompoundKey
    (readings : List source.AromaticCanonicalRerootRule4bcReading) :
    source.AromaticCanonicalRerootCompoundRule4bcKey :=
  { rule4aKey := leftBranchRule4aKey
    references := [RS.R, RS.S]
    referenceCountPriority := 1
    readings := readings }

def rightActualCompoundKey
    (readings : List source.AromaticCanonicalRerootRule4bcReading) :
    source.AromaticCanonicalRerootCompoundRule4bcKey :=
  { rule4aKey := rightBranchRule4aKey
    references := [RS.R]
    referenceCountPriority := 2
    readings := readings }

theorem build_leftBranchCompoundRule4bc :
    ∃ readings, source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
        read evaluationFuel leftBranchCursor = some (leftActualCompoundKey readings) := by
  obtain ⟨readings, readingsComputed⟩ :=
    source.exists_buildAromaticCanonicalRerootRule4bcReadingsWithRead?_at_twice
      read leftBranchCursor leftBranchCursor_valid [some RS.R, some RS.S]
  refine ⟨readings, ?_⟩
  have rule4aEq :
      source.buildAromaticCanonicalCumulativeRule45KeyWithRead? .rule4a read
        (2 * (carrierFuel + 1)) leftBranchCursor = some leftBranchRule4aKey := by
    simpa [evaluationFuel] using build_leftBranch_rule4a
  simp [AuthoritativeChemicalInput.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?,
    evaluationFuel, rule4aEq, leftBranch_references,
    aromaticCanonicalRule4bcReferenceAlternatives,
    referenceCountPriority_leftList, leftActualCompoundKey, readingsComputed]

theorem build_rightBranchCompoundRule4bc :
    ∃ readings, source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
        read evaluationFuel rightBranchCursor = some (rightActualCompoundKey readings) := by
  obtain ⟨readings, readingsComputed⟩ :=
    source.exists_buildAromaticCanonicalRerootRule4bcReadingsWithRead?_at_twice
      read rightBranchCursor rightBranchCursor_valid [some RS.R]
  refine ⟨readings, ?_⟩
  have rule4aEq :
      source.buildAromaticCanonicalCumulativeRule45KeyWithRead? .rule4a read
        (2 * (carrierFuel + 1)) rightBranchCursor = some rightBranchRule4aKey := by
    simpa [evaluationFuel] using build_rightBranch_rule4a
  simp [AuthoritativeChemicalInput.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?,
    evaluationFuel, rule4aEq, rightBranch_references,
    aromaticCanonicalRule4bcReferenceAlternatives,
    referenceCountPriority_rightList, rightActualCompoundKey, readingsComputed]

/-- The shipped public compound comparator omits the Rule-4a gate.  On the actual built outputs
the reference-count gate is decisive and yields `lt`, even though the Rule-4a projections compare
`gt`. -/
theorem compare_actualCompoundOutputs_legacy_lt
    (leftReadings rightReadings : List source.AromaticCanonicalRerootRule4bcReading) :
    source.compareAromaticCanonicalRerootCompoundRule4bcKeys
        (leftActualCompoundKey leftReadings) (rightActualCompoundKey rightReadings) = .lt := by
  apply source.compareAromaticCanonicalRerootCompoundRule4bcKeys_eq_referenceCount_of_ne
  simp [leftActualCompoundKey, rightActualCompoundKey]

/-- The corrected Rule-4a-prefixed comparator on the same actual built outputs returns `gt`,
because the strict Rule-4a projection decides before the reference-count gate. -/
theorem compare_actualCompoundOutputs_corrected_gt
    (leftReadings rightReadings : List source.AromaticCanonicalRerootRule4bcReading) :
    source.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys
        (leftActualCompoundKey leftReadings) (rightActualCompoundKey rightReadings) = .gt := by
  have decisive : source.compareAromaticCanonicalCumulativeRule45Keys
      (leftActualCompoundKey leftReadings).rule4aKey
      (rightActualCompoundKey rightReadings).rule4aKey ≠ Ordering.eq := by
    simp [leftActualCompoundKey, rightActualCompoundKey, compare_branches_rule4a]
  rw [source.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys_eq_rule4a_of_ne
    (leftActualCompoundKey leftReadings) (rightActualCompoundKey rightReadings) decisive]
  simpa [leftActualCompoundKey, rightActualCompoundKey] using compare_branches_rule4a

/-! ## Actual through-Rule-5 outputs -/

def leftActualCompoundRule45Key
    (priorReadings : List source.AromaticCanonicalRerootRule4bcReading)
    (rule5Readings : List source.AromaticCanonicalRerootRule5Reading) :
    source.AromaticCanonicalRerootCompoundRule45Key :=
  { prior := leftActualCompoundKey priorReadings
    rule5Readings := rule5Readings }

def rightActualCompoundRule45Key
    (priorReadings : List source.AromaticCanonicalRerootRule4bcReading)
    (rule5Readings : List source.AromaticCanonicalRerootRule5Reading) :
    source.AromaticCanonicalRerootCompoundRule45Key :=
  { prior := rightActualCompoundKey priorReadings
    rule5Readings := rule5Readings }

theorem build_leftBranchCompoundRule45 :
    ∃ priorReadings rule5Readings,
      source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
        read evaluationFuel leftBranchCursor =
        some (leftActualCompoundRule45Key priorReadings rule5Readings) := by
  obtain ⟨priorReadings, priorComputed⟩ := build_leftBranchCompoundRule4bc
  have priorEq :
      source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead? read
        (2 * (carrierFuel + 1)) leftBranchCursor =
        some (leftActualCompoundKey priorReadings) := by
    simpa [evaluationFuel] using priorComputed
  obtain ⟨rule5Readings, readingsComputed⟩ :=
    source.exists_buildAromaticCanonicalRerootRule5ReadingsWithRead?_at_twice
      read leftBranchCursor leftBranchCursor_valid (leftActualCompoundKey priorReadings).readings
  refine ⟨priorReadings, rule5Readings, ?_⟩
  simp [AuthoritativeChemicalInput.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?,
    evaluationFuel, priorEq, leftActualCompoundRule45Key, readingsComputed]

theorem build_rightBranchCompoundRule45 :
    ∃ priorReadings rule5Readings,
      source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
        read evaluationFuel rightBranchCursor =
        some (rightActualCompoundRule45Key priorReadings rule5Readings) := by
  obtain ⟨priorReadings, priorComputed⟩ := build_rightBranchCompoundRule4bc
  have priorEq :
      source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead? read
        (2 * (carrierFuel + 1)) rightBranchCursor =
        some (rightActualCompoundKey priorReadings) := by
    simpa [evaluationFuel] using priorComputed
  obtain ⟨rule5Readings, readingsComputed⟩ :=
    source.exists_buildAromaticCanonicalRerootRule5ReadingsWithRead?_at_twice
      read rightBranchCursor rightBranchCursor_valid (rightActualCompoundKey priorReadings).readings
  refine ⟨priorReadings, rule5Readings, ?_⟩
  simp [AuthoritativeChemicalInput.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?,
    evaluationFuel, priorEq, rightActualCompoundRule45Key, readingsComputed]

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.source
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.source_structurallyWellFormed?
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.source_structurallyWellFormed
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.rootCursor_children
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.leftBranchCursor_children
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.rightBranchCursor_children
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.leftChild0Cursor_children
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.leftChild1Cursor_children
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.rightChild0Cursor_children
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.rightChild1Cursor_children
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.leftBranchCursor_valid
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.rightBranchCursor_valid
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.read
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.build_terminal
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.build_leftChild0_rule4a
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.build_leftChild1_rule4a
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.build_rightChild0_rule4a
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.build_rightChild1_rule4a

assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.leftBranchCursor_node
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.rightBranchCursor_node

assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.terminalKey
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.leftChild0Rule4aKey
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.leftChild1Rule4aKey
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.rightChild0Rule4aKey
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.rightChild1Rule4aKey
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.leftChild0Rule4aKey_descriptor
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.leftChild0Rule4aKey_labels
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.leftChild0Rule4aKey_rankedLabels
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.leftChild1Rule4aKey_descriptor
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.leftChild1Rule4aKey_labels
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.leftChild1Rule4aKey_rankedLabels
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.rightChild0Rule4aKey_descriptor
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.rightChild0Rule4aKey_labels
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.rightChild0Rule4aKey_rankedLabels
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.rightChild1Rule4aKey_descriptor
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.rightChild1Rule4aKey_labels
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.rightChild1Rule4aKey_rankedLabels

assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.compareExactAtomicNumber_eq_self
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.compareSparseLayers_singleton_eq
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.compareNat_eq_self
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.compareRule1b_eq_self
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.listCompareNat_self
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.compareSparseEntry_eq_self
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.compareSparseLayer_eq_self
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.compareSparseLayers_eq_self
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.compareObserved_rootKeys_eq

assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.leftChildren_rule1a_tie
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.leftChildren_rule1b_tie
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.leftChildren_rule2_tie
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.rightChildren_rule1a_tie
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.rightChildren_rule1b_tie
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.rightChildren_rule2_tie
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.leftChildren_constitutional_tie
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.rightChildren_constitutional_tie
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.compare_leftChildren_rule4a
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.compare_rightChildren_rule4a
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.compare_leftChildren_rule4a_swap
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.compare_rightChildren_rule4a_swap

assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.leftBranchRule4aKey
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.rightBranchRule4aKey
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.branchKey
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.build_succ_of_children
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.leftChildren_mapM_rule4a
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.rightChildren_mapM_rule4a
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.sort_leftChildren_rule4a
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.sort_rightChildren_rule4a
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.leftBranch_branchKey
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.rightBranch_branchKey
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.build_leftBranch_rule4a
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.build_rightBranch_rule4a

assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.branches_rule1a_layers_tie
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.branches_rule1b_layers_tie
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.branches_rule2_layers_tie
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.source_interactions_are_singleBonds
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.branches_constitutional_tie
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.branches_readerFree_rule3_tie
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.compare_branches_rule4a

assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.leftBranch_references
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.rightBranch_references
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.leftBranch_referenceCountPriority
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.rightBranch_referenceCountPriority
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.referenceCountPriority_leftList
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.referenceCountPriority_rightList

assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.leftActualCompoundKey
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.rightActualCompoundKey
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.build_leftBranchCompoundRule4bc
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.build_rightBranchCompoundRule4bc
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.compare_actualCompoundOutputs_legacy_lt
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.compare_actualCompoundOutputs_corrected_gt
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.leftActualCompoundRule45Key
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.rightActualCompoundRule45Key
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.build_leftBranchCompoundRule45
assert_kernel_only TetraStereo.OneCenter.PublicRule4aGateActualBuilderWitness.build_rightBranchCompoundRule45

end PublicRule4aGateActualBuilderWitness
end TetraStereo.OneCenter
