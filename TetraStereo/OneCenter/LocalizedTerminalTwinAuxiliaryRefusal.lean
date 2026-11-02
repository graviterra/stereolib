import TetraStereo.OneCenter.LocalizedTerminalLigandTieRefusal
import TetraStereo.OneCenter.LocalizedTerminalEndpointObservationAbsorption
import TetraStereo.OneCenter.LocalizedPhysicalLeafModelNone
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal

/-!
# Actual terminal twins force a bare Rule-45 descriptor refusal

Two distinct outward reroot child cursors of one actual four-ligand occurrence frame represent
terminal physical neighbor atoms.  The physical terminal data are graph-level: each node denotes a
real atom, its only physical neighbor is the frame centre atom, and that bond has order one.  From
that data this module derives, rather than assumes:

* the executable reroot expansion of each twin is empty, using the exact incoming cut and address;
* the concrete Rule-45 auxiliary model stores `none` at each twin, using the sibling physical-leaf
  model theorem;
* the actual dependency label read at each twin is therefore `none`;
* a Rule-3 double-bond edge is excluded at each terminal twin;
* the two actual terminal compound Rules-4b--5 keys tie in both directions;
* the all-pairs strict coherence gate cannot accept any tracked order of the actual four-ligand
  frame; and hence
* the actual bare occurrence Rule-45 descriptor refuses.

No label, key, comparison or sort-success premise is supplied.  The only structural inputs beyond
the target frame are the physical graph facts of the two terminal twin atoms.
-/

/-! ## Physical leaves have no executable reroot children -/

/-- A real node whose only physical neighbor is its official parent, with a single bond to that
parent, has no executable official child copies. -/
theorem executableOfficialChildCopies_eq_nil_of_neighborFinset_singleton
    (input : CertifiedLocalizedCIPInput) (node : OfficialCIPNode input.Atom)
    (current parent : input.Atom)
    (currentObserved : node.current? = some current)
    (parentObserved : node.parent? = some parent)
    (neighbors : input.moleculeGraph.neighborFinset current = {parent})
    (singleBond : input.moleculeGraph.bond current parent = 1) :
    input.executableOfficialChildCopies node = [] := by
  simp only [executableOfficialChildCopies, currentObserved, parentObserved,
    executableOfficialNeighborCopies, neighbors, Finset.sort_singleton]
  simp [singleBond]

/-- A non-duplicate node with no executable official child copies has no executable official
children. -/
theorem executableOfficialCIPChildren_eq_nil_of_childCopies_eq_nil
    (input : CertifiedLocalizedCIPInput) (node : OfficialCIPNode input.Atom)
    (nonduplicate : node.isDuplicateLeaf = false)
    (copiesNil : input.executableOfficialChildCopies node = []) :
    input.executableOfficialCIPChildren node = [] := by
  simp [executableOfficialCIPChildren, nonduplicate, copiesNil]

/-- A non-duplicate node with no official children has no intended children, provided the incoming
coordinate is its carrier parent (so every parent frame is cut) and the frame's address is one
official slot below the parent. -/
theorem executableChildren_eq_nil_of_officialChildren_eq_nil
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (parent child : input.LocalizedRerootCursor fuel)
    (incoming : child.previous? = some parent.occurrence)
    (slot : Nat)
    (address : child.occurrence.1.address =
      parent.occurrence.1.address ++ [slot])
    (nonduplicate : child.occurrence.1.node.isDuplicateLeaf = false)
    (officialNil : input.executableOfficialCIPChildren child.occurrence.1.node = []) :
    input.executableLocalizedRerootChildren child = [] := by
  have sourceDerived : input.DeclarativeLocalizedOccurrence fuel child.occurrence.1 :=
    (input.mem_localizedOccurrences_iff fuel child.occurrence.1).mp child.occurrence.2
  have outwardFilter :
      (input.localizedCarrierOutwardChildFrames (fuel := fuel) child.occurrence.1).filter
        (fun frame => frame.address != parent.occurrence.1.address) = [] := by
    rw [List.filter_eq_nil_iff]
    intro candidate candidatePresent
    rw [localizedCarrierOutwardChildFrames, List.mem_filter] at candidatePresent
    obtain ⟨candidateCarrier, conditions⟩ := candidatePresent
    simp only [Bool.and_eq_true, beq_iff_eq] at conditions
    have candidateDerived :
        input.DeclarativeLocalizedOccurrence fuel candidate :=
      (input.mem_localizedOccurrences_iff fuel candidate).mp candidateCarrier
    have nonempty : candidate.address ≠ [] := by
      intro empty
      have lengthCondition : candidate.address.length =
          child.occurrence.1.address.length + 1 := conditions.1.2
      rw [empty, address] at lengthCondition
      simp at lengthCondition
    have decomp : candidate.address =
        candidate.address.dropLast ++ [candidate.address.getLast nonempty] :=
      (List.dropLast_concat_getLast nonempty).symm
    have candidateAddress : candidate.address =
        child.occurrence.1.address ++ [candidate.address.getLast nonempty] := by
      calc
        candidate.address =
            candidate.address.dropLast ++ [candidate.address.getLast nonempty] := decomp
        _ = child.occurrence.1.address ++ [candidate.address.getLast nonempty] := by
          rw [conditions.2]
    obtain ⟨node, nodeAtSlot, candidateEq⟩ :=
      input.declarativeLocalizedOccurrence_immediate_child sourceDerived candidateDerived
        conditions.1.1 (candidate.address.getLast nonempty) candidateAddress
    rw [officialNil] at nodeAtSlot
    simp at nodeAtSlot
  have parentFilter :
      (input.localizedCarrierParentFrames (fuel := fuel) child.occurrence.1).filter
        (fun frame => frame.address != parent.occurrence.1.address) = [] := by
    rw [List.filter_eq_nil_iff]
    intro candidate candidatePresent
    rw [localizedCarrierParentFrames, List.mem_filter] at candidatePresent
    obtain ⟨_, conditions⟩ := candidatePresent
    simp only [Bool.and_eq_true, beq_iff_eq] at conditions
    have candidateAddress : candidate.address = parent.occurrence.1.address := by
      rw [conditions.2, address, List.dropLast_concat]
    simp [candidateAddress]
  have intended : input.intendedLocalizedRerootChildFrames child = [] := by
    unfold intendedLocalizedRerootChildFrames
    rw [if_neg (by simpa using nonduplicate)]
    rw [incoming]
    dsimp only
    rw [localizedRerootNeighborFrames, List.filter_append, parentFilter,
      outwardFilter, List.append_nil]
  unfold executableLocalizedRerootChildren
  have attached : (input.intendedLocalizedRerootChildFrames child).attach = [] := by
    rw [intended]
    rfl
  rw [attached]
  rfl

/-- Physical terminal data at one reroot cursor: the node is a real atom, its only physical
neighbor is the incoming parent atom, that bond is single, the node is not a duplicate leaf, and
the occurrence address is one official slot below the parent.  These are exactly the inputs of the
leaf expansion bridge. -/
theorem physicalLeaf_terminal
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (parent child : input.LocalizedRerootCursor fuel)
    (leafAtom parentAtom : input.Atom)
    (incoming : child.previous? = some parent.occurrence)
    (slot : Nat)
    (address : child.occurrence.1.address =
      parent.occurrence.1.address ++ [slot])
    (actual : input.ActualPhysicalAtomAtNode child.occurrence.1.node leafAtom)
    (parentObserved : child.occurrence.1.node.parent? = some parentAtom)
    (neighbors : input.moleculeGraph.neighborFinset leafAtom = {parentAtom})
    (singleBond : input.moleculeGraph.bond leafAtom parentAtom = 1)
    (nonduplicate : child.occurrence.1.node.isDuplicateLeaf = false) :
    input.executableLocalizedRerootChildren? child = some [] := by
  have copiesNil := executableOfficialChildCopies_eq_nil_of_neighborFinset_singleton
    input child.occurrence.1.node leafAtom parentAtom actual.2 parentObserved neighbors singleBond
  have officialNil := executableOfficialCIPChildren_eq_nil_of_childCopies_eq_nil
    input child.occurrence.1.node nonduplicate copiesNil
  have childrenNil := executableChildren_eq_nil_of_officialChildren_eq_nil
    input parent child incoming slot address nonduplicate officialNil
  rw [executableLocalizedRerootChildren?_eq_some, childrenNil]

/-- Physical terminal data also exclude a Rule-3 double-bond edge at the same occurrence. -/
theorem not_hasRule3DoubleBondEdge_of_physicalLeaf
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (leafAtom parentAtom : input.Atom)
    (currentObserved : occurrence.1.node.current? = some leafAtom)
    (parentObserved : occurrence.1.node.parent? = some parentAtom)
    (singleBond : input.moleculeGraph.bond leafAtom parentAtom = 1) :
    ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence := by
  rintro ⟨_real, current, parent, currentComputed, parentComputed, doubleBond⟩
  rw [currentObserved] at currentComputed
  rw [parentObserved] at parentComputed
  have currentEq : current = leafAtom := (Option.some.inj currentComputed).symm
  have parentEq : parent = parentAtom := (Option.some.inj parentComputed).symm
  subst current
  subst parent
  have symmetric : input.moleculeGraph.bond parentAtom leafAtom = 1 := by
    simpa [input.moleculeGraph.bond_symm] using singleBond
  rw [symmetric] at doubleBond
  exact absurd doubleBond (by decide)

/-! ## Actual atom labels and model labels -/

/-- Equal atomic number and equal mass make the actual official atom labels of two real nodes
equal. -/
theorem officialNodeAtomLabel_eq_of_actualPhysical_z_mass
    (input : CertifiedLocalizedCIPInput)
    (first second : OfficialCIPNode input.Atom)
    (firstAtom secondAtom : input.Atom)
    (firstActual : input.ActualPhysicalAtomAtNode first firstAtom)
    (secondActual : input.ActualPhysicalAtomAtNode second secondAtom)
    (zEq : input.moleculeGraph.atomZ firstAtom = input.moleculeGraph.atomZ secondAtom)
    (massEq : input.moleculeGraph.atomMass firstAtom =
      input.moleculeGraph.atomMass secondAtom) :
    input.moleculeGraph.officialNodeAtomLabel first =
      input.moleculeGraph.officialNodeAtomLabel second := by
  simp [MoleculeGraph.officialNodeAtomLabel, MoleculeGraph.rawCIPAtomLabel,
    firstActual.1, firstActual.2, secondActual.1, secondActual.2, zEq, massEq]

/-- The actual Rule-45 CIP model stores `none` at an actual physical leaf occurrence. -/
theorem modelState_eq_none_of_physicalLeaf
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (atom : input.Atom)
    (actual : input.ActualPhysicalAtomAtNode target.1.node atom)
    (cardLe : (input.moleculeGraph.neighborFinset atom).card ≤ 1)
    (state : input.LocalizedAuxiliaryState fuel)
    (model : (input.localizedAuxiliaryOccurrenceSystem
      (input.localizedOccurrenceRule45AuxiliarySemantics fuel)).CIPModel state) :
    state target = none :=
  input.localizedOccurrenceRule45CIPModel_eq_none_of_actualPhysical_neighborCard_le_one
    target atom actual cardLe model

/-- The actual dependency label read at a cursor is `none` whenever the model state is `none`
there. -/
theorem localizedDependencyLabel_eq_none_of_state_eq_none
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (state : input.LocalizedAuxiliaryState fuel)
    (cursor : input.LocalizedRerootCursor fuel)
    (stateNone : state cursor.occurrence = none) :
    input.localizedDependencyLabel target (input.localizedDependencyView state target) cursor =
      none := by
  unfold localizedDependencyLabel
  split
  · simpa [localizedDependencyView] using stateNone
  · rfl

/-- The actual dependency label at a physical leaf cursor is `none`. -/
theorem localizedDependencyLabel_eq_none_of_physicalLeaf
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (cursor : input.LocalizedRerootCursor fuel) (atom : input.Atom)
    (actual : input.ActualPhysicalAtomAtNode cursor.occurrence.1.node atom)
    (cardLe : (input.moleculeGraph.neighborFinset atom).card ≤ 1)
    (state : input.LocalizedAuxiliaryState fuel)
    (model : (input.localizedAuxiliaryOccurrenceSystem
      (input.localizedOccurrenceRule45AuxiliarySemantics fuel)).CIPModel state) :
    input.localizedDependencyLabel target (input.localizedDependencyView state target) cursor =
      none :=
  localizedDependencyLabel_eq_none_of_state_eq_none input target state cursor
    (modelState_eq_none_of_physicalLeaf input cursor.occurrence atom actual cardLe state model)

/-! ## Canonical terminal compound Rules-4b--5 keys -/

/-- The cumulative key of a terminal node: canonical constitutional root, one empty-observation
label layer, and the stage priority vector of the empty label. -/
def terminalCumulativeKey (input : CertifiedLocalizedCIPInput)
    (node : OfficialCIPNode input.Atom) (stage : LocalizedCumulativeRule45Stage) :
    input.LocalizedRerootCumulativeRule45Key :=
  { constitutional := input.moleculeGraph.officialRuleMajorRootKey node true
    descriptor := [[([], localizedCumulativeRule45Priority stage none)]]
    labels := [[([], (none : Option LocalizedAuxiliaryLabel))]]
    rankedLabels := [[([], (none : Option LocalizedAuxiliaryLabel))]] }

/-- The single no-reference Rule-4b/4c reading of a terminal node. -/
def terminalReading (input : CertifiedLocalizedCIPInput)
    (node : OfficialCIPNode input.Atom) : input.LocalizedRerootRule4bcReading :=
  { reference? := none
    rule4bKey := terminalCumulativeKey input node .rule4a
    rule4cKey := terminalCumulativeKey input node .rule4cNoReference }

/-- The compound Rules-4b/4c key of a terminal node. -/
def terminalCompound4bc (input : CertifiedLocalizedCIPInput)
    (node : OfficialCIPNode input.Atom) : input.LocalizedRerootCompoundRule4bcKey :=
  { rule4aKey := terminalCumulativeKey input node .rule4a
    references := []
    referenceCountPriority := 0
    readings := [terminalReading input node] }

/-- The one common-`R`/common-`S` Rule-5 reading of a terminal node. -/
def terminalRule5Reading (input : CertifiedLocalizedCIPInput)
    (node : OfficialCIPNode input.Atom) : input.LocalizedRerootRule5Reading :=
  { prior := terminalReading input node
    commonR := terminalCumulativeKey input node (.rule5NoRule4bReference .R)
    commonS := terminalCumulativeKey input node (.rule5NoRule4bReference .S) }

/-- The through-Rule-5 compound key of a terminal node. -/
def terminalCompound45 (input : CertifiedLocalizedCIPInput)
    (node : OfficialCIPNode input.Atom) : input.LocalizedRerootCompoundRule45Key :=
  { prior := terminalCompound4bc input node
    rule5Readings := [terminalRule5Reading input node] }

/-- The `do`-notation form of the `Option` bind on a successful value. -/
private theorem terminalBindApply {α β : Type} (value : α)
    (continuation : α → Option β) :
    (some value : Option α) >>= continuation = continuation value :=
  rfl

/-! ## The reader-parameterized compiler on a terminal cursor

These lemmas are the only place where the child reader is used.  A terminal cursor reads `some []`
from the supplied reader and its actual dependency label is `none`; everything the compiler emits
is then the canonical terminal key above. -/

/-- The reader-parameterized cumulative compiler returns the canonical terminal cumulative key at
every stage and budget. -/
theorem buildCumulative_terminal_actual
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (terminal : readChildren cursor = some [])
    (labelNone : input.localizedDependencyLabel target view cursor = none)
    (stage : LocalizedCumulativeRule45Stage) (fuel : Nat) :
    WithChildren.buildLocalizedRerootCumulativeRule45KeyExec?
        input readChildren stage target view fuel cursor =
      some (terminalCumulativeKey input cursor.occurrence.1.node stage) := by
  cases fuel with
  | zero =>
      simp only [WithChildren.buildLocalizedRerootCumulativeRule45KeyExec?, terminal,
        labelNone]
      rfl
  | succ fuel =>
      simp only [WithChildren.buildLocalizedRerootCumulativeRule45KeyExec?, terminal,
        labelNone]
      rfl

/-- The reader-parameterized no-reference Rule-4b/4c reading compiler returns the canonical
terminal reading. -/
theorem buildReading_none_terminal_actual
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (terminal : readChildren cursor = some [])
    (labelNone : input.localizedDependencyLabel target view cursor = none)
    (fuel : Nat) :
    WithChildren.buildLocalizedRerootRule4bcReadingExec?
        input readChildren target view fuel cursor none =
      some (terminalReading input cursor.occurrence.1.node) := by
  simp only [WithChildren.buildLocalizedRerootRule4bcReadingExec?, terminalBindApply,
    buildCumulative_terminal_actual input readChildren target view cursor terminal labelNone
      .rule4a fuel,
    buildCumulative_terminal_actual input readChildren target view cursor terminal labelNone
      .rule4cNoReference fuel]
  rfl

/-- The reader-parameterized alternative-list compiler returns the single canonical terminal
reading. -/
theorem buildReadings_terminal_actual
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (terminal : readChildren cursor = some [])
    (labelNone : input.localizedDependencyLabel target view cursor = none)
    (fuel : Nat) :
    WithChildren.buildLocalizedRerootRule4bcReadingsExec?
        input readChildren target view fuel cursor [none] =
      some [terminalReading input cursor.occurrence.1.node] := by
  simp only [WithChildren.buildLocalizedRerootRule4bcReadingsExec?, terminalBindApply,
    buildReading_none_terminal_actual input readChildren target view cursor terminal labelNone fuel]

/-- The reader-parameterized compound Rules-4b/4c compiler returns the canonical terminal compound
key. -/
theorem buildCompound4bc_terminal_actual
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (terminal : readChildren cursor = some [])
    (labelNone : input.localizedDependencyLabel target view cursor = none)
    (fuel : Nat) :
    WithChildren.buildLocalizedRerootCompoundRule4bcKeyExec?
        input readChildren target view fuel cursor =
      some (terminalCompound4bc input cursor.occurrence.1.node) := by
  simp only [WithChildren.buildLocalizedRerootCompoundRule4bcKeyExec?, terminalBindApply,
    buildCumulative_terminal_actual input readChildren target view cursor terminal labelNone
      .rule4a fuel,
    terminalCumulativeKey, terminalCompound4bc, List.isEmpty_nil, if_true,
    localizedRule4bReferencesFromRankedLabels, localizedFirstChiralRankPopulation,
    localizedFirstChiralRankPopulationInLayer, localizedRule4bReferencesFromPopulation,
    localizedRule4bcReferenceAlternatives, constitutionalRule4bReferenceCountPriority,
    buildReadings_terminal_actual input readChildren target view cursor terminal labelNone fuel]

/-- The reader-parameterized Rule-5 reading compiler returns the canonical terminal common
reading. -/
theorem buildRule5Reading_terminal_actual
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (terminal : readChildren cursor = some [])
    (labelNone : input.localizedDependencyLabel target view cursor = none)
    (fuel : Nat) :
    WithChildren.buildLocalizedRerootRule5ReadingExec?
        input readChildren target view fuel cursor
        (terminalReading input cursor.occurrence.1.node) =
      some (terminalRule5Reading input cursor.occurrence.1.node) := by
  simp only [WithChildren.buildLocalizedRerootRule5ReadingExec?, terminalBindApply,
    localizedRule5StageFor, terminalReading,
    buildCumulative_terminal_actual input readChildren target view cursor terminal labelNone
      (.rule5NoRule4bReference .R) fuel,
    buildCumulative_terminal_actual input readChildren target view cursor terminal labelNone
      (.rule5NoRule4bReference .S) fuel]
  rfl

/-- The reader-parameterized Rule-5 reading-list compiler returns the single canonical terminal
reading. -/
theorem buildRule5Readings_terminal_actual
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (terminal : readChildren cursor = some [])
    (labelNone : input.localizedDependencyLabel target view cursor = none)
    (fuel : Nat) :
    WithChildren.buildLocalizedRerootRule5ReadingsExec?
        input readChildren target view fuel cursor
        [terminalReading input cursor.occurrence.1.node] =
      some [terminalRule5Reading input cursor.occurrence.1.node] := by
  simp only [WithChildren.buildLocalizedRerootRule5ReadingsExec?, terminalBindApply,
    buildRule5Reading_terminal_actual input readChildren target view cursor terminal labelNone
      fuel]

/-- The reader-parameterized through-Rule-5 compound compiler returns the canonical terminal
compound key. -/
theorem buildCompound45_terminal_actual
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (terminal : readChildren cursor = some [])
    (labelNone : input.localizedDependencyLabel target view cursor = none)
    (fuel : Nat) :
    WithChildren.buildLocalizedRerootCompoundRule45KeyExec?
        input readChildren target view fuel cursor =
      some (terminalCompound45 input cursor.occurrence.1.node) := by
  simp only [WithChildren.buildLocalizedRerootCompoundRule45KeyExec?, terminalBindApply,
    terminalCompound45, terminalCompound4bc,
    buildCompound4bc_terminal_actual input readChildren target view cursor terminal labelNone
      fuel,
    buildRule5Readings_terminal_actual input readChildren target view cursor terminal labelNone
      fuel]

/-- The original state-relative through-Rule-5 compiler, run on a terminal cursor whose actual
dependency label is `none`, returns the canonical terminal compound key. -/
theorem buildCompound45?_terminal_actual
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (terminal : input.executableLocalizedRerootChildren? cursor = some [])
    (labelNone : input.localizedDependencyLabel target view cursor = none)
    (fuel : Nat) :
    input.buildLocalizedRerootCompoundRule45Key? target view fuel cursor =
      some (terminalCompound45 input cursor.occurrence.1.node) := by
  rw [input.buildLocalizedRerootCompoundRule45Key?_eq_buildLocalizedRerootCompoundRule45KeyExec?]
  rw [← WithChildren.buildLocalizedRerootCompoundRule45KeyExec?_eq_original
    input input.executableLocalizedRerootChildren? (fun _ => rfl) target view fuel cursor]
  exact buildCompound45_terminal_actual input input.executableLocalizedRerootChildren?
    target view cursor terminal labelNone fuel

/-! ## Tie of two actual terminal compound keys -/

private theorem terminalSelfCompareNat (value : Nat) :
    OfficialRuleMajorKey.compareNat value value = Ordering.eq := by
  unfold OfficialRuleMajorKey.compareNat
  exact Std.ReflOrd.compare_self

private theorem terminalSelfListCompareLex {α : Type*} (cmp : α → α → Ordering)
    (refl : ∀ value, cmp value value = Ordering.eq) :
    ∀ values : List α, List.compareLex cmp values values = Ordering.eq
  | [] => rfl
  | value :: values => by
      rw [List.compareLex_cons_cons, refl value]
      exact terminalSelfListCompareLex cmp refl values

private theorem terminalSelfCompareSparseEntry {α : Type*} (cmp : α → α → Ordering)
    (refl : ∀ value, cmp value value = Ordering.eq)
    (entry : OfficialSparseEntry α) :
    OfficialRuleMajorKey.compareSparseEntry cmp entry entry = Ordering.eq := by
  rcases entry with ⟨path, observation⟩
  have pathEqual :
      Ordering.byKey Prod.fst (flip (List.compareLex OfficialRuleMajorKey.compareNat))
          (path, observation) (path, observation) = Ordering.eq := by
    show List.compareLex OfficialRuleMajorKey.compareNat path path = Ordering.eq
    exact terminalSelfListCompareLex OfficialRuleMajorKey.compareNat
      terminalSelfCompareNat path
  have observationEqual :
      Ordering.byKey Prod.snd cmp (path, observation) (path, observation) = Ordering.eq := by
    show cmp observation observation = Ordering.eq
    exact refl observation
  unfold OfficialRuleMajorKey.compareSparseEntry
  simp only [compareLex]
  rw [pathEqual, observationEqual]
  rfl

private theorem terminalSelfCompareSparseLayer {α : Type*} (cmp : α → α → Ordering)
    (refl : ∀ value, cmp value value = Ordering.eq)
    (layer : List (OfficialSparseEntry α)) :
    OfficialRuleMajorKey.compareSparseLayer cmp layer layer = Ordering.eq :=
  terminalSelfListCompareLex (OfficialRuleMajorKey.compareSparseEntry cmp)
    (fun entry => terminalSelfCompareSparseEntry cmp refl entry) layer

private theorem terminalSelfCompareSparseLayers {α : Type*} (cmp : α → α → Ordering)
    (refl : ∀ value, cmp value value = Ordering.eq)
    (layers : List (List (OfficialSparseEntry α))) :
    OfficialRuleMajorKey.compareSparseLayers cmp layers layers = Ordering.eq :=
  terminalSelfListCompareLex (OfficialRuleMajorKey.compareSparseLayer cmp)
    (fun layer => terminalSelfCompareSparseLayer cmp refl layer) layers

private theorem terminalSelfCompareZero : compare (0 : Nat) 0 = Ordering.eq := by
  decide

/-- Identical canonical terminal descriptors compare equal. -/
private theorem terminalDescriptor_compare_eq (input : CertifiedLocalizedCIPInput)
    (first second : OfficialCIPNode input.Atom) (stage : LocalizedCumulativeRule45Stage) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
      (terminalCumulativeKey input first stage).descriptor
      (terminalCumulativeKey input second stage).descriptor = Ordering.eq := by
  unfold terminalCumulativeKey
  exact terminalSelfCompareSparseLayers compareLocalizedCumulativeRule45Priority
    (fun value => terminalSelfListCompareLex OfficialRuleMajorKey.compareNat
      terminalSelfCompareNat value) _

/-- Two canonical terminal cumulative keys with equal constitutional comparison tie. -/
theorem terminalCumulative_compare_eq (input : CertifiedLocalizedCIPInput)
    (first second : OfficialCIPNode input.Atom)
    (constitutionalEq : OfficialRuleMajorKey.compare
      (input.moleculeGraph.officialRuleMajorRootKey first true)
      (input.moleculeGraph.officialRuleMajorRootKey second true) = Ordering.eq)
    (stage : LocalizedCumulativeRule45Stage) :
    input.compareLocalizedRerootCumulativeRule45Keys
      (terminalCumulativeKey input first stage)
      (terminalCumulativeKey input second stage) = Ordering.eq := by
  simp only [compareLocalizedRerootCumulativeRule45Keys, compareLex, Ordering.byKey,
    terminalCumulativeKey, constitutionalEq,
    terminalSelfCompareSparseLayers compareLocalizedCumulativeRule45Priority
      (fun value => terminalSelfListCompareLex OfficialRuleMajorKey.compareNat
        terminalSelfCompareNat value)]
  rfl

/-- Identical terminal no-reference readings tie under the Rule-4b comparison. -/
theorem terminalReadingByRule4b_compare_eq (input : CertifiedLocalizedCIPInput)
    (first second : OfficialCIPNode input.Atom) :
    input.compareLocalizedRerootRule4bcReadingsByRule4b
      (terminalReading input first) (terminalReading input second) = Ordering.eq := by
  unfold compareLocalizedRerootRule4bcReadingsByRule4b Ordering.byKey
  unfold terminalReading
  exact terminalDescriptor_compare_eq input first second .rule4a

/-- The singleton terminal readings tie under the Rule-4b list comparison. -/
theorem terminalReadingsByRule4b_compare_eq (input : CertifiedLocalizedCIPInput)
    (first second : OfficialCIPNode input.Atom) :
    input.compareLocalizedRerootCompoundRule4bReadings
      [terminalReading input first] [terminalReading input second] = Ordering.eq := by
  unfold compareLocalizedRerootCompoundRule4bReadings
  rw [List.compareLex_cons_cons, terminalReadingByRule4b_compare_eq]
  rfl

/-- Identical terminal no-reference readings tie pointwise under the Rule-4c descriptor
projection. -/
theorem terminalReadingByRule4cDescriptor_compare_eq (input : CertifiedLocalizedCIPInput)
    (first second : OfficialCIPNode input.Atom) :
    Ordering.byKey (fun reading => reading.rule4cKey.descriptor)
      (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority)
      (terminalReading input first) (terminalReading input second) = Ordering.eq := by
  unfold Ordering.byKey
  unfold terminalReading
  exact terminalDescriptor_compare_eq input first second .rule4cNoReference

/-- The singleton terminal readings tie under the Rule-4c list comparison. -/
theorem terminalReadingsByRule4c_compare_eq (input : CertifiedLocalizedCIPInput)
    (first second : OfficialCIPNode input.Atom) :
    input.compareLocalizedRerootCompoundRule4cReadings
      [terminalReading input first] [terminalReading input second] = Ordering.eq := by
  simp only [compareLocalizedRerootCompoundRule4cReadings]
  rw [List.compareLex_cons_cons, terminalReadingByRule4cDescriptor_compare_eq]
  rfl

/-- The canonical terminal compound Rules-4b/4c keys tie whenever their primitive constitutional
comparisons tie. -/
theorem terminalCompound4bc_compare_eq (input : CertifiedLocalizedCIPInput)
    (first second : OfficialCIPNode input.Atom)
    (constitutionalEq : OfficialRuleMajorKey.compare
      (input.moleculeGraph.officialRuleMajorRootKey first true)
      (input.moleculeGraph.officialRuleMajorRootKey second true) = Ordering.eq) :
    input.compareLocalizedRerootCompoundRule4bcKeys
      (terminalCompound4bc input first) (terminalCompound4bc input second) = Ordering.eq := by
  simp only [compareLocalizedRerootCompoundRule4bcKeys, compareLex, Ordering.byKey,
    terminalCompound4bc]
  rw [terminalCumulative_compare_eq input first second constitutionalEq .rule4a,
    terminalSelfCompareZero,
    terminalReadingsByRule4b_compare_eq input first second,
    terminalReadingsByRule4c_compare_eq input first second]
  rfl

/-- Identical terminal Rule-5 readings tie pointwise under the common-`R` descriptor
projection. -/
theorem terminalRule5Descriptor_compare_eq (input : CertifiedLocalizedCIPInput)
    (first second : OfficialCIPNode input.Atom) :
    Ordering.byKey (input.localizedRerootRule5Descriptor .R)
      (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority)
      (terminalRule5Reading input first) (terminalRule5Reading input second) = Ordering.eq := by
  unfold Ordering.byKey
  unfold localizedRerootRule5Descriptor
  unfold terminalRule5Reading
  exact terminalDescriptor_compare_eq input first second (.rule5NoRule4bReference .R)

/-- The singleton canonical terminal Rule-5 readings tie under the common-`R` comparison. -/
theorem terminalRule5Readings_compare_eq (input : CertifiedLocalizedCIPInput)
    (first second : OfficialCIPNode input.Atom) :
    input.compareLocalizedRerootCompoundRule5Readings .R
      [terminalRule5Reading input first] [terminalRule5Reading input second] = Ordering.eq := by
  simp only [compareLocalizedRerootCompoundRule5Readings]
  rw [List.compareLex_cons_cons, terminalRule5Descriptor_compare_eq]
  rfl

/-- Two canonical terminal compound through-Rule-5 keys with equal constitutional comparison tie. -/
theorem terminalCompound45_compare_eq (input : CertifiedLocalizedCIPInput)
    (first second : OfficialCIPNode input.Atom)
    (constitutionalEq : OfficialRuleMajorKey.compare
      (input.moleculeGraph.officialRuleMajorRootKey first true)
      (input.moleculeGraph.officialRuleMajorRootKey second true) = Ordering.eq) :
    input.compareLocalizedRerootCompoundRule45Keys
      (terminalCompound45 input first) (terminalCompound45 input second) = Ordering.eq := by
  simp only [compareLocalizedRerootCompoundRule45Keys, compareLex, Ordering.byKey,
    terminalCompound45]
  rw [terminalCompound4bc_compare_eq input first second constitutionalEq,
    terminalRule5Readings_compare_eq input first second]
  rfl

/-! ## Frame slots, outward addresses, and the all-pairs coherence contradiction -/

/-- The cursor at any frame index is a member of the frame. -/
theorem cursorAt_mem (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel) (index : Fin 4) :
    frame.cursorAt index ∈ frame.cursors := by
  unfold LocalizedOccurrenceFourLigandFrame.cursorAt
  exact List.get_mem _ _

/-- Every cursor of an actual four-ligand frame records the target occurrence as its incoming cut,
so its expansion cuts exactly the edge back to the target. -/
theorem cursorAt_previous_eq_target_of_frame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (frameComputed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (index : Fin 4) :
    (frame.cursorAt index).previous? = some target := by
  have derived := input.localizedOccurrenceFourLigandFrame?_sound target frame frameComputed
  exact derived.1.2 _ (cursorAt_mem input frame index)

/-- An outward child frame sits at the parent address extended by one official slot. -/
theorem exists_address_slot_of_mem_outwardChildFrames
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (parent child : input.LocalizedCIPOccurrenceFrame)
    (present : child ∈ input.localizedCarrierOutwardChildFrames (fuel := carrierFuel) parent) :
    ∃ slot, child.address = parent.address ++ [slot] := by
  rw [localizedCarrierOutwardChildFrames, List.mem_filter] at present
  obtain ⟨_carrier, conditions⟩ := present
  simp only [Bool.and_eq_true, beq_iff_eq] at conditions
  have nonempty : child.address ≠ [] := by
    intro empty
    have lengthCondition : child.address.length = parent.address.length + 1 := conditions.1.2
    rw [empty] at lengthCondition
    simp at lengthCondition
  refine ⟨child.address.getLast nonempty, ?_⟩
  calc
    child.address = child.address.dropLast ++ [child.address.getLast nonempty] :=
      (List.dropLast_concat_getLast nonempty).symm
    _ = parent.address ++ [child.address.getLast nonempty] := by rw [conditions.2]

/-- A pairwise relation on a list relates two distinct members in one of the two possible
orientations. -/
private theorem pairwise_or_of_mem {α : Type*} {relation : α → α → Prop}
    {values : List α} (pairwise : values.Pairwise relation)
    {left right : α} (leftMem : left ∈ values) (rightMem : right ∈ values)
    (distinct : left ≠ right) : relation left right ∨ relation right left := by
  induction values with
  | nil => simp at leftMem
  | cons head tail inductionHypothesis =>
      rw [List.pairwise_cons] at pairwise
      obtain ⟨headRel, tailPairwise⟩ := pairwise
      simp only [List.mem_cons] at leftMem rightMem
      rcases leftMem with rfl | leftMem <;> rcases rightMem with rfl | rightMem
      · exact (distinct rfl).elim
      · exact Or.inl (headRel right rightMem)
      · exact Or.inr (headRel left leftMem)
      · exact inductionHypothesis tailPairwise leftMem rightMem

/-- Two strict comparisons at distinct frame indices, one for each orientation, are impossible on
any tracked order whose highest-first list is a permutation of all four indices.  Hence the
all-pairs coherence gate rejects every tracked order at that frame. -/
theorem orderCoherent?_eq_false_of_twin_tie
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (tracked : TrackedLocalizedLigandOrder)
    (trackedPerm : tracked.highestFirst.Perm (List.finRange 4))
    (left right : Fin 4) (distinct : left ≠ right)
    (leftRightTie : ∃ result,
      input.compareLocalizedOccurrenceThroughRule5At? target view frame left right =
        some result ∧ result.ordering = Ordering.eq)
    (rightLeftTie : ∃ result,
      input.compareLocalizedOccurrenceThroughRule5At? target view frame right left =
        some result ∧ result.ordering = Ordering.eq) :
    input.localizedOccurrenceRule45OrderCoherent? target view frame tracked.highestFirst =
      false := by
  cases coherent : input.localizedOccurrenceRule45OrderCoherent?
      target view frame tracked.highestFirst with
  | false => rfl
  | true =>
      exfalso
      have pairwise :=
        (input.localizedOccurrenceRule45OrderCoherent?_eq_true_iff
          target view frame tracked.highestFirst).mp coherent
      have leftMem : left ∈ tracked.highestFirst :=
        trackedPerm.mem_iff.mpr (List.mem_finRange left)
      have rightMem : right ∈ tracked.highestFirst :=
        trackedPerm.mem_iff.mpr (List.mem_finRange right)
      rcases pairwise_or_of_mem pairwise leftMem rightMem distinct with higher | higher
      · rcases leftRightTie with ⟨leftResult, leftComputed, leftOrdering⟩
        rcases higher with ⟨result, compared, ordering⟩
        rw [leftComputed] at compared
        have same : leftResult = result := Option.some.inj compared
        subst result
        rw [leftOrdering] at ordering
        cases ordering
      · rcases rightLeftTie with ⟨rightResult, rightComputed, rightOrdering⟩
        rcases higher with ⟨result, compared, ordering⟩
        rw [rightComputed] at compared
        have same : rightResult = result := Option.some.inj compared
        subst result
        rw [rightOrdering] at ordering
        cases ordering

/-- Distinct tied frame slots force the safe tracked order to refuse. -/
theorem safeLocalizedOccurrenceRule45TrackedOrder?_eq_none_of_twin_tie
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (left right : Fin 4) (distinct : left ≠ right)
    (leftRightTie : ∃ result,
      input.compareLocalizedOccurrenceThroughRule5At? target view frame left right =
        some result ∧ result.ordering = Ordering.eq)
    (rightLeftTie : ∃ result,
      input.compareLocalizedOccurrenceThroughRule5At? target view frame right left =
        some result ∧ result.ordering = Ordering.eq) :
    input.safeLocalizedOccurrenceRule45TrackedOrder? target view frame = none := by
  unfold safeLocalizedOccurrenceRule45TrackedOrder?
  cases trackedComputed : input.localizedOccurrenceRule45TrackedOrder? target view frame with
  | none => rfl
  | some tracked =>
      have trackedPerm := sortFourLocalizedLigandsTracked_perm
        (input.compareLocalizedOccurrenceThroughRule5At? target view frame)
        tracked trackedComputed
      have coherentFalse := orderCoherent?_eq_false_of_twin_tie input target view frame
        tracked trackedPerm left right distinct leftRightTie rightLeftTie
      simp [coherentFalse]

/-! ## The actual comparison at two terminal keys -/

/-- At two frame slots holding actual terminal keys whose constitutional roots tie, the actual
through-Rule-5 comparison succeeds with ordering equality. -/
theorem compareLocalizedOccurrenceThroughRule5At?_terminal_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (leftIndex rightIndex : Fin 4)
    (leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel)
    (leftAt : frame.cursorAt leftIndex = leftCursor)
    (rightAt : frame.cursorAt rightIndex = rightCursor)
    (leftComputed : input.buildLocalizedRerootCompoundRule45Key?
      target view (localizedOccurrenceRerootEvaluationFuel carrierFuel) leftCursor =
        some (terminalCompound45 input leftCursor.occurrence.1.node))
    (rightComputed : input.buildLocalizedRerootCompoundRule45Key?
      target view (localizedOccurrenceRerootEvaluationFuel carrierFuel) rightCursor =
        some (terminalCompound45 input rightCursor.occurrence.1.node))
    (constitutionalEq : OfficialRuleMajorKey.compare
      (input.moleculeGraph.officialRuleMajorRootKey leftCursor.occurrence.1.node true)
      (input.moleculeGraph.officialRuleMajorRootKey rightCursor.occurrence.1.node true) =
        Ordering.eq) :
    ∃ result,
      input.compareLocalizedOccurrenceThroughRule5At? target view frame leftIndex rightIndex =
        some result ∧ result.ordering = Ordering.eq := by
  unfold compareLocalizedOccurrenceThroughRule5At?
  rw [leftAt, rightAt]
  simp only [leftComputed, rightComputed, terminalBindApply]
  refine ⟨_, rfl, ?_⟩
  dsimp only [localizedOccurrenceRule45ComparisonRecord]
  rw [compareLocalizedRerootCompoundThroughRule5_ordering]
  exact terminalCompound45_compare_eq input _ _ constitutionalEq

/-! ## Refusal of the bare descriptor -/

/-- If the bare safe order refuses at a frame, then the bare spatial evidence refuses, because the
evidence compiler is the same `safeLocalizedOccurrenceRule45TrackedOrder?` call at that frame. -/
theorem localizedOccurrenceRule45SpatialEvidence?_eq_none_of_safe_eq_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (frameComputed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (safeNone : input.safeLocalizedOccurrenceRule45TrackedOrder? target view frame = none) :
    input.localizedOccurrenceRule45SpatialEvidence? target view = none := by
  unfold localizedOccurrenceRule45SpatialEvidence?
  cases centerComputed : input.localizedOccurrenceDescriptorCenter? target with
  | none => rfl
  | some center => simp [frameComputed, safeNone]

/-- The bare Rule-45 descriptor refuses whenever the actual four-ligand safe order refuses at the
frame that the descriptor itself computes. -/
theorem localizedOccurrenceRule45Descriptor?_eq_none_of_safe_eq_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (frameComputed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (safeNone : input.safeLocalizedOccurrenceRule45TrackedOrder? target view frame = none) :
    input.localizedOccurrenceRule45Descriptor? target view = none := by
  unfold localizedOccurrenceRule45Descriptor?
  rw [localizedOccurrenceRule45SpatialEvidence?_eq_none_of_safe_eq_none input target view frame
    frameComputed safeNone]
  rfl

/-! ## The central actual terminal-twin refusal theorem -/

/-- Two distinct outward child slots of an actual four-ligand frame hold terminal physical twins:
real atoms whose only physical neighbor is the frame centre atom, joined to it by single bonds,
with equal atomic number and mass.  If the two terminal roots also have equal Rule-1b distance,
then the actual bare occurrence Rule-45 descriptor computed from the actual Rule-45 model view
refuses.

Nothing about labels, compiled keys, comparisons or sort success is assumed.  The labels are
derived as `none` from the sibling physical-leaf model theorem, both directional compound-key ties
are derived from the actual terminal keys, and the safe order is refuted by the all-pairs coherence
gate. -/
theorem localizedOccurrenceRule45Descriptor?_eq_none_of_actualPhysical_terminalTwins
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (state : input.LocalizedAuxiliaryState fuel)
    (model : (input.localizedAuxiliaryOccurrenceSystem
      (input.localizedOccurrenceRule45AuxiliarySemantics fuel)).CIPModel state)
    (frame : input.LocalizedOccurrenceFourLigandFrame fuel)
    (frameComputed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (leftIndex rightIndex : Fin 4)
    (leftCursor rightCursor : input.LocalizedRerootCursor fuel)
    (leftAt : frame.cursorAt leftIndex = leftCursor)
    (rightAt : frame.cursorAt rightIndex = rightCursor)
    (leftOutward : leftCursor.occurrence.1 ∈
      input.localizedCarrierOutwardChildFrames (fuel := fuel) target.1)
    (rightOutward : rightCursor.occurrence.1 ∈
      input.localizedCarrierOutwardChildFrames (fuel := fuel) target.1)
    (cursorDistinct : leftCursor ≠ rightCursor)
    (centerAtom leftAtom rightAtom : input.Atom)
    (leftActual : input.ActualPhysicalAtomAtNode leftCursor.occurrence.1.node leftAtom)
    (rightActual : input.ActualPhysicalAtomAtNode rightCursor.occurrence.1.node rightAtom)
    (leftParentObserved : leftCursor.occurrence.1.node.parent? = some centerAtom)
    (rightParentObserved : rightCursor.occurrence.1.node.parent? = some centerAtom)
    (leftNeighbors : input.moleculeGraph.neighborFinset leftAtom = {centerAtom})
    (rightNeighbors : input.moleculeGraph.neighborFinset rightAtom = {centerAtom})
    (leftSingleBond : input.moleculeGraph.bond leftAtom centerAtom = 1)
    (rightSingleBond : input.moleculeGraph.bond rightAtom centerAtom = 1)
    (leftNonduplicate : leftCursor.occurrence.1.node.isDuplicateLeaf = false)
    (rightNonduplicate : rightCursor.occurrence.1.node.isDuplicateLeaf = false)
    (zEq : input.moleculeGraph.atomZ leftAtom = input.moleculeGraph.atomZ rightAtom)
    (massEq : input.moleculeGraph.atomMass leftAtom =
      input.moleculeGraph.atomMass rightAtom)
    (distanceEq : leftCursor.occurrence.1.node.rule1bRootDistance =
      rightCursor.occurrence.1.node.rule1bRootDistance) :
    input.localizedOccurrenceRule45Descriptor?
      target (input.localizedDependencyView state target) = none := by
  let parentCursor : input.LocalizedRerootCursor fuel :=
    { occurrence := target, previous? := none }
  have leftIncomingFrame := cursorAt_previous_eq_target_of_frame
    input target frame frameComputed leftIndex
  rw [leftAt] at leftIncomingFrame
  have rightIncomingFrame := cursorAt_previous_eq_target_of_frame
    input target frame frameComputed rightIndex
  rw [rightAt] at rightIncomingFrame
  obtain ⟨leftSlot, leftAddress⟩ :=
    exists_address_slot_of_mem_outwardChildFrames input target.1 leftCursor.occurrence.1
      leftOutward
  obtain ⟨rightSlot, rightAddress⟩ :=
    exists_address_slot_of_mem_outwardChildFrames input target.1 rightCursor.occurrence.1
      rightOutward
  have leftAddress' : leftCursor.occurrence.1.address =
      parentCursor.occurrence.1.address ++ [leftSlot] := by
    simpa [parentCursor] using leftAddress
  have rightAddress' : rightCursor.occurrence.1.address =
      parentCursor.occurrence.1.address ++ [rightSlot] := by
    simpa [parentCursor] using rightAddress
  have leftTerminal := physicalLeaf_terminal input parentCursor leftCursor leftAtom centerAtom
    leftIncomingFrame leftSlot leftAddress' leftActual leftParentObserved leftNeighbors
    leftSingleBond leftNonduplicate
  have rightTerminal := physicalLeaf_terminal input parentCursor rightCursor rightAtom centerAtom
    rightIncomingFrame rightSlot rightAddress' rightActual rightParentObserved rightNeighbors
    rightSingleBond rightNonduplicate
  have leftCard : (input.moleculeGraph.neighborFinset leftAtom).card ≤ 1 := by
    rw [leftNeighbors]
    simp
  have rightCard : (input.moleculeGraph.neighborFinset rightAtom).card ≤ 1 := by
    rw [rightNeighbors]
    simp
  have leftLabelNone := localizedDependencyLabel_eq_none_of_physicalLeaf input target
    leftCursor leftAtom leftActual leftCard state model
  have rightLabelNone := localizedDependencyLabel_eq_none_of_physicalLeaf input target
    rightCursor rightAtom rightActual rightCard state model
  have leftComputed := buildCompound45?_terminal_actual input target
    (input.localizedDependencyView state target) leftCursor leftTerminal leftLabelNone
    (localizedOccurrenceRerootEvaluationFuel fuel)
  have rightComputed := buildCompound45?_terminal_actual input target
    (input.localizedDependencyView state target) rightCursor rightTerminal rightLabelNone
    (localizedOccurrenceRerootEvaluationFuel fuel)
  have labelEq := officialNodeAtomLabel_eq_of_actualPhysical_z_mass input
    leftCursor.occurrence.1.node rightCursor.occurrence.1.node leftAtom rightAtom
    leftActual rightActual zEq massEq
  have constitutionalEq :=
    TerminalEndpointObservation.officialRuleMajorRootKey_compare_eq_of_label_distance
      input leftCursor rightCursor labelEq distanceEq
  have constitutionalEqSymm :=
    TerminalEndpointObservation.officialRuleMajorRootKey_compare_eq_of_label_distance
      input rightCursor leftCursor labelEq.symm distanceEq.symm
  have leftRightTie := compareLocalizedOccurrenceThroughRule5At?_terminal_eq input target
    (input.localizedDependencyView state target) frame leftIndex rightIndex
    leftCursor rightCursor leftAt rightAt leftComputed rightComputed constitutionalEq
  have rightLeftTie := compareLocalizedOccurrenceThroughRule5At?_terminal_eq input target
    (input.localizedDependencyView state target) frame rightIndex leftIndex
    rightCursor leftCursor rightAt leftAt rightComputed leftComputed constitutionalEqSymm
  have indexDistinct : leftIndex ≠ rightIndex := by
    intro same
    apply cursorDistinct
    rw [← leftAt, ← rightAt, same]
  have safeNone := safeLocalizedOccurrenceRule45TrackedOrder?_eq_none_of_twin_tie input target
    (input.localizedDependencyView state target) frame leftIndex rightIndex indexDistinct
    leftRightTie rightLeftTie
  exact localizedOccurrenceRule45Descriptor?_eq_none_of_safe_eq_none input target
    (input.localizedDependencyView state target) frame frameComputed safeNone

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal.terminalCumulativeKey
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal.terminalReading
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal.terminalCompound4bc
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal.terminalRule5Reading
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal.terminalCompound45
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal.executableOfficialChildCopies_eq_nil_of_neighborFinset_singleton
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal.executableOfficialCIPChildren_eq_nil_of_childCopies_eq_nil
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal.executableChildren_eq_nil_of_officialChildren_eq_nil
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal.physicalLeaf_terminal
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal.not_hasRule3DoubleBondEdge_of_physicalLeaf
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal.officialNodeAtomLabel_eq_of_actualPhysical_z_mass
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal.modelState_eq_none_of_physicalLeaf
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal.localizedDependencyLabel_eq_none_of_state_eq_none
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal.localizedDependencyLabel_eq_none_of_physicalLeaf
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal.buildCumulative_terminal_actual
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal.buildReading_none_terminal_actual
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal.buildReadings_terminal_actual
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal.buildCompound4bc_terminal_actual
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal.buildRule5Reading_terminal_actual
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal.buildRule5Readings_terminal_actual
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal.buildCompound45_terminal_actual
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal.buildCompound45?_terminal_actual
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal.terminalCumulative_compare_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal.terminalReadingByRule4b_compare_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal.terminalReadingsByRule4b_compare_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal.terminalReadingByRule4cDescriptor_compare_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal.terminalReadingsByRule4c_compare_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal.terminalCompound4bc_compare_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal.terminalRule5Descriptor_compare_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal.terminalRule5Readings_compare_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal.terminalCompound45_compare_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal.cursorAt_mem
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal.cursorAt_previous_eq_target_of_frame
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal.exists_address_slot_of_mem_outwardChildFrames
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal.orderCoherent?_eq_false_of_twin_tie
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal.safeLocalizedOccurrenceRule45TrackedOrder?_eq_none_of_twin_tie
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal.compareLocalizedOccurrenceThroughRule5At?_terminal_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal.localizedOccurrenceRule45SpatialEvidence?_eq_none_of_safe_eq_none
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal.localizedOccurrenceRule45Descriptor?_eq_none_of_safe_eq_none
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal.localizedOccurrenceRule45Descriptor?_eq_none_of_actualPhysical_terminalTwins
