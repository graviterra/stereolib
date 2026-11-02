import TetraStereo.UniversalProof.NativeInitialSeedRuntimeSupport
import TetraStereo.UniversalProof.NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery
import TetraStereo.OneCenter.ProductionCIPHistoryBridge

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeInitialSeedRuntimeSupportProofsLibrary.GeneratedPendantOccurrenceRecovery

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment
open TetraStereo.UniversalProof.RuntimeOccurrenceFactRecoveryProofs.RuntimeOccurrenceFactRecovery
open TetraStereo.UniversalProof.NonleafAtomicRuntimeComparisonRecoveryProofs.NonleafAtomicRuntimeComparisonRecovery
open TetraStereo.UniversalProof.FiniteCanonicalCollectorRecoveryProofs.FiniteCanonicalCollectorRecovery
open TetraStereo.UniversalProof.NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery














-- record_neighbors_symmetric is re-exported from NativeInitialSeedRuntimeSupport.


/-- Child membership itself exposes a real raw record edge, including for duplicate children. -/
theorem generated_child_incident (raw : RawMolecule) (well : raw.WellFormed)
    {parent child : CanonicalBranchNode} (member : child ∈ raw.canonicalChildren parent) :
    child.atom ∈ recordNeighbors raw parent.atom := by
  unfold canonicalChildren at member
  by_cases leaf : parent.forcedLeaf
  · simp [leaf] at member
  · simp only [leaf, Bool.false_eq_true, ↓reduceIte, List.mem_map] at member
    obtain ⟨copy, copyMember, rfl⟩ := member
    obtain ⟨bond, retained, endpoints, _⟩ := raw.canonicalChildCopies_source parent copy copyMember
    refine List.mem_filterMap.mpr ⟨bond, retained, ?_⟩
    rcases endpoints with ⟨source, target⟩ | ⟨target, source⟩
    · simp [recordNeighbor?, source, target]
    · have different : copy.1 ≠ parent.atom := by
        simpa only [source, target] using (well bond retained).2.2
      simp [recordNeighbor?, target, source, different]

/-- A path of actual raw-record edges terminating at its original root. -/
inductive RootedRecordPath (raw : RawMolecule) (root : Nat) : List Nat → Prop
  | root : RootedRecordPath raw root [root]
  | step {head : Nat} {rest : List Nat} (next : Nat) :
      RootedRecordPath raw root (head :: rest) →
      head ∈ recordNeighbors raw next →
      RootedRecordPath raw root (next :: head :: rest)

/-- The actual generated history is a record path; this is derived, not a supplied path witness. -/
theorem generated_record_path (raw : RawMolecule) (well : raw.WellFormed) (root : Nat)
    {node : CanonicalBranchNode} (generated : CanonicalCenterTreeNode raw root node) :
    RootedRecordPath raw root node.history := by
  induction generated with
  | root => exact .root
  | @child parent child parentGenerated member ih =>
      have history := raw.canonicalChildren_history parent child member
      have head := parentGenerated.history_head
      have adjacent := record_neighbors_symmetric raw well (generated_child_incident raw well member)
      cases shape : parent.history with
      | nil => simp [shape] at head
      | cons current rest =>
          have equal : current = parent.atom := by simpa only [shape, List.head?_cons, Option.some.injEq] using head
          subst current
          rw [history, shape]
          exact .step child.atom (by simpa only [shape] using ih) adjacent

/-- A degree-one vertex cannot be internal to a simple undirected record path. -/
theorem terminal_path_endpoint (raw : RawMolecule) (well : raw.WellFormed)
    (root leaf attached : Nat) {history : List Nat}
    (path : RootedRecordPath raw root history) (distinct : history.Nodup)
    (terminal : recordNeighbors raw leaf = [attached]) (member : leaf ∈ history) :
    history.head? = some leaf ∨ leaf = root := by
  induction path with
  | root =>
      have equal := List.mem_singleton.mp member
      exact Or.inr equal
  | @step head rest next path adjacent ih =>
      rcases List.mem_cons.mp member with equal | retained
      · subst leaf
        exact Or.inl rfl
      · rcases ih (List.nodup_cons.mp distinct).2 retained with first | final
        · have equal : head = leaf := Option.some.inj first
          cases path with
          | root => exact Or.inr equal.symm
          | @step previous tail head previousPath previousAdjacent =>
              have nextAdjacent := record_neighbors_symmetric raw well adjacent
              rw [equal, terminal] at previousAdjacent nextAdjacent
              have previousEqual := List.mem_singleton.mp previousAdjacent
              have nextEqual := List.mem_singleton.mp nextAdjacent
              have forbidden := (List.nodup_cons.mp distinct).1
              exact False.elim (forbidden (List.mem_cons_of_mem head
                (List.mem_cons.mpr (Or.inl (nextEqual.trans previousEqual.symm)))))
        · exact Or.inr final

/-- Terminal endpoints other than the actual current/root cannot occur in a real generated history. -/
theorem generated_terminal_absent (raw : RawMolecule) (well : raw.WellFormed)
    (root leaf attached : Nat) (rootBound : root < raw.atomCount)
    {node : CanonicalBranchNode} (generated : CanonicalCenterTreeNode raw root node)
    (real : node.provenance = CanonicalNodeProvenance.realAtom)
    (terminal : recordNeighbors raw leaf = [attached])
    (currentDifferent : node.atom ≠ leaf) (rootDifferent : root ≠ leaf) :
    leaf ∉ node.history := by
  intro member
  rcases terminal_path_endpoint raw well root leaf attached
    (generated_record_path raw well root generated)
    (generated.real_history rootBound well real).1 terminal member with current | rootEqual
  · exact currentDifferent (Option.some.inj (generated.history_head.symm.trans current))
  · exact rootDifferent rootEqual.symm

/-- Independent local physical pendant structure. Stored raw record order is unrestricted.
Atomic-number equations are raw element observations; they specify no priority permutation. -/
structure PendantSite (raw : RawMolecule) (atom : Nat) where
  backbone : Nat
  hydrogen : Nat
  fluorine : Nat
  bromine : Nat
  bound : atom < raw.atomCount
  carbon : raw.atomZAt atom = 6
  neighbors : (recordNeighbors raw atom).Perm [backbone, hydrogen, fluorine, bromine]
  single : ∀ other ∈ recordNeighbors raw atom, raw.bondOrder atom other = 1
  backboneCarbon : raw.atomZAt backbone = 6
  hydrogenZ : raw.atomZAt hydrogen = 1
  fluorineZ : raw.atomZAt fluorine = 9
  bromineZ : raw.atomZAt bromine = 35
  hydrogenRow : recordNeighbors raw hydrogen = [atom]
  fluorineRow : recordNeighbors raw fluorine = [atom]
  bromineRow : recordNeighbors raw bromine = [atom]

theorem PendantSite.atomic_domain (raw : RawMolecule) (well : raw.WellFormed)
    (atom : Nat) (site : PendantSite raw atom) : AtomicCenterDomain raw atom := by
  refine ⟨well, site.bound, site.single, ?_⟩
  have rankPermutation := site.neighbors.map raw.atomZAt
  have target : ([site.backbone, site.hydrogen, site.fluorine, site.bromine].map raw.atomZAt).Nodup := by
    rw [List.map_cons, List.map_cons, List.map_cons, List.map_cons, List.map_nil,
      site.backboneCarbon, site.hydrogenZ, site.fluorineZ, site.bromineZ]
    decide +kernel
  exact rankPermutation.nodup_iff.mpr target

theorem PendantSite.four (raw : RawMolecule) (atom : Nat) (site : PendantSite raw atom) :
    (recordNeighbors raw atom).length = 4 := site.neighbors.length_eq

/-- All three terminal endpoints are absent from the ACTUAL real carbon-rooted history. -/
theorem actual_terminal_freshness (raw : RawMolecule) (well : raw.WellFormed)
    (root atom : Nat) (rootBound : root < raw.atomCount) (rootCarbon : raw.atomZAt root = 6)
    (site : PendantSite raw atom) {node : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode raw root node)
    (real : node.provenance = CanonicalNodeProvenance.realAtom) (current : node.atom = atom) :
    site.hydrogen ∉ node.history ∧ site.fluorine ∉ node.history ∧ site.bromine ∉ node.history := by
  have currentZ : raw.atomZAt node.atom = 6 := by simpa only [current] using site.carbon
  refine ⟨?_, ?_, ?_⟩
  · exact generated_terminal_absent raw well root site.hydrogen atom rootBound generated real
      site.hydrogenRow (by intro equal; rw [equal, site.hydrogenZ] at currentZ; omega)
      (by intro equal; rw [equal, site.hydrogenZ] at rootCarbon; omega)
  · exact generated_terminal_absent raw well root site.fluorine atom rootBound generated real
      site.fluorineRow (by intro equal; rw [equal, site.fluorineZ] at currentZ; omega)
      (by intro equal; rw [equal, site.fluorineZ] at rootCarbon; omega)
  · exact generated_terminal_absent raw well root site.bromine atom rootBound generated real
      site.bromineRow (by intro equal; rw [equal, site.bromineZ] at currentZ; omega)
      (by intro equal; rw [equal, site.bromineZ] at rootCarbon; omega)

/-- Every actual interior daughter entry uses its backbone, derived from the original history. -/
theorem actual_pendant_entry (raw : RawMolecule) (well : raw.WellFormed)
    (root atom : Nat) (rootBound : root < raw.atomCount) (rootCarbon : raw.atomZAt root = 6)
    (site : PendantSite raw atom) {parent node : CanonicalBranchNode}
    (parentGenerated : CanonicalCenterTreeNode raw root parent)
    (child : node ∈ raw.canonicalChildren parent)
    (real : node.provenance = CanonicalNodeProvenance.realAtom) (current : node.atom = atom) :
    parent.atom = site.backbone := by
  have generated := CanonicalCenterTreeNode.child parentGenerated child
  have fresh := actual_terminal_freshness raw well root atom rootBound rootCarbon site generated real current
  have incident := record_neighbors_symmetric raw well (generated_child_incident raw well child)
  rw [current] at incident
  have selected := site.neighbors.mem_iff.mp incident
  simp only [List.mem_cons, List.not_mem_nil, or_false] at selected
  have parentMember : parent.atom ∈ node.history := by
    rw [raw.canonicalChildren_history parent node child]
    exact List.mem_cons_of_mem node.atom (List.mem_of_head?_eq_some parentGenerated.history_head)
  rcases selected with equal | equal | equal | equal
  · exact equal
  · exact False.elim (fresh.1 (equal ▸ parentMember))
  · exact False.elim (fresh.2.1 (equal ▸ parentMember))
  · exact False.elim (fresh.2.2 (equal ▸ parentMember))

private theorem canonical_bond_one (raw : RawMolecule) (node : CanonicalBranchNode) (atom : Nat)
    (one : raw.bondOrder node.atom atom = 1) : raw.canonicalBondOrder node atom = 1 := by
  cases history : node.history with
  | nil => simpa only [canonicalBondOrder, history] using one
  | cons first tail =>
      cases tail with
      | nil => simpa only [canonicalBondOrder, history] using one
      | cons second tail =>
          cases tail with
          | nil => simp [canonicalBondOrder, history, one]
          | cons third rest => simpa only [canonicalBondOrder, history] using one

private theorem unit_copies (raw : RawMolecule) (node : CanonicalBranchNode) (bonds : List RawBond)
    (single : ∀ bond ∈ bonds, ∀ atom, recordNeighbor? node.atom bond = some atom →
      raw.canonicalBondOrder node atom = 1) :
    (bonds.flatMap fun bond => match recordNeighbor? node.atom bond with
      | none => []
      | some atom => (List.range (raw.canonicalBondOrder node atom)).map (fun copy => (atom, copy))) =
    (bonds.filterMap (recordNeighbor? node.atom)).map (fun atom => (atom, 0)) := by
  induction bonds with
  | nil => rfl
  | cons bond bonds ih =>
      have tailSingle : ∀ selected ∈ bonds, ∀ atom, recordNeighbor? node.atom selected = some atom →
          raw.canonicalBondOrder node atom = 1 := by
        intro selected member atom observed
        exact single selected (List.mem_cons_of_mem bond member) atom observed
      simp only [List.flatMap_cons, List.filterMap_cons]
      cases observed : recordNeighbor? node.atom bond with
      | none => simpa only [List.nil_append] using ih tailSingle
      | some atom =>
          have one := single bond List.mem_cons_self atom observed
          simp only [one, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
            List.map_nil, List.cons_append]
          rw [ih tailSingle]

private theorem erase_parent_map (parent : Nat) (atoms : List Nat) :
    eraseCanonicalParentCopy parent (atoms.map (fun atom => (atom, 0))) =
      (atoms.erase parent).map (fun atom => (atom, 0)) := by
  induction atoms with
  | nil => rfl
  | cons atom atoms ih =>
      by_cases equal : atom = parent
      · subst atom
        simp [eraseCanonicalParentCopy]
      · simp [eraseCanonicalParentCopy, equal, ih]

/-- The actual stored-parent deletion acts on exactly the original single-edge records. -/
theorem actual_child_copies (raw : RawMolecule) (atom : Nat) (site : PendantSite raw atom)
    (node : CanonicalBranchNode) (current : node.atom = atom) :
    raw.canonicalChildCopies node =
      ((recordNeighbors raw atom).erase node.parent).map (fun other => (other, 0)) := by
  have seeds := unit_copies raw node raw.bonds (by
    intro bond retained other observed
    apply canonical_bond_one
    rw [current]
    apply site.single
    rw [← current]
    exact List.mem_filterMap.mpr ⟨bond, retained, observed⟩)
  change eraseCanonicalParentCopy node.parent
    (raw.bonds.flatMap fun bond => match recordNeighbor? node.atom bond with
      | none => []
      | some other => (List.range (raw.canonicalBondOrder node other)).map (fun copy => (other, copy))) = _
  rw [seeds, erase_parent_map, current]
  rfl

/-- Outgoing nodes retain the ACTUAL history and become real only after freshness is proved. -/
def outgoingNode (node : CanonicalBranchNode) (atom : Nat) : CanonicalBranchNode :=
  { atom := atom, parent := node.atom, history := atom :: node.history, provenance := .realAtom }

/-- The original incoming parent and the original generated terminal children, before sorting. -/
def interiorRoots (raw : RawMolecule) (atom : Nat) (site : PendantSite raw atom)
    (node parent : CanonicalBranchNode) : List CanonicalRerootCursor :=
  { node := parent, previous? := some node } ::
    ((recordNeighbors raw atom).erase site.backbone).map
      (fun other => { node := outgoingNode node other, previous? := some node })

/-- Original parent-copy deletion removes the unique backbone record and nothing else. -/
theorem actual_outgoing_atoms (raw : RawMolecule) (atom : Nat) (site : PendantSite raw atom) :
    ((recordNeighbors raw atom).erase site.backbone).Perm
      [site.hydrogen, site.fluorine, site.bromine] := by
  simpa only [List.erase_cons_head] using List.Perm.erase site.backbone site.neighbors

/-- Exact three original child nodes. Their real provenance is DERIVED from physical-terminal
freshness and single bonds, rather than supplied as a frame or callback hypothesis. -/
theorem actual_outgoing_children (raw : RawMolecule) (well : raw.WellFormed)
    (root atom : Nat) (rootBound : root < raw.atomCount) (rootCarbon : raw.atomZAt root = 6)
    (site : PendantSite raw atom) {parent node : CanonicalBranchNode}
    (parentGenerated : CanonicalCenterTreeNode raw root parent)
    (child : node ∈ raw.canonicalChildren parent)
    (real : node.provenance = CanonicalNodeProvenance.realAtom) (current : node.atom = atom) :
    raw.canonicalChildren node =
      ((recordNeighbors raw atom).erase site.backbone).map (outgoingNode node) := by
  have generated := CanonicalCenterTreeNode.child parentGenerated child
  have entry := actual_pendant_entry raw well root atom rootBound rootCarbon site parentGenerated child real current
  have stored : node.parent = site.backbone :=
    (raw.canonicalChildren_parent_eq parent node child).trans entry
  have fresh := actual_terminal_freshness raw well root atom rootBound rootCarbon site generated real current
  have forced : node.forcedLeaf = false := by rw [CanonicalBranchNode.forcedLeaf, real]
  unfold canonicalChildren
  rw [forced]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [actual_child_copies raw atom site node current, stored, List.map_map]
  apply List.map_congr_left
  intro other member
  have selected := (actual_outgoing_atoms raw atom site).mem_iff.mp member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at selected
  have unvisited : other ∉ node.history := by
    rcases selected with rfl | rfl | rfl
    · exact fresh.1
    · exact fresh.2.1
    · exact fresh.2.2
  simp [outgoingNode, unvisited]

/-- Actual production reroot cursors retain the exact recovered original parent and history. -/
theorem actual_interior_roots (raw : RawMolecule) (well : raw.WellFormed)
    (root atom : Nat) (rootBound : root < raw.atomCount) (rootCarbon : raw.atomZAt root = 6)
    (site : PendantSite raw atom) {parent node : CanonicalBranchNode}
    (parentGenerated : CanonicalCenterTreeNode raw root parent)
    (child : node ∈ raw.canonicalChildren parent)
    (real : node.provenance = CanonicalNodeProvenance.realAtom) (current : node.atom = atom) :
    occurrenceLigandCursors raw node = interiorRoots raw atom site node parent := by
  have parentComputed := canonicalOriginalParent?_eq_some_of_child parentGenerated child
  have childrenComputed := actual_outgoing_children raw well root atom rootBound rootCarbon site
    parentGenerated child real current
  have forced : node.forcedLeaf = false := by rw [CanonicalBranchNode.forcedLeaf, real]
  change (if node.forcedLeaf then [] else
    ((canonicalOriginalParent? node).toList ++ raw.canonicalChildren node).filterMap
      (fun other => some ({ node := other, previous? := some node } : CanonicalRerootCursor))) = _
  rw [forced]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [parentComputed, childrenComputed]
  simp only [Option.toList_some, List.singleton_append, List.filterMap_cons,
    List.filterMap_map, Function.comp_def, List.filterMap_eq_map']
  rfl

theorem actual_interior_ids (raw : RawMolecule) (atom : Nat) (site : PendantSite raw atom)
    (node parent : CanonicalBranchNode) (entry : parent.atom = site.backbone) :
    ((interiorRoots raw atom site node parent).map (fun cursor => cursor.node.atom)).Perm
      (recordNeighbors raw atom) := by
  have tailPermutation := actual_outgoing_atoms raw atom site
  have mapped : (interiorRoots raw atom site node parent).map (fun cursor => cursor.node.atom) =
      site.backbone :: (recordNeighbors raw atom).erase site.backbone := by
    simp only [interiorRoots, List.map_cons, List.map_map, entry]
    change site.backbone :: ((recordNeighbors raw atom).erase site.backbone).map id = _
    rw [List.map_id]
  rw [mapped]
  exact (List.Perm.cons site.backbone tailPermutation).trans site.neighbors.symm

/-- Four physical roots and the actual written four-ligand perception are both derived. -/
theorem actual_interior_frame (raw : RawMolecule) (well : raw.WellFormed)
    (written : raw.WrittenNeighborExact) (root atom : Nat)
    (rootBound : root < raw.atomCount) (rootCarbon : raw.atomZAt root = 6)
    (site : PendantSite raw atom) {parent node : CanonicalBranchNode}
    (parentGenerated : CanonicalCenterTreeNode raw root parent)
    (child : node ∈ raw.canonicalChildren parent)
    (real : node.provenance = CanonicalNodeProvenance.realAtom) (current : node.atom = atom) :
    occurrenceLigandFrame? raw node = some (interiorRoots raw atom site node parent) := by
  have atomicDomain := PendantSite.atomic_domain raw well atom site
  have four := PendantSite.four raw atom site
  have writtenFour := (actual_written_permutation raw atom atomicDomain written).length_eq.trans four
  have ligands := AuthoritativeCIPRule6Scheduler.ligandsWithLonePair_eq_writtenNeighbors_of_length_four
    raw atom writtenFour
  have entry := actual_pendant_entry raw well root atom rootBound rootCarbon site parentGenerated child real current
  have rootsFour : (interiorRoots raw atom site node parent).length = 4 := by
    have ids := actual_interior_ids raw atom site node parent entry
    simpa only [List.length_map] using ids.length_eq.trans four
  have rootsComputed := actual_interior_roots raw well root atom rootBound rootCarbon site parentGenerated child real current
  unfold occurrenceLigandFrame?
  rw [current, ligands, rootsComputed]
  simp [writtenFour, rootsFour]

/-- Original returned cursors have actual physical observations; no fresh final-root replacement. -/
theorem actual_interior_observations (raw : RawMolecule) (well : raw.WellFormed)
    (root atom : Nat) (rootBound : root < raw.atomCount) (rootCarbon : raw.atomZAt root = 6)
    (site : PendantSite raw atom) {parent node : CanonicalBranchNode}
    (parentGenerated : CanonicalCenterTreeNode raw root parent)
    (child : node ∈ raw.canonicalChildren parent)
    (real : node.provenance = CanonicalNodeProvenance.realAtom) (current : node.atom = atom) :
    ∀ cursor ∈ interiorRoots raw atom site node parent, ObservedReal raw cursor := by
  have entry := actual_pendant_entry raw well root atom rootBound rootCarbon site parentGenerated child real current
  have ids := actual_interior_ids raw atom site node parent entry
  intro cursor member
  have incident := ids.mem_iff.mp (List.mem_map.mpr ⟨cursor, member, rfl⟩)
  have bound := (recordNeighbor_bounds well incident).1
  obtain ⟨spec, lookup⟩ := NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery.atomAt?_exists_of_lt_atomCount raw cursor.node.atom bound
  refine ⟨?_, spec, lookup⟩
  change cursor ∈ { node := parent, previous? := some node } :: _ at member
  rcases List.mem_cons.mp member with equal | remaining
  · subst cursor
    exact real_of_child_mem child
  · obtain ⟨other, _, rfl⟩ := List.mem_map.mp remaining
    rfl

theorem actual_interior_distinct_ranks (raw : RawMolecule) (well : raw.WellFormed)
    (atom : Nat) (site : PendantSite raw atom) (node parent : CanonicalBranchNode)
    (entry : parent.atom = site.backbone) :
    ((interiorRoots raw atom site node parent).map (fun cursor => raw.atomZAt cursor.node.atom)).Nodup := by
  have mapped := (actual_interior_ids raw atom site node parent entry).map raw.atomZAt
  rw [List.map_map] at mapped
  exact mapped.nodup_iff.mpr (PendantSite.atomic_domain raw well atom site).distinctRanks

/-- The actual strict production sorter result is independent of BOTH state and budget.
This follows from first-Z comparisons and unique strict sorting of the original returned roots. -/
theorem actual_interior_sort_uniform (raw : RawMolecule) (well : raw.WellFormed)
    (root atom : Nat) (rootBound : root < raw.atomCount) (rootCarbon : raw.atomZAt root = 6)
    (site : PendantSite raw atom) {parent node : CanonicalBranchNode}
    (parentGenerated : CanonicalCenterTreeNode raw root parent)
    (child : node ∈ raw.canonicalChildren parent)
    (real : node.provenance = CanonicalNodeProvenance.realAtom) (current : node.atom = atom) :
    ∃ result : List CanonicalRerootCursor × Nat,
      result.1.Perm (interiorRoots raw atom site node parent) ∧
      result.1.Pairwise (NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery.AtomicDesc raw) ∧ result.2 = 0 ∧
      ∀ state fuel, sortOccurrencesTrackedAuthoritative? raw state fuel
        (interiorRoots raw atom site node parent) = some result := by
  have observed := actual_interior_observations raw well root atom rootBound rootCarbon site parentGenerated child real current
  have entry := actual_pendant_entry raw well root atom rootBound rootCarbon site parentGenerated child real current
  have distinct := actual_interior_distinct_ranks raw well atom site node parent entry
  obtain ⟨result, _, permutation, ordered, zero⟩ := actual_sort_distinct_observed raw [] 0 _ observed distinct
  refine ⟨result, permutation, ordered, zero, ?_⟩
  intro state fuel
  obtain ⟨other, computed, otherPermutation, otherOrdered, otherZero⟩ :=
    actual_sort_distinct_observed raw state fuel _ observed distinct
  have listEqual : other.1 = result.1 := by
    apply List.Perm.eq_of_pairwise (le := NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery.AtomicDesc raw)
      _ otherOrdered ordered (otherPermutation.trans permutation.symm)
    intro a b _ _ forward backward
    exact False.elim (Nat.lt_asymm forward backward)
  have equal : other = result := Prod.ext listEqual (otherZero.trans zero.symm)
  simpa only [equal] using computed

private theorem interior_positions_exists (raw : RawMolecule) (well : raw.WellFormed)
    (written : raw.WrittenNeighborExact) (atom : Nat) (site : PendantSite raw atom)
    (roots : List CanonicalRerootCursor)
    (members : ∀ cursor ∈ roots, cursor.node.atom ∈ recordNeighbors raw atom) :
    ∃ positions, runtimePriorityPositions? raw atom roots = some positions := by
  have domain := PendantSite.atomic_domain raw well atom site
  have permutation := actual_written_permutation raw atom domain written
  have nodup := permutation.nodup_iff.mpr domain.neighbors_nodup
  have writtenFour := permutation.length_eq.trans (PendantSite.four raw atom site)
  have ligands := AuthoritativeCIPRule6Scheduler.ligandsWithLonePair_eq_writtenNeighbors_of_length_four raw atom writtenFour
  unfold runtimePriorityPositions?
  rw [ligands]
  change ∃ positions, roots.mapM (fun cursor => writtenSlot? (raw.writtenNeighbors atom) cursor.node.atom) = some positions
  revert members
  induction roots with
  | nil => intro _; exact ⟨[], rfl⟩
  | cons cursor roots ih =>
      intro members
      have member := permutation.mem_iff.mpr (members cursor List.mem_cons_self)
      obtain ⟨position, lookup⟩ := List.mem_iff_getElem?.mp member
      have found := writtenSlot?_eq_some _ nodup position cursor.node.atom lookup
      obtain ⟨positions, computed⟩ := ih (fun other retained => members other (List.mem_cons_of_mem cursor retained))
      exact ⟨position :: positions, by simp [List.mapM_cons, found, computed]⟩

/-- Only the key/address of the ACTUAL incoming occurrence is used in the auxiliary fact. -/
def interiorFact (node : CanonicalBranchNode) (positions : List Nat) (descriptor : RS) : OccurrenceAuxFact where
  key := canonicalOccurrenceKey node
  atom := node.atom
  descriptor := descriptor
  uppercase := true
  priorityPositions := positions

/-- Actual total interior callback, independent of state/fuel. Positions and label are derived
from source-written lookup and the observed INPUT parity; no expected descriptor is a premise. -/
theorem actual_interior_fact_uniform (raw : RawMolecule) (well : raw.WellFormed)
    (written : raw.WrittenNeighborExact) (root atom : Nat)
    (rootBound : root < raw.atomCount) (rootCarbon : raw.atomZAt root = 6)
    (site : PendantSite raw atom) {parent node : CanonicalBranchNode}
    (parentGenerated : CanonicalCenterTreeNode raw root parent)
    (child : node ∈ raw.canonicalChildren parent)
    (real : node.provenance = CanonicalNodeProvenance.realAtom) (current : node.atom = atom)
    (spec : AtomSpec) (lookup : raw.atomAt? atom = some spec)
    (parity : TetrahedralInputParity) (tag : spec.tetrahedral? = some parity) :
    ∃ positions, ∀ state fuel, occurrenceFactAuthoritative? raw fuel state node =
      some (interiorFact node positions (RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven positions))) := by
  have entry := actual_pendant_entry raw well root atom rootBound rootCarbon site parentGenerated child real current
  have ids := actual_interior_ids raw atom site node parent entry
  have observed := actual_interior_observations raw well root atom rootBound rootCarbon site parentGenerated child real current
  have frame := actual_interior_frame raw well written root atom rootBound rootCarbon site parentGenerated child real current
  obtain ⟨result, permutation, ordered, _, uniform⟩ := actual_interior_sort_uniform raw well root atom rootBound rootCarbon site parentGenerated child real current
  have physical : ∀ cursor ∈ result.1, cursor.node.atom ∈ recordNeighbors raw atom := by
    intro cursor member
    exact ids.mem_iff.mp (List.mem_map.mpr ⟨cursor, permutation.mem_iff.mp member, rfl⟩)
  obtain ⟨positions, positionsComputed⟩ := interior_positions_exists raw well written atom site result.1 physical
  refine ⟨positions, ?_⟩
  intro state fuel
  obtain ⟨decisions, decisionsComputed, strict, pseudo, _⟩ := actual_observed_adjacent raw state fuel result.1
    (fun cursor member => observed cursor (permutation.mem_iff.mp member)) ordered
  have physical := actual_interior_roots raw well root atom rootBound rootCarbon site
    parentGenerated child real current
  have distinct := actual_interior_distinct_ranks raw well atom site node parent entry
  rw [FramedAtomicDispatch.authoritative_fact_eq_legacy raw root fuel state node
    (CanonicalCenterTreeNode.child parentGenerated child) (interiorRoots raw atom site node parent)
    physical frame observed distinct]
  unfold legacyOccurrenceFactAuthoritative?
  rw [current]
  change (do
    let actualSpec ← raw.atomAt? atom
    let actualParity ← actualSpec.tetrahedral?
    let actualRoots ← occurrenceLigandFrame? raw node
    let actualSorted ← sortOccurrencesTrackedAuthoritative? raw state fuel actualRoots
    let actualPositions ← runtimePriorityPositions? raw atom actualSorted.1
    let actualDecisions ← compareOccurrenceAdjacentPairsAuthoritative? raw state fuel actualSorted.1
    if !(actualDecisions.all fun decision => decision.ordering != Ordering.eq) then none else
      some ({ key := canonicalOccurrenceKey node, atom := atom, descriptor := RawMolecule.descriptorOfParity actualParity (RawMolecule.permutationIsEven actualPositions), uppercase := (actualDecisions.filter fun (decision : OccurrenceComparison) => decision.pseudo).length % 2 == 0, priorityPositions := actualPositions } : OccurrenceAuxFact)) = _
  simp [lookup, tag, frame, uniform state fuel, positionsComputed, decisionsComputed,
    pseudo, interiorFact, current]
  simpa using strict

/-- Direct application to the ACTUAL collector output; generated membership is recovered. -/
theorem collected_pendant_entry (raw : RawMolecule) (well : raw.WellFormed)
    (root atom fuel : Nat) (rootBound : root < raw.atomCount) (rootCarbon : raw.atomZAt root = 6)
    (site : PendantSite raw atom) (node : CanonicalBranchNode)
    (member : node ∈ prefixTree raw root 0 fuel)
    (real : node.provenance = CanonicalNodeProvenance.realAtom) (current : node.atom = atom)
    (different : atom ≠ root) :
    ∃ parent, CanonicalCenterTreeNode raw root parent ∧
      node ∈ raw.canonicalChildren parent ∧ parent.atom = site.backbone := by
  have generated := prefixTree_generated raw root fuel 0 node member
  cases generated with
  | root =>
      have equal : root = atom := current
      exact False.elim (different equal.symm)
  | @child parent node parentGenerated child =>
      exact ⟨parent, parentGenerated, child,
        actual_pendant_entry raw well root atom rootBound rootCarbon site parentGenerated child real current⟩

namespace TwoPendants

/-- Two annotated pendant carbons share one untagged carbon backbone. All H are physical records. -/
def hydrogen : AtomSpec := { AtomSpec.aliphatic .H with explicitHydrogens? := some 0 }

def raw : RawMolecule :=
  { atoms := [{ AtomSpec.aliphatic .C with tetrahedral? := some .clockwise },
      AtomSpec.aliphatic .C, hydrogen, AtomSpec.aliphatic .F, AtomSpec.aliphatic .Br,
      { AtomSpec.aliphatic .C with tetrahedral? := some .anticlockwise },
      hydrogen, AtomSpec.aliphatic .F, AtomSpec.aliphatic .Br, hydrogen, hydrogen]
    bonds := [⟨0, 1, .single⟩, ⟨0, 2, .single⟩, ⟨0, 3, .single⟩, ⟨0, 4, .single⟩,
      ⟨1, 5, .single⟩, ⟨5, 6, .single⟩, ⟨5, 7, .single⟩, ⟨5, 8, .single⟩,
      ⟨1, 9, .single⟩, ⟨1, 10, .single⟩]
    neighborOrder := [[1, 2, 3, 4], [0, 5, 9, 10], [0], [0], [0],
      [1, 6, 7, 8], [5], [5], [5], [1], [1]] }

theorem actual_admissible : raw.StereochemicalAdmissible := by
  apply (stereochemicalAdmissible?_eq_true_iff raw).mp
  decide +kernel

theorem actual_written : raw.WrittenNeighborExact := by
  change raw.writtenNeighborExact? = true
  decide +kernel

/-- Production valence conventions and zero additional-H demand, not external chemical approval. -/
theorem actual_valences :
    [0, 1, 5].map raw.usedValenceAt = [4, 4, 4] ∧
    [2, 3, 4, 6, 7, 8, 9, 10].map raw.usedValenceAt = [1, 1, 1, 1, 1, 1, 1, 1] ∧
    (List.range 11).map raw.hydrogenCountAt = List.replicate 11 0 := by decide +kernel

def site : PendantSite raw 5 where
  backbone := 1
  hydrogen := 6
  fluorine := 7
  bromine := 8
  bound := by decide +kernel
  carbon := by decide +kernel
  neighbors := List.Perm.refl _
  single := by
    intro other member
    change other ∈ [1, 6, 7, 8] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide +kernel
  backboneCarbon := by decide +kernel
  hydrogenZ := by decide +kernel
  fluorineZ := by decide +kernel
  bromineZ := by decide +kernel
  hydrogenRow := rfl
  fluorineRow := rfl
  bromineRow := rfl

def parent : CanonicalBranchNode := canonicalRoot 0 1

def daughter : CanonicalBranchNode :=
  { atom := 5, parent := 1, history := [5, 1, 0], provenance := .realAtom }

theorem actual_parent_generated : CanonicalCenterTreeNode raw 0 parent :=
  .child .root (by decide +kernel)

theorem actual_daughter_child : daughter ∈ raw.canonicalChildren parent := by decide +kernel

/-- The frame uses original incoming history [1,0] and outgoing histories [terminal,5,1,0]. -/
theorem actual_interior_four_frame :
    occurrenceLigandFrame? raw daughter = some
      [{ node := parent, previous? := some daughter },
       { node := outgoingNode daughter 6, previous? := some daughter },
       { node := outgoingNode daughter 7, previous? := some daughter },
       { node := outgoingNode daughter 8, previous? := some daughter }] := by
  exact actual_interior_frame raw actual_admissible.1.1 actual_written 0 5
    (by decide +kernel) (by decide +kernel) site actual_parent_generated actual_daughter_child rfl rfl

/-- Nonvacuous actual interior callback at every state/budget; observed input parity determines
its returned label through internally recovered positions, with no expected label input. -/
theorem actual_interior_assignment :
    ∃ positions, ∀ state fuel, occurrenceFactAuthoritative? raw fuel state daughter =
      some (interiorFact daughter positions (RawMolecule.descriptorOfParity .anticlockwise
        (RawMolecule.permutationIsEven positions))) := by
  exact actual_interior_fact_uniform raw actual_admissible.1.1 actual_written 0 5
    (by decide +kernel) (by decide +kernel) site actual_parent_generated actual_daughter_child rfl rfl
    { AtomSpec.aliphatic .C with tetrahedral? := some .anticlockwise } rfl .anticlockwise rfl

end TwoPendants

end TetraStereo.UniversalProof.NativeInitialSeedRuntimeSupportProofsLibrary.GeneratedPendantOccurrenceRecovery
