import TetraStereo.OneCenter.LocalizedPreflightDemandDiscovery
import TetraStereo.OneCenter.LocalizedPreflightDemandTotality
import TetraStereo.OneCenter.LocalizedExtendedMandatoryRecursion
import TetraStereo.OneCenter.LocalizedOccurrenceExecutableRoots
import TetraStereo.OneCenter.LocalizedShortCircuitPipeline
import TetraStereo.OneCenter.LocalizedRule3DemandRankProducer
import TetraStereo.OneCenter.LocalizedRule3RouteCompleteness
import TetraStereo.OneCenter.LocalizedPhysicalReferenceUniqueness
import TetraStereo.OneCenter.LocalizedUniversalRule3Evaluation
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace TetraStereo.OneCenter.LocalizedRetainedDemandCycleClosure

open TetraStereo.OneCenter
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.Certificate.WeightedDemand

/-!
# Kernel closure of the retained-demand cycle of the ten-atom `S(=CH₂)₃` fixture

This module is self-contained: it imports the lower-level executable/proof modules directly rather
than the earlier draft that attempted a global kernel reduction of the fuel-11 occurrence carrier.
The fixture, admission witness, occurrence cursors, endpoint readiness and conditional request
membership are reproduced from `LocalizedRetainedDemandCycleKernel`; the unconditional
constitutional ties, the actual two-cycle, the all-budget refusal and the input-graph obstruction
are new.

The constitutional tie is proved without evaluating the whole carrier.  The exact reroot child
list of each carbon cursor is characterized locally (parent cut plus official grandchildren), the
finite `mapM` is transported across a `List.Perm` of child cursors, and the observable projections
of the two sorted sibling key lists are compared by the existing order-insensitive theorem
`constitutional_observables_eq_of_perm`.
-/

/-! ## The syntactically admitted source -/

/-- Sulfur at `0`, three carbons at `1,2,3` doubly bonded to `0`, and one hydrogen pair on each
carbon at `4..9`.  No coordinates are supplied. -/
def source : AuthoritativeChemicalInput :=
  let sulfur : PeriodicElement := ⟨16, by decide, by decide⟩
  let carbon : PeriodicElement := ⟨6, by decide, by decide⟩
  let hydrogen : PeriodicElement := ⟨1, by decide, by decide⟩
  let bond (first second order : Nat) : SemanticInteraction :=
    { participants := [first, second], kind := .covalent order }
  { molecule :=
      { atoms :=
          [sulfur, carbon, carbon, carbon,
            hydrogen, hydrogen, hydrogen, hydrogen, hydrogen, hydrogen].map
            fun element => { element := element }
        interactions :=
          [ bond 0 1 2, bond 0 2 2, bond 0 3 2
          , bond 1 4 1, bond 1 5 1
          , bond 2 6 1, bond 2 7 1
          , bond 3 8 1, bond 3 9 1 ] } }

/-- The fixture passes the structural admission gate. -/
theorem source_structurallyWellFormed : source.structurallyWellFormed? = true := by
  decide

/-- The fixture passes the localized-graph readiness gate. -/
theorem source_localizedGraphReady :
    source.molecule.localizedCIPGraphReady? = true := by
  decide

/-- The certified authoritative input built from the fixture. -/
def certifiedSource : CertifiedAuthoritativeChemicalInput :=
  { input := source
    structurallyWellFormed :=
      (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff source).mp
        source_structurallyWellFormed }

/-- The certified localized input built from the fixture. -/
def localizedSource : CertifiedLocalizedCIPInput :=
  { certified := certifiedSource
    graphReady :=
      (certifiedSource.input.molecule.localizedCIPGraphReady?_eq_true_iff).mp
        source_localizedGraphReady }

/-- The runtime input of the complete localized evaluator. -/
def input : LocalizedReference.Input :=
  { certified := localizedSource }

/-- **Admission.**  The real source-admission pipeline returns exactly the constructed input. -/
theorem admission : LocalizedReference.admitSource? source = some input := rfl

/-- The carrier fuel of the admitted input. -/
def fuel : Nat := LocalizedShortCircuit.carrierFuel input

/-- The carrier fuel is the atom count plus one, here `11`. -/
theorem fuel_eq : fuel = 11 := rfl

/-! ## The atoms of the fixture -/

def atom0 : localizedSource.Atom := ⟨0, by decide⟩
def atom1 : localizedSource.Atom := ⟨1, by decide⟩
def atom2 : localizedSource.Atom := ⟨2, by decide⟩
def atom3 : localizedSource.Atom := ⟨3, by decide⟩
def atom4 : localizedSource.Atom := ⟨4, by decide⟩
def atom5 : localizedSource.Atom := ⟨5, by decide⟩
def atom6 : localizedSource.Atom := ⟨6, by decide⟩
def atom7 : localizedSource.Atom := ⟨7, by decide⟩
def atom8 : localizedSource.Atom := ⟨8, by decide⟩
def atom9 : localizedSource.Atom := ⟨9, by decide⟩

/-! ## Kernel computation of the sorted neighbor lists -/

/-- If `l` is a nodup, sorted enumeration of `s`, then `s.sort` is `l`. -/
theorem sort_of_toFinset_eq (a : localizedSource.Atom) (l : List localizedSource.Atom)
    (hset : l.toFinset = localizedSource.moleculeGraph.neighborFinset a)
    (hnd : l.Nodup) (hpw : l.Pairwise (· ≤ ·)) :
    (localizedSource.moleculeGraph.neighborFinset a).sort (· ≤ ·) = l := by
  rw [← hset]
  exact (List.toFinset_sort (r := (· ≤ ·)) (l := l) hnd).mpr hpw

/-- The sorted neighbor list of every atom of the fixture. -/
theorem neighborSort_eq (a : localizedSource.Atom) :
    (localizedSource.moleculeGraph.neighborFinset a).sort (· ≤ ·) =
      match a.val with
      | 0 => [atom1, atom2, atom3]
      | 1 => [atom0, atom4, atom5]
      | 2 => [atom0, atom6, atom7]
      | 3 => [atom0, atom8, atom9]
      | 4 => [atom1]
      | 5 => [atom1]
      | 6 => [atom2]
      | 7 => [atom2]
      | 8 => [atom3]
      | 9 => [atom3]
      | _ => [] := by
  fin_cases a
  · exact sort_of_toFinset_eq ⟨0, by decide⟩ [atom1, atom2, atom3]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq ⟨1, by decide⟩ [atom0, atom4, atom5]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq ⟨2, by decide⟩ [atom0, atom6, atom7]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq ⟨3, by decide⟩ [atom0, atom8, atom9]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq ⟨4, by decide⟩ [atom1]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq ⟨5, by decide⟩ [atom1]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq ⟨6, by decide⟩ [atom2]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq ⟨7, by decide⟩ [atom2]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq ⟨8, by decide⟩ [atom3]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq ⟨9, by decide⟩ [atom3]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)

/-! ## The atom-`0` root and its six executable children -/

/-- The atom-`0` occurrence root with no incoming cut. -/
def root : localizedSource.LocalizedRerootCursor fuel :=
  { occurrence := localizedSource.localizedAtomRootOccurrenceExecutable fuel atom0 }

/-- The atom-`0` root records no incoming cut. -/
theorem root_previous : root.previous? = none := rfl

/-- The root node of the official hierarchy at atom `0`. -/
def rootNode : OfficialCIPNode localizedSource.Atom := OfficialCIPNode.root atom0

/-- The real first copy of the carbon child at atom `1`. -/
def node1 : OfficialCIPNode localizedSource.Atom := rootNode.extend atom1 0
/-- The multiple-bond duplicate copy of the carbon child at atom `1`. -/
def node1d : OfficialCIPNode localizedSource.Atom := rootNode.extend atom1 1
/-- The real first copy of the carbon child at atom `2`. -/
def node2 : OfficialCIPNode localizedSource.Atom := rootNode.extend atom2 0
/-- The multiple-bond duplicate copy of the carbon child at atom `2`. -/
def node2d : OfficialCIPNode localizedSource.Atom := rootNode.extend atom2 1
/-- The real first copy of the carbon child at atom `3`. -/
def node3 : OfficialCIPNode localizedSource.Atom := rootNode.extend atom3 0
/-- The multiple-bond duplicate copy of the carbon child at atom `3`. -/
def node3d : OfficialCIPNode localizedSource.Atom := rootNode.extend atom3 1

/-- **Exact root children.** -/
theorem rootChildren_eq :
    localizedSource.executableOfficialCIPChildren rootNode =
      [node1, node1d, node2, node2d, node3, node3d] := by
  simp only [executableOfficialCIPChildren, executableOfficialChildCopies,
    executableOfficialNeighborCopies, neighborSort_eq, rootNode, node1, node1d, node2, node2d,
    node3, node3d, atom0]
  decide

/-- The atom-`1` node has the three executable children: the multiple-bond duplicate of its sulfur
parent and the two hydrogens. -/
def c1Node0 : OfficialCIPNode localizedSource.Atom := node1.extend atom0 1
def c1NodeH4 : OfficialCIPNode localizedSource.Atom := node1.extend atom4 0
def c1NodeH5 : OfficialCIPNode localizedSource.Atom := node1.extend atom5 0

theorem c1Children_eq :
    localizedSource.executableOfficialCIPChildren node1 =
      [c1Node0, c1NodeH4, c1NodeH5] := by
  simp only [executableOfficialCIPChildren, executableOfficialChildCopies,
    executableOfficialNeighborCopies, neighborSort_eq, node1, rootNode, c1Node0, c1NodeH4,
    c1NodeH5, atom0, atom1]
  decide

def c2Node0 : OfficialCIPNode localizedSource.Atom := node2.extend atom0 1
def c2NodeH6 : OfficialCIPNode localizedSource.Atom := node2.extend atom6 0
def c2NodeH7 : OfficialCIPNode localizedSource.Atom := node2.extend atom7 0

theorem c2Children_eq :
    localizedSource.executableOfficialCIPChildren node2 =
      [c2Node0, c2NodeH6, c2NodeH7] := by
  simp only [executableOfficialCIPChildren, executableOfficialChildCopies,
    executableOfficialNeighborCopies, neighborSort_eq, node2, rootNode, c2Node0, c2NodeH6,
    c2NodeH7, atom0, atom2]
  decide

def c3Node0 : OfficialCIPNode localizedSource.Atom := node3.extend atom0 1
def c3NodeH8 : OfficialCIPNode localizedSource.Atom := node3.extend atom8 0
def c3NodeH9 : OfficialCIPNode localizedSource.Atom := node3.extend atom9 0

theorem c3Children_eq :
    localizedSource.executableOfficialCIPChildren node3 =
      [c3Node0, c3NodeH8, c3NodeH9] := by
  simp only [executableOfficialCIPChildren, executableOfficialChildCopies,
    executableOfficialNeighborCopies, neighborSort_eq, node3, rootNode, c3Node0, c3NodeH8,
    c3NodeH9, atom0, atom3]
  decide

/-! ## The three real carbon children of the root -/

/-- The occurrence frame of the first carbon: root atom `0`, address `[0]`, carbon node. -/
def frame1 : localizedSource.LocalizedCIPOccurrenceFrame :=
  { root := atom0, address := [0], node := node1, remaining := fuel }

/-- The occurrence frame of the second carbon: address `[2]`. -/
def frame2 : localizedSource.LocalizedCIPOccurrenceFrame :=
  { root := atom0, address := [2], node := node2, remaining := fuel }

/-- The occurrence frame of the third carbon: address `[4]`. -/
def frame3 : localizedSource.LocalizedCIPOccurrenceFrame :=
  { root := atom0, address := [4], node := node3, remaining := fuel }

/-- The first carbon occurrence belongs to the molecule-wide carrier. -/
theorem frame1_mem : frame1 ∈ localizedSource.localizedOccurrences fuel := by
  rw [localizedSource.mem_localizedOccurrences_iff]
  exact DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (path := []) (fuel := fuel) (node := rootNode) (child := node1) (slot := 0)
    (occurrence := frame1)
    (by rw [rootChildren_eq]; decide)
    (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot [0] fuel node1)

/-- The second carbon occurrence is the official child at slot `2` of the atom-`0` root. -/
theorem frame2_mem : frame2 ∈ localizedSource.localizedOccurrences fuel := by
  rw [localizedSource.mem_localizedOccurrences_iff]
  exact DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (path := []) (fuel := fuel) (node := rootNode) (child := node2) (slot := 2)
    (occurrence := frame2)
    (by rw [rootChildren_eq]; decide)
    (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot [2] fuel node2)

/-- The third carbon occurrence is the official child at slot `4` of the atom-`0` root. -/
theorem frame3_mem : frame3 ∈ localizedSource.localizedOccurrences fuel := by
  rw [localizedSource.mem_localizedOccurrences_iff]
  exact DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (path := []) (fuel := fuel) (node := rootNode) (child := node3) (slot := 4)
    (occurrence := frame3)
    (by rw [rootChildren_eq]; decide)
    (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot [4] fuel node3)

/-- The first real carbon child, with the sulfur root recorded as incoming cut. -/
def c1 : localizedSource.LocalizedRerootCursor fuel :=
  { occurrence := ⟨frame1, frame1_mem⟩, previous? := some root.occurrence }

/-- The second real carbon child, with the sulfur root recorded as incoming cut. -/
def c2 : localizedSource.LocalizedRerootCursor fuel :=
  { occurrence := ⟨frame2, frame2_mem⟩, previous? := some root.occurrence }

/-- The third real carbon child, with the sulfur root recorded as incoming cut. -/
def c3 : localizedSource.LocalizedRerootCursor fuel :=
  { occurrence := ⟨frame3, frame3_mem⟩, previous? := some root.occurrence }

/-- **Exact membership** of the first carbon child of the atom-`0` root. -/
theorem c1_mem : c1 ∈ localizedSource.executableLocalizedRerootChildren root := by
  obtain ⟨children, childCursor, computed, memChild, frameEq⟩ :=
    localizedSource.exists_mem_localizedRerootChildren_of_executable_child
      (cursor := root) (nonduplicate := rfl) (positive := by decide)
      (child := node1) (slot := 0)
      (childAtSlot := by
        show (node1, 0) ∈ (localizedSource.executableOfficialCIPChildren rootNode).zipIdx
        rw [rootChildren_eq]; decide)
      (notIncoming := by
        intro previous h
        rw [root_previous] at h
        cases h)
  have sound := localizedSource.localizedRerootChildren?_sound root children computed
  have prevEq : childCursor.previous? = some root.occurrence := sound.2 childCursor memChild
  have executableEq : children = localizedSource.executableLocalizedRerootChildren root := by
    have h := localizedSource.localizedRerootChildren?_eq_some_executable root
    rw [computed] at h
    exact Option.some.inj h
  have childEq : childCursor = c1 := by
    apply LocalizedRerootCursor.ext
    · apply Subtype.ext
      rw [frameEq]
      rfl
    · rw [prevEq]
      rfl
  rw [← executableEq, ← childEq]
  exact memChild

/-- **Exact membership** of the second carbon child of the atom-`0` root. -/
theorem c2_mem : c2 ∈ localizedSource.executableLocalizedRerootChildren root := by
  obtain ⟨children, childCursor, computed, memChild, frameEq⟩ :=
    localizedSource.exists_mem_localizedRerootChildren_of_executable_child
      (cursor := root) (nonduplicate := rfl) (positive := by decide)
      (child := node2) (slot := 2)
      (childAtSlot := by
        show (node2, 2) ∈ (localizedSource.executableOfficialCIPChildren rootNode).zipIdx
        rw [rootChildren_eq]; decide)
      (notIncoming := by
        intro previous h
        rw [root_previous] at h
        cases h)
  have sound := localizedSource.localizedRerootChildren?_sound root children computed
  have prevEq : childCursor.previous? = some root.occurrence := sound.2 childCursor memChild
  have executableEq : children = localizedSource.executableLocalizedRerootChildren root := by
    have h := localizedSource.localizedRerootChildren?_eq_some_executable root
    rw [computed] at h
    exact Option.some.inj h
  have childEq : childCursor = c2 := by
    apply LocalizedRerootCursor.ext
    · apply Subtype.ext
      rw [frameEq]
      rfl
    · rw [prevEq]
      rfl
  rw [← executableEq, ← childEq]
  exact memChild

/-- **Exact membership** of the third carbon child of the atom-`0` root. -/
theorem c3_mem : c3 ∈ localizedSource.executableLocalizedRerootChildren root := by
  obtain ⟨children, childCursor, computed, memChild, frameEq⟩ :=
    localizedSource.exists_mem_localizedRerootChildren_of_executable_child
      (cursor := root) (nonduplicate := rfl) (positive := by decide)
      (child := node3) (slot := 4)
      (childAtSlot := by
        show (node3, 4) ∈ (localizedSource.executableOfficialCIPChildren rootNode).zipIdx
        rw [rootChildren_eq]; decide)
      (notIncoming := by
        intro previous h
        rw [root_previous] at h
        cases h)
  have sound := localizedSource.localizedRerootChildren?_sound root children computed
  have prevEq : childCursor.previous? = some root.occurrence := sound.2 childCursor memChild
  have executableEq : children = localizedSource.executableLocalizedRerootChildren root := by
    have h := localizedSource.localizedRerootChildren?_eq_some_executable root
    rw [computed] at h
    exact Option.some.inj h
  have childEq : childCursor = c3 := by
    apply LocalizedRerootCursor.ext
    · apply Subtype.ext
      rw [frameEq]
      rfl
    · rw [prevEq]
      rfl
  rw [← executableEq, ← childEq]
  exact memChild

/-- The exact coordinates of the three carbon cursors. -/
@[simp] theorem c1_address : c1.occurrence.1.address = [0] := rfl
@[simp] theorem c2_address : c2.occurrence.1.address = [2] := rfl
@[simp] theorem c3_address : c3.occurrence.1.address = [4] := rfl

@[simp] theorem c1_current : c1.occurrence.1.node.current? = some atom1 := rfl
@[simp] theorem c2_current : c2.occurrence.1.node.current? = some atom2 := rfl
@[simp] theorem c3_current : c3.occurrence.1.node.current? = some atom3 := rfl

@[simp] theorem c1_provenance :
    c1.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom := rfl
@[simp] theorem c2_provenance :
    c2.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom := rfl
@[simp] theorem c3_provenance :
    c3.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom := rfl

@[simp] theorem c1_previous : c1.previous? = some root.occurrence := rfl
@[simp] theorem c2_previous : c2.previous? = some root.occurrence := rfl
@[simp] theorem c3_previous : c3.previous? = some root.occurrence := rfl

/-- Erasing a vertex from a sorted enumeration stays sorted and agrees with the explicit list
erase. -/
theorem sort_erase_eq (s : Finset localizedSource.Atom) (b : localizedSource.Atom)
    (l : List localizedSource.Atom) (hl : s.sort (· ≤ ·) = l) :
    (s.erase b).sort (· ≤ ·) = l.erase b := by
  have hnd : l.Nodup := hl ▸ Finset.sort_nodup s (· ≤ ·)
  have hpw : l.Pairwise (· ≤ ·) := hl ▸ Finset.pairwise_sort s (· ≤ ·)
  have htoF : l.toFinset = s := hl ▸ Finset.sort_toFinset s (· ≤ ·)
  have htoFe : (l.erase b).toFinset = s.erase b := by
    ext x
    rw [List.mem_toFinset, Finset.mem_erase]
    constructor
    · intro hx
      refine ⟨fun hxb => hnd.not_mem_erase (hxb ▸ hx), ?_⟩
      rw [← htoF]
      exact List.mem_toFinset.mpr (List.mem_of_mem_erase (l := l) (b := b) hx)
    · rintro ⟨hxb, hx⟩
      exact (List.mem_erase_of_ne (l := l) (a := x) (b := b) hxb).mpr
        (by rwa [← htoF, List.mem_toFinset] at hx)
  have hpwe : (l.erase b).Pairwise (· ≤ ·) := by
    rw [hnd.erase_eq_filter]
    exact hpw.filter (fun x => x != b)
  have h :=
    (List.toFinset_sort (r := (· ≤ ·)) (l := l.erase b) (hnd.erase b)).mpr hpwe
  rwa [htoFe] at h

/-- The explicit Rule-3 substituent list of every ordered pair of atoms. -/
theorem explicitSubstituents_eq (endpoint partner : localizedSource.Atom) :
    localizedSource.localizedRule3ExplicitSubstituents endpoint partner =
      (match endpoint.val with
       | 0 => [atom1, atom2, atom3]
       | 1 => [atom0, atom4, atom5]
       | 2 => [atom0, atom6, atom7]
       | 3 => [atom0, atom8, atom9]
       | 4 => [atom1]
       | 5 => [atom1]
       | 6 => [atom2]
       | 7 => [atom2]
       | 8 => [atom3]
       | 9 => [atom3]
       | _ => []).erase partner := by
  fin_cases endpoint <;> exact sort_erase_eq _ partner _ (neighborSort_eq _)

/-! ## Root coordinate and the two endpoint cursors of the first carbon -/

@[simp] theorem root_address : root.occurrence.1.address = [] := rfl
@[simp] theorem root_remaining : root.occurrence.1.remaining = fuel + 1 := rfl
@[simp] theorem root_node : root.occurrence.1.node = rootNode := rfl
@[simp] theorem root_current : root.occurrence.1.node.current? = some atom0 := rfl
@[simp] theorem root_provenance :
    root.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom := rfl

@[simp] theorem node1_parent : node1.parent? = some atom0 := rfl
@[simp] theorem node1_current : node1.current? = some atom1 := rfl
@[simp] theorem node1_provenance : node1.provenance = OfficialCIPNodeProvenance.realAtom := by
  decide
@[simp] theorem node1_not_duplicate : node1.isDuplicateLeaf = false := by
  decide

/-- The carrier parent of the first carbon is the atom-`0` root occurrence. -/
theorem carrierParent_c1 :
    localizedSource.DeclarativeLocalizedRule3CarrierParentOccurrence c1.occurrence root.occurrence := by
  unfold DeclarativeLocalizedRule3CarrierParentOccurrence localizedCarrierParentFrames
  rw [List.mem_filter]
  exact ⟨root.occurrence.2, by decide⟩

/-- The left endpoint cursor of the double bond `0 = 1`, entered from the first carbon. -/
def leftCursor1 : localizedSource.LocalizedRerootCursor fuel :=
  { occurrence := root.occurrence, previous? := some c1.occurrence }

/-- The right endpoint cursor of the double bond `0 = 1`, entered from the sulfur root. -/
def rightCursor1 : localizedSource.LocalizedRerootCursor fuel :=
  { occurrence := c1.occurrence, previous? := some root.occurrence }

/-- The oriented physical endpoint frame of the double bond `0 = 1`. -/
def topology1 : localizedSource.LocalizedRule3PhysicalEndpointCursorFrame fuel :=
  { left := atom0
    right := atom1
    leftCursor := leftCursor1
    rightCursor := rightCursor1 }

/-- The declarative meaning of `topology1`, component by component. -/
theorem topology1_spec :
    localizedSource.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame c1.occurrence topology1 := by
  refine ⟨rfl, rfl, rfl, by decide, carrierParent_c1, rfl, rfl, rfl, rfl⟩

/-- **Physical endpoint recovery** at the first carbon. -/
theorem physical_c1 :
    localizedSource.localizedRule3PhysicalEndpointCursorFrameExec? c1.occurrence =
      some topology1 :=
  localizedSource.localizedRule3PhysicalEndpointCursorFrameExec?_eq_some_of_declarative
    c1.occurrence topology1 topology1_spec

theorem substituents_0_1 :
    localizedSource.localizedRule3ExplicitSubstituents atom0 atom1 = [atom2, atom3] := by
  rw [explicitSubstituents_eq]
  rfl

theorem substituents_1_0 :
    localizedSource.localizedRule3ExplicitSubstituents atom1 atom0 = [atom4, atom5] := by
  rw [explicitSubstituents_eq]
  rfl

@[simp] theorem leftCursor1_previous : leftCursor1.previous? = some c1.occurrence := rfl
@[simp] theorem leftCursor1_address : leftCursor1.occurrence.1.address = [] := rfl
@[simp] theorem leftCursor1_remaining : leftCursor1.occurrence.1.remaining = fuel + 1 := rfl
@[simp] theorem leftCursor1_current : leftCursor1.occurrence.1.node.current? = some atom0 := rfl
@[simp] theorem leftCursor1_provenance :
    leftCursor1.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom := rfl

@[simp] theorem rightCursor1_previous : rightCursor1.previous? = some root.occurrence := rfl
@[simp] theorem rightCursor1_address : rightCursor1.occurrence.1.address = [0] := rfl
@[simp] theorem rightCursor1_remaining : rightCursor1.occurrence.1.remaining = fuel := rfl
@[simp] theorem rightCursor1_current : rightCursor1.occurrence.1.node.current? = some atom1 := rfl
@[simp] theorem rightCursor1_provenance :
    rightCursor1.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom := by
  decide

/-- The second carbon is an exact executable child of the left endpoint cursor. -/
theorem exists_children_c2 :
    ∃ children, localizedSource.localizedRerootChildren? leftCursor1 = some children ∧
      c2 ∈ children ∧
      localizedSource.DeclarativeLocalizedRerootChildren leftCursor1 children := by
  obtain ⟨children, childCursor, computed, memChild, frameEq⟩ :=
    localizedSource.exists_mem_localizedRerootChildren_of_executable_child
      (cursor := leftCursor1) (nonduplicate := by decide) (positive := by decide)
      (child := node2) (slot := 2)
      (childAtSlot := by
        show (node2, 2) ∈
          (localizedSource.executableOfficialCIPChildren rootNode).zipIdx
        rw [rootChildren_eq]; decide)
      (notIncoming := by
        intro previous h
        rw [leftCursor1_previous] at h
        cases h
        decide)
  have derived := localizedSource.localizedRerootChildren?_sound leftCursor1 children computed
  have cursorEq : childCursor = c2 := by
    apply LocalizedRerootCursor.ext
    · apply Subtype.ext
      rw [frameEq]
      rfl
    · rw [derived.2 childCursor memChild]
      rfl
  exact ⟨children, computed, cursorEq ▸ memChild, derived⟩

/-- The third carbon is an exact executable child of the left endpoint cursor. -/
theorem exists_children_c3 :
    ∃ children, localizedSource.localizedRerootChildren? leftCursor1 = some children ∧
      c3 ∈ children ∧
      localizedSource.DeclarativeLocalizedRerootChildren leftCursor1 children := by
  obtain ⟨children, childCursor, computed, memChild, frameEq⟩ :=
    localizedSource.exists_mem_localizedRerootChildren_of_executable_child
      (cursor := leftCursor1) (nonduplicate := by decide) (positive := by decide)
      (child := node3) (slot := 4)
      (childAtSlot := by
        show (node3, 4) ∈
          (localizedSource.executableOfficialCIPChildren rootNode).zipIdx
        rw [rootChildren_eq]; decide)
      (notIncoming := by
        intro previous h
        rw [leftCursor1_previous] at h
        cases h
        decide)
  have derived := localizedSource.localizedRerootChildren?_sound leftCursor1 children computed
  have cursorEq : childCursor = c3 := by
    apply LocalizedRerootCursor.ext
    · apply Subtype.ext
      rw [frameEq]
      rfl
    · rw [derived.2 childCursor memChild]
      rfl
  exact ⟨children, computed, cursorEq ▸ memChild, derived⟩

/-- **Reference selection at the left endpoint** for atom `2`. -/
theorem refExec_c2 :
    localizedSource.localizedRule3ReferenceCursorExec? leftCursor1 atom2 = some c2 := by
  have declarative : localizedSource.DeclarativeLocalizedRule3ReferenceCursor
      leftCursor1 c2 atom2 := by
    obtain ⟨children, computed, mem, derived⟩ := exists_children_c2
    exact ⟨children, computed, derived, mem, rfl, trivial, rfl⟩
  rw [← localizedSource.localizedRule3ReferenceCursor?_eq_localizedRule3ReferenceCursorExec?]
  exact localizedSource.localizedRule3ReferenceCursor?_eq_some_of_declarative
    leftCursor1 c2 atom2 declarative

/-- **Reference selection at the left endpoint** for atom `3`. -/
theorem refExec_c3 :
    localizedSource.localizedRule3ReferenceCursorExec? leftCursor1 atom3 = some c3 := by
  have declarative : localizedSource.DeclarativeLocalizedRule3ReferenceCursor
      leftCursor1 c3 atom3 := by
    obtain ⟨children, computed, mem, derived⟩ := exists_children_c3
    exact ⟨children, computed, derived, mem, rfl, trivial, rfl⟩
  rw [← localizedSource.localizedRule3ReferenceCursor?_eq_localizedRule3ReferenceCursorExec?]
  exact localizedSource.localizedRule3ReferenceCursor?_eq_some_of_declarative
    leftCursor1 c3 atom3 declarative

/-! ### The hydrogen children of the first carbon -/

def h4Frame : localizedSource.LocalizedCIPOccurrenceFrame :=
  { root := atom0, address := [0, 1], node := c1NodeH4, remaining := fuel - 1 }

def h5Frame : localizedSource.LocalizedCIPOccurrenceFrame :=
  { root := atom0, address := [0, 2], node := c1NodeH5, remaining := fuel - 1 }

theorem h4Frame_mem : h4Frame ∈ localizedSource.localizedOccurrences fuel := by
  rw [localizedSource.mem_localizedOccurrences_iff]
  exact DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (path := []) (fuel := fuel) (node := rootNode) (child := node1) (slot := 0)
    (occurrence := h4Frame)
    (by rw [rootChildren_eq]; decide)
    (DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (path := [0]) (fuel := fuel - 1) (node := node1) (child := c1NodeH4) (slot := 1)
      (occurrence := h4Frame)
      (by
        show (c1NodeH4, 1) ∈
          (localizedSource.executableOfficialCIPChildren node1).zipIdx
        rw [c1Children_eq]; decide)
      (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot [0, 1] (fuel - 1) c1NodeH4))

theorem h5Frame_mem : h5Frame ∈ localizedSource.localizedOccurrences fuel := by
  rw [localizedSource.mem_localizedOccurrences_iff]
  exact DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (path := []) (fuel := fuel) (node := rootNode) (child := node1) (slot := 0)
    (occurrence := h5Frame)
    (by rw [rootChildren_eq]; decide)
    (DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (path := [0]) (fuel := fuel - 1) (node := node1) (child := c1NodeH5) (slot := 2)
      (occurrence := h5Frame)
      (by
        show (c1NodeH5, 2) ∈
          (localizedSource.executableOfficialCIPChildren node1).zipIdx
        rw [c1Children_eq]; decide)
      (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot [0, 2] (fuel - 1) c1NodeH5))

def h4 : localizedSource.LocalizedRerootCursor fuel :=
  { occurrence := ⟨h4Frame, h4Frame_mem⟩, previous? := some rightCursor1.occurrence }

def h5 : localizedSource.LocalizedRerootCursor fuel :=
  { occurrence := ⟨h5Frame, h5Frame_mem⟩, previous? := some rightCursor1.occurrence }

@[simp] theorem h4_previous : h4.previous? = some rightCursor1.occurrence := rfl
@[simp] theorem h5_previous : h5.previous? = some rightCursor1.occurrence := rfl
@[simp] theorem h4_current : h4.occurrence.1.node.current? = some atom4 := rfl
@[simp] theorem h5_current : h5.occurrence.1.node.current? = some atom5 := rfl

theorem h4_provenance :
    h4.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom := by
  decide

theorem h5_provenance :
    h5.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom := by
  decide

theorem exists_children_h4 :
    ∃ children, localizedSource.localizedRerootChildren? rightCursor1 = some children ∧
      h4 ∈ children ∧
      localizedSource.DeclarativeLocalizedRerootChildren rightCursor1 children := by
  obtain ⟨children, childCursor, computed, memChild, frameEq⟩ :=
    localizedSource.exists_mem_localizedRerootChildren_of_executable_child
      (cursor := rightCursor1) (nonduplicate := by decide) (positive := by decide)
      (child := c1NodeH4) (slot := 1)
      (childAtSlot := by
        show (c1NodeH4, 1) ∈
          (localizedSource.executableOfficialCIPChildren node1).zipIdx
        rw [c1Children_eq]; decide)
      (notIncoming := by
        intro previous h
        rw [rightCursor1_previous] at h
        cases h
        decide)
  have derived := localizedSource.localizedRerootChildren?_sound rightCursor1 children computed
  have cursorEq : childCursor = h4 := by
    apply LocalizedRerootCursor.ext
    · apply Subtype.ext
      rw [frameEq]
      rfl
    · rw [derived.2 childCursor memChild]
      rfl
  exact ⟨children, computed, cursorEq ▸ memChild, derived⟩

theorem exists_children_h5 :
    ∃ children, localizedSource.localizedRerootChildren? rightCursor1 = some children ∧
      h5 ∈ children ∧
      localizedSource.DeclarativeLocalizedRerootChildren rightCursor1 children := by
  obtain ⟨children, childCursor, computed, memChild, frameEq⟩ :=
    localizedSource.exists_mem_localizedRerootChildren_of_executable_child
      (cursor := rightCursor1) (nonduplicate := by decide) (positive := by decide)
      (child := c1NodeH5) (slot := 2)
      (childAtSlot := by
        show (c1NodeH5, 2) ∈
          (localizedSource.executableOfficialCIPChildren node1).zipIdx
        rw [c1Children_eq]; decide)
      (notIncoming := by
        intro previous h
        rw [rightCursor1_previous] at h
        cases h
        decide)
  have derived := localizedSource.localizedRerootChildren?_sound rightCursor1 children computed
  have cursorEq : childCursor = h5 := by
    apply LocalizedRerootCursor.ext
    · apply Subtype.ext
      rw [frameEq]
      rfl
    · rw [derived.2 childCursor memChild]
      rfl
  exact ⟨children, computed, cursorEq ▸ memChild, derived⟩

/-- **Reference selection at the right endpoint** for atom `4`. -/
theorem refExec_h4 :
    localizedSource.localizedRule3ReferenceCursorExec? rightCursor1 atom4 = some h4 := by
  have declarative : localizedSource.DeclarativeLocalizedRule3ReferenceCursor
      rightCursor1 h4 atom4 := by
    obtain ⟨children, computed, mem, derived⟩ := exists_children_h4
    exact ⟨children, computed, derived, mem, rfl, trivial, rfl⟩
  rw [← localizedSource.localizedRule3ReferenceCursor?_eq_localizedRule3ReferenceCursorExec?]
  exact localizedSource.localizedRule3ReferenceCursor?_eq_some_of_declarative
    rightCursor1 h4 atom4 declarative

/-- **Reference selection at the right endpoint** for atom `5`. -/
theorem refExec_h5 :
    localizedSource.localizedRule3ReferenceCursorExec? rightCursor1 atom5 = some h5 := by
  have declarative : localizedSource.DeclarativeLocalizedRule3ReferenceCursor
      rightCursor1 h5 atom5 := by
    obtain ⟨children, computed, mem, derived⟩ := exists_children_h5
    exact ⟨children, computed, derived, mem, rfl, trivial, rfl⟩
  rw [← localizedSource.localizedRule3ReferenceCursor?_eq_localizedRule3ReferenceCursorExec?]
  exact localizedSource.localizedRule3ReferenceCursor?_eq_some_of_declarative
    rightCursor1 h5 atom5 declarative

/-! ## Pair readiness of the first carbon -/

theorem pairReady_left1 :
    localizedSource.rule3EndpointPairReady topology1.left topology1.right
      topology1.leftCursor = true := by
  simp only [rule3EndpointPairReady, topology1, substituents_0_1, refExec_c2, refExec_c3,
    Option.isSome_some]
  rfl

theorem pairReady_right1 :
    localizedSource.rule3EndpointPairReady topology1.right topology1.left
      topology1.rightCursor = true := by
  simp only [rule3EndpointPairReady, topology1, substituents_1_0, refExec_h4, refExec_h5,
    Option.isSome_some]
  rfl

/-- **Readiness of the first carbon endpoint.** -/
theorem ordinaryPairReady_c1 :
    localizedSource.ordinaryPairReady c1.occurrence = true := by
  simp only [ordinaryPairReady, physical_c1, topology1, rule3EndpointPairReady,
    substituents_0_1, substituents_1_0, refExec_c2, refExec_c3, refExec_h4, refExec_h5,
    Option.isSome_some]
  rfl

/-! ## The physical route certificate of the first carbon -/

/-- The first carbon is a real node on an order-two bond. -/
theorem edge_c1 :
    localizedSource.LocalizedOccurrenceHasRule3DoubleBondEdge c1.occurrence := by
  refine ⟨rfl, atom1, atom0, rfl, rfl, ?_⟩
  decide

/-- The second carbon is an exact child in the total executable child list of the left endpoint
cursor. -/
theorem c2_mem_executableChildren :
    c2 ∈ localizedSource.executableLocalizedRerootChildren leftCursor1 := by
  obtain ⟨children, computed, mem, _derived⟩ := exists_children_c2
  have executableEq := localizedSource.localizedRerootChildren?_eq_some_executable leftCursor1
  have childrenEq : children = localizedSource.executableLocalizedRerootChildren leftCursor1 :=
    (Option.some.injEq _ _).mp (computed.symm.trans executableEq)
  rwa [childrenEq] at mem

/-- The third carbon is an exact child in the total executable child list of the left endpoint
cursor. -/
theorem c3_mem_executableChildren :
    c3 ∈ localizedSource.executableLocalizedRerootChildren leftCursor1 := by
  obtain ⟨children, computed, mem, _derived⟩ := exists_children_c3
  have executableEq := localizedSource.localizedRerootChildren?_eq_some_executable leftCursor1
  have childrenEq : children = localizedSource.executableLocalizedRerootChildren leftCursor1 :=
    (Option.some.injEq _ _).mp (computed.symm.trans executableEq)
  rwa [childrenEq] at mem

/-- The second carbon is a physical order-two continuation of the sulfur endpoint cursor. -/
theorem axisContinuation_c2 :
    localizedSource.LocalizedRule3AxisPhysicalContinuation leftCursor1 c2 := by
  refine ⟨leftCursor1_provenance, ?_, ?_⟩
  · decide
  · show localizedSource.moleculeGraph.bond atom0 atom2 = 2
    decide

/-- The third carbon is a physical order-two continuation of the sulfur endpoint cursor. -/
theorem axisContinuation_c3 :
    localizedSource.LocalizedRule3AxisPhysicalContinuation leftCursor1 c3 := by
  refine ⟨leftCursor1_provenance, ?_, ?_⟩
  · decide
  · show localizedSource.moleculeGraph.bond atom0 atom3 = 2
    decide

/-- The two real carbon continuations are distinct cursors. -/
theorem c2_ne_c3 : c2 ≠ c3 := by
  intro equally
  have addresses := congrArg (fun cursor => cursor.occurrence.1.address) equally
  simp only at addresses
  rw [c2_address, c3_address] at addresses
  exact absurd addresses (by decide)

/-- A list with two distinct members has length at least two. -/
theorem two_le_length_of_mem_of_mem {α : Type*} {values : List α} {first second : α}
    (firstPresent : first ∈ values) (secondPresent : second ∈ values)
    (distinct : first ≠ second) : 2 ≤ values.length := by
  cases values with
  | nil => simp at firstPresent
  | cons head tail =>
      cases tail with
      | nil =>
          simp only [List.mem_singleton] at firstPresent secondPresent
          exact absurd (firstPresent.trans secondPresent.symm) distinct
      | cons next rest => simp

/-- A list of length at least two has a two-element prefix. -/
theorem exists_two_cons_of_two_le_length {α : Type*} {values : List α}
    (long : 2 ≤ values.length) : ∃ first second rest, values = first :: second :: rest := by
  cases values with
  | nil => simp at long
  | cons head tail =>
      cases tail with
      | nil => simp at long
      | cons next rest => exact ⟨head, next, rest, rfl⟩

/-- The executable physical continuations of the left endpoint cursor number at least two. -/
theorem axisContinuations_two_le :
    2 ≤ (localizedSource.localizedRule3AxisPhysicalContinuationCursorsExec leftCursor1
      (localizedSource.executableLocalizedRerootChildren leftCursor1)).length := by
  apply two_le_length_of_mem_of_mem (first := c2) (second := c3)
  · simp only [localizedRule3AxisPhysicalContinuationCursorsExec, List.mem_filter]
    exact ⟨c2_mem_executableChildren, decide_eq_true axisContinuation_c2⟩
  · simp only [localizedRule3AxisPhysicalContinuationCursorsExec, List.mem_filter]
    exact ⟨c3_mem_executableChildren, decide_eq_true axisContinuation_c3⟩
  · exact c2_ne_c3

/-- The cumulated axis topology of the sulfur endpoint cursor is `branched`. -/
theorem axisTopology_c1_branched :
    ∃ first second rest,
      localizedSource.localizedRule3AxisTopologyExec? leftCursor1 =
        some (.branched first second rest) := by
  have long : 2 ≤ ((localizedSource.executableLocalizedRerootChildren leftCursor1).filter
      (fun child => decide (localizedSource.LocalizedRule3AxisPhysicalContinuation
        leftCursor1 child))).length := axisContinuations_two_le
  obtain ⟨first, second, rest, shape⟩ := exists_two_cons_of_two_le_length long
  refine ⟨first, second, rest, ?_⟩
  have expanded :
      localizedSource.localizedRule3AxisPhysicalContinuationCursorsExec? leftCursor1 =
        some ((localizedSource.executableLocalizedRerootChildren leftCursor1).filter
          (fun child => decide (localizedSource.LocalizedRule3AxisPhysicalContinuation
            leftCursor1 child))) := by
    unfold localizedRule3AxisPhysicalContinuationCursorsExec?
      localizedRule3AxisPhysicalContinuationCursorsExec
    rw [executableLocalizedRerootChildren?_eq_some]
    rfl
  unfold localizedRule3AxisTopologyExec?
  rw [expanded, shape]
  rfl

/-- The cumulated axis entry of the first carbon is `branched`. -/
theorem axisEntry_c1_branched :
    ∃ initial first second rest,
      localizedSource.localizedRule3CumulatedAxisEntryExec? c1.occurrence =
        some (.branched initial first second rest) := by
  obtain ⟨first, second, rest, topology⟩ := axisTopology_c1_branched
  refine ⟨topology1, first, second, rest, ?_⟩
  simp [localizedRule3CumulatedAxisEntryExec?, physical_c1, topology1, topology]

/-- The odd-cumulene route is absent at the first carbon: the entry is branched. -/
theorem oddRoute_c1_eq_none :
    localizedSource.localizedRule3OddRouteCertificate? c1.occurrence = none := by
  obtain ⟨initial, first, second, rest, entry⟩ := axisEntry_c1_branched
  simp only [localizedRule3OddRouteCertificate?]
  rw [dif_pos edge_c1]
  rw [entry]

/-- The ordinary one-bond route certificate is present at the first carbon. -/
theorem ordinaryRoute_c1_some :
    ∃ certificate,
      localizedSource.localizedRule3OrdinaryRouteCertificate? c1.occurrence = some certificate := by
  obtain ⟨initial, first, second, rest, entry⟩ := axisEntry_c1_branched
  unfold localizedRule3OrdinaryRouteCertificate?
  rw [dif_pos edge_c1]
  split
  next initial' first' second' rest' entryEq =>
    exact ⟨_, rfl⟩
  next initial' entryEq =>
    rw [entry] at entryEq
    simp at entryEq
  next notBranched notTerminal =>
    exact absurd entry (notBranched initial first second rest)

/-- The preflight extended node requests of the first carbon are exactly its short spatial
requests. -/
theorem requests_c1_eq :
    localizedSource.rule3PreflightExtendedNodeCallbackRequests c1.occurrence =
      localizedSource.rule3ShortSpatialCallbackRequests c1.occurrence := by
  obtain ⟨certificate, ordinary⟩ := ordinaryRoute_c1_some
  simp only [rule3PreflightExtendedNodeCallbackRequests, oddRoute_c1_eq_none, ordinary]
  exact localizedSource.rule3PreflightShortSpatialCallbackRequests_eq_of_ready
    c1.occurrence ordinaryPairReady_c1

/-- The short spatial requests of the first carbon expand into the two oriented endpoint request
lists of the sulfur/carbon double bond. -/
theorem shortSpatial_c1_eq :
    localizedSource.rule3ShortSpatialCallbackRequests c1.occurrence =
      localizedSource.rule3ShortEndpointCallbackRequests atom0 atom1 leftCursor1 ++
        localizedSource.rule3ShortEndpointCallbackRequests atom1 atom0 rightCursor1 := by
  simp only [rule3ShortSpatialCallbackRequests, physical_c1, topology1]

/-- The root constitutional comparison of the second and third carbons defers. -/
theorem rootCompare_c2_c3 :
    localizedSource.compareLocalizedRerootCursorConstitutionalRoot c2 c3 = .eq := by
  decide

/-- The root constitutional comparison of the two hydrogens defers. -/
theorem rootCompare_h4_h5 :
    localizedSource.compareLocalizedRerootCursorConstitutionalRoot h4 h5 = .eq := by
  decide

/-- The left endpoint request of the first carbon is `[[c2, c3]]`, conditional on the
constitutional tie of the two carbon substituents. -/
theorem endpointRequests_0_1_eq_of_tie
    (tie : localizedSource.compareLocalizedConstitutionalCursors? c2 c3 = some .eq) :
    localizedSource.rule3ShortEndpointCallbackRequests atom0 atom1 leftCursor1 = [[c2, c3]] := by
  simp only [rule3ShortEndpointCallbackRequests, substituents_0_1, refExec_c2, refExec_c3,
    rootCompare_c2_c3, tie]

/-- The right endpoint request of the first carbon is `[[h4, h5]]`, conditional on the
constitutional tie of the two hydrogen substituents. -/
theorem endpointRequests_1_0_eq_of_tie
    (tie : localizedSource.compareLocalizedConstitutionalCursors? h4 h5 = some .eq) :
    localizedSource.rule3ShortEndpointCallbackRequests atom1 atom0 rightCursor1 = [[h4, h5]] := by
  simp only [rule3ShortEndpointCallbackRequests, substituents_1_0, refExec_h4, refExec_h5,
    rootCompare_h4_h5, tie]

/-- Exact full request list at the first carbon, conditional on the two endpoint constitutional
ties. -/
theorem requests_c1_eq_pairs_of_ties
    (carbonTie : localizedSource.compareLocalizedConstitutionalCursors? c2 c3 = some .eq)
    (hydrogenTie : localizedSource.compareLocalizedConstitutionalCursors? h4 h5 = some .eq) :
    localizedSource.rule3PreflightExtendedNodeCallbackRequests c1.occurrence =
      [[c2, c3], [h4, h5]] := by
  rw [requests_c1_eq, shortSpatial_c1_eq,
    endpointRequests_0_1_eq_of_tie carbonTie,
    endpointRequests_1_0_eq_of_tie hydrogenTie]
  rfl

/-- The second carbon is demanded at the first carbon, conditional on the two ties. -/
theorem c2_mem_requests_c1_of_ties
    (carbonTie : localizedSource.compareLocalizedConstitutionalCursors? c2 c3 = some .eq)
    (hydrogenTie : localizedSource.compareLocalizedConstitutionalCursors? h4 h5 = some .eq) :
    c2 ∈ (localizedSource.rule3PreflightExtendedNodeCallbackRequests c1.occurrence).flatten := by
  rw [requests_c1_eq_pairs_of_ties carbonTie hydrogenTie]
  simp

/-- The third carbon is demanded at the first carbon, conditional on the two ties. -/
theorem c3_mem_requests_c1_of_ties
    (carbonTie : localizedSource.compareLocalizedConstitutionalCursors? c2 c3 = some .eq)
    (hydrogenTie : localizedSource.compareLocalizedConstitutionalCursors? h4 h5 = some .eq) :
    c3 ∈ (localizedSource.rule3PreflightExtendedNodeCallbackRequests c1.occurrence).flatten := by
  rw [requests_c1_eq_pairs_of_ties carbonTie hydrogenTie]
  simp

/-! ## The second sulfur--carbon endpoint -/

/-- The carrier parent of the second carbon is the atom-`0` root occurrence. -/
theorem carrierParent_c2 :
    localizedSource.DeclarativeLocalizedRule3CarrierParentOccurrence c2.occurrence root.occurrence := by
  unfold DeclarativeLocalizedRule3CarrierParentOccurrence localizedCarrierParentFrames
  rw [List.mem_filter]
  exact ⟨root.occurrence.2, by decide⟩

/-- The left endpoint cursor of the double bond `0 = 2`, entered from the second carbon. -/
def leftCursor2 : localizedSource.LocalizedRerootCursor fuel :=
  { occurrence := root.occurrence, previous? := some c2.occurrence }

/-- The right endpoint cursor of the double bond `0 = 2`, entered from the sulfur root. -/
def rightCursor2 : localizedSource.LocalizedRerootCursor fuel := c2

/-- The oriented physical endpoint frame of the double bond `0 = 2`. -/
def topology2 : localizedSource.LocalizedRule3PhysicalEndpointCursorFrame fuel :=
  { left := atom0
    right := atom2
    leftCursor := leftCursor2
    rightCursor := rightCursor2 }

/-- The declarative meaning of `topology2`. -/
theorem topology2_spec :
    localizedSource.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame c2.occurrence topology2 := by
  refine ⟨rfl, rfl, rfl, by decide, carrierParent_c2, rfl, rfl, rfl, rfl⟩

/-- **Physical endpoint recovery at the second carbon.** -/
theorem physical_c2 :
    localizedSource.localizedRule3PhysicalEndpointCursorFrameExec? c2.occurrence =
      some topology2 :=
  localizedSource.localizedRule3PhysicalEndpointCursorFrameExec?_eq_some_of_declarative
    c2.occurrence topology2 topology2_spec

@[simp] theorem leftCursor2_previous : leftCursor2.previous? = some c2.occurrence := rfl
@[simp] theorem leftCursor2_address : leftCursor2.occurrence.1.address = [] := rfl
@[simp] theorem leftCursor2_remaining : leftCursor2.occurrence.1.remaining = fuel + 1 := rfl
@[simp] theorem leftCursor2_current : leftCursor2.occurrence.1.node.current? = some atom0 := rfl
@[simp] theorem leftCursor2_provenance :
    leftCursor2.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom := rfl

@[simp] theorem rightCursor2_previous : rightCursor2.previous? = some root.occurrence := rfl
@[simp] theorem rightCursor2_address : rightCursor2.occurrence.1.address = [2] := rfl
@[simp] theorem rightCursor2_remaining : rightCursor2.occurrence.1.remaining = fuel := rfl
@[simp] theorem rightCursor2_current : rightCursor2.occurrence.1.node.current? = some atom2 := rfl
@[simp] theorem rightCursor2_provenance :
    rightCursor2.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom := rfl

theorem substituents_0_2 :
    localizedSource.localizedRule3ExplicitSubstituents atom0 atom2 = [atom1, atom3] := by
  rw [explicitSubstituents_eq]
  rfl

theorem substituents_2_0 :
    localizedSource.localizedRule3ExplicitSubstituents atom2 atom0 = [atom6, atom7] := by
  rw [explicitSubstituents_eq]
  rfl

/-- The first carbon is an exact executable child of the sulfur endpoint cursor seen from atom
`2`. -/
theorem exists_children_left2_c1 :
    ∃ children, localizedSource.localizedRerootChildren? leftCursor2 = some children ∧
      c1 ∈ children ∧
      localizedSource.DeclarativeLocalizedRerootChildren leftCursor2 children := by
  obtain ⟨children, childCursor, computed, memChild, frameEq⟩ :=
    localizedSource.exists_mem_localizedRerootChildren_of_executable_child
      (cursor := leftCursor2) (nonduplicate := by decide) (positive := by decide)
      (child := node1) (slot := 0)
      (childAtSlot := by
        show (node1, 0) ∈
          (localizedSource.executableOfficialCIPChildren rootNode).zipIdx
        rw [rootChildren_eq]; decide)
      (notIncoming := by
        intro previous h
        rw [leftCursor2_previous] at h
        cases h
        decide)
  have derived := localizedSource.localizedRerootChildren?_sound leftCursor2 children computed
  have cursorEq : childCursor = c1 := by
    apply LocalizedRerootCursor.ext
    · apply Subtype.ext
      rw [frameEq]
      rfl
    · rw [derived.2 childCursor memChild]
      rfl
  exact ⟨children, computed, cursorEq ▸ memChild, derived⟩

/-- The third carbon is an exact executable child of the sulfur endpoint cursor seen from atom
`2`. -/
theorem exists_children_left2_c3 :
    ∃ children, localizedSource.localizedRerootChildren? leftCursor2 = some children ∧
      c3 ∈ children ∧
      localizedSource.DeclarativeLocalizedRerootChildren leftCursor2 children := by
  obtain ⟨children, childCursor, computed, memChild, frameEq⟩ :=
    localizedSource.exists_mem_localizedRerootChildren_of_executable_child
      (cursor := leftCursor2) (nonduplicate := by decide) (positive := by decide)
      (child := node3) (slot := 4)
      (childAtSlot := by
        show (node3, 4) ∈
          (localizedSource.executableOfficialCIPChildren rootNode).zipIdx
        rw [rootChildren_eq]; decide)
      (notIncoming := by
        intro previous h
        rw [leftCursor2_previous] at h
        cases h
        decide)
  have derived := localizedSource.localizedRerootChildren?_sound leftCursor2 children computed
  have cursorEq : childCursor = c3 := by
    apply LocalizedRerootCursor.ext
    · apply Subtype.ext
      rw [frameEq]
      rfl
    · rw [derived.2 childCursor memChild]
      rfl
  exact ⟨children, computed, cursorEq ▸ memChild, derived⟩

theorem refExec_left2_c1 :
    localizedSource.localizedRule3ReferenceCursorExec? leftCursor2 atom1 = some c1 := by
  have declarative : localizedSource.DeclarativeLocalizedRule3ReferenceCursor
      leftCursor2 c1 atom1 := by
    obtain ⟨children, computed, mem, derived⟩ := exists_children_left2_c1
    exact ⟨children, computed, derived, mem, rfl, trivial, rfl⟩
  rw [← localizedSource.localizedRule3ReferenceCursor?_eq_localizedRule3ReferenceCursorExec?]
  exact localizedSource.localizedRule3ReferenceCursor?_eq_some_of_declarative
    leftCursor2 c1 atom1 declarative

theorem refExec_left2_c3 :
    localizedSource.localizedRule3ReferenceCursorExec? leftCursor2 atom3 = some c3 := by
  have declarative : localizedSource.DeclarativeLocalizedRule3ReferenceCursor
      leftCursor2 c3 atom3 := by
    obtain ⟨children, computed, mem, derived⟩ := exists_children_left2_c3
    exact ⟨children, computed, derived, mem, rfl, trivial, rfl⟩
  rw [← localizedSource.localizedRule3ReferenceCursor?_eq_localizedRule3ReferenceCursorExec?]
  exact localizedSource.localizedRule3ReferenceCursor?_eq_some_of_declarative
    leftCursor2 c3 atom3 declarative

/-! ### The hydrogen children of the second carbon -/

def h6Frame : localizedSource.LocalizedCIPOccurrenceFrame :=
  { root := atom0, address := [2, 1], node := c2NodeH6, remaining := fuel - 1 }

def h7Frame : localizedSource.LocalizedCIPOccurrenceFrame :=
  { root := atom0, address := [2, 2], node := c2NodeH7, remaining := fuel - 1 }

theorem h6Frame_mem : h6Frame ∈ localizedSource.localizedOccurrences fuel := by
  rw [localizedSource.mem_localizedOccurrences_iff]
  exact DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (path := []) (fuel := fuel) (node := rootNode) (child := node2) (slot := 2)
    (occurrence := h6Frame)
    (by rw [rootChildren_eq]; decide)
    (DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (path := [2]) (fuel := fuel - 1) (node := node2) (child := c2NodeH6) (slot := 1)
      (occurrence := h6Frame)
      (by
        show (c2NodeH6, 1) ∈
          (localizedSource.executableOfficialCIPChildren node2).zipIdx
        rw [c2Children_eq]; decide)
      (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot [2, 1] (fuel - 1) c2NodeH6))

theorem h7Frame_mem : h7Frame ∈ localizedSource.localizedOccurrences fuel := by
  rw [localizedSource.mem_localizedOccurrences_iff]
  exact DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (path := []) (fuel := fuel) (node := rootNode) (child := node2) (slot := 2)
    (occurrence := h7Frame)
    (by rw [rootChildren_eq]; decide)
    (DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (path := [2]) (fuel := fuel - 1) (node := node2) (child := c2NodeH7) (slot := 2)
      (occurrence := h7Frame)
      (by
        show (c2NodeH7, 2) ∈
          (localizedSource.executableOfficialCIPChildren node2).zipIdx
        rw [c2Children_eq]; decide)
      (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot [2, 2] (fuel - 1) c2NodeH7))

def h6 : localizedSource.LocalizedRerootCursor fuel :=
  { occurrence := ⟨h6Frame, h6Frame_mem⟩, previous? := some rightCursor2.occurrence }

def h7 : localizedSource.LocalizedRerootCursor fuel :=
  { occurrence := ⟨h7Frame, h7Frame_mem⟩, previous? := some rightCursor2.occurrence }

@[simp] theorem h6_previous : h6.previous? = some rightCursor2.occurrence := rfl
@[simp] theorem h7_previous : h7.previous? = some rightCursor2.occurrence := rfl
@[simp] theorem h6_current : h6.occurrence.1.node.current? = some atom6 := rfl
@[simp] theorem h7_current : h7.occurrence.1.node.current? = some atom7 := rfl

theorem h6_provenance :
    h6.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom := by
  decide

theorem h7_provenance :
    h7.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom := by
  decide

theorem exists_children_h6 :
    ∃ children, localizedSource.localizedRerootChildren? rightCursor2 = some children ∧
      h6 ∈ children ∧
      localizedSource.DeclarativeLocalizedRerootChildren rightCursor2 children := by
  obtain ⟨children, childCursor, computed, memChild, frameEq⟩ :=
    localizedSource.exists_mem_localizedRerootChildren_of_executable_child
      (cursor := rightCursor2) (nonduplicate := by decide) (positive := by decide)
      (child := c2NodeH6) (slot := 1)
      (childAtSlot := by
        show (c2NodeH6, 1) ∈
          (localizedSource.executableOfficialCIPChildren node2).zipIdx
        rw [c2Children_eq]; decide)
      (notIncoming := by
        intro previous h
        rw [rightCursor2_previous] at h
        cases h
        decide)
  have derived := localizedSource.localizedRerootChildren?_sound rightCursor2 children computed
  have cursorEq : childCursor = h6 := by
    apply LocalizedRerootCursor.ext
    · apply Subtype.ext
      rw [frameEq]
      rfl
    · rw [derived.2 childCursor memChild]
      rfl
  exact ⟨children, computed, cursorEq ▸ memChild, derived⟩

theorem exists_children_h7 :
    ∃ children, localizedSource.localizedRerootChildren? rightCursor2 = some children ∧
      h7 ∈ children ∧
      localizedSource.DeclarativeLocalizedRerootChildren rightCursor2 children := by
  obtain ⟨children, childCursor, computed, memChild, frameEq⟩ :=
    localizedSource.exists_mem_localizedRerootChildren_of_executable_child
      (cursor := rightCursor2) (nonduplicate := by decide) (positive := by decide)
      (child := c2NodeH7) (slot := 2)
      (childAtSlot := by
        show (c2NodeH7, 2) ∈
          (localizedSource.executableOfficialCIPChildren node2).zipIdx
        rw [c2Children_eq]; decide)
      (notIncoming := by
        intro previous h
        rw [rightCursor2_previous] at h
        cases h
        decide)
  have derived := localizedSource.localizedRerootChildren?_sound rightCursor2 children computed
  have cursorEq : childCursor = h7 := by
    apply LocalizedRerootCursor.ext
    · apply Subtype.ext
      rw [frameEq]
      rfl
    · rw [derived.2 childCursor memChild]
      rfl
  exact ⟨children, computed, cursorEq ▸ memChild, derived⟩

theorem refExec_h6 :
    localizedSource.localizedRule3ReferenceCursorExec? rightCursor2 atom6 = some h6 := by
  have declarative : localizedSource.DeclarativeLocalizedRule3ReferenceCursor
      rightCursor2 h6 atom6 := by
    obtain ⟨children, computed, mem, derived⟩ := exists_children_h6
    exact ⟨children, computed, derived, mem, rfl, trivial, rfl⟩
  rw [← localizedSource.localizedRule3ReferenceCursor?_eq_localizedRule3ReferenceCursorExec?]
  exact localizedSource.localizedRule3ReferenceCursor?_eq_some_of_declarative
    rightCursor2 h6 atom6 declarative

theorem refExec_h7 :
    localizedSource.localizedRule3ReferenceCursorExec? rightCursor2 atom7 = some h7 := by
  have declarative : localizedSource.DeclarativeLocalizedRule3ReferenceCursor
      rightCursor2 h7 atom7 := by
    obtain ⟨children, computed, mem, derived⟩ := exists_children_h7
    exact ⟨children, computed, derived, mem, rfl, trivial, rfl⟩
  rw [← localizedSource.localizedRule3ReferenceCursor?_eq_localizedRule3ReferenceCursorExec?]
  exact localizedSource.localizedRule3ReferenceCursor?_eq_some_of_declarative
    rightCursor2 h7 atom7 declarative

theorem pairReady_left2 :
    localizedSource.rule3EndpointPairReady topology2.left topology2.right
      topology2.leftCursor = true := by
  simp only [rule3EndpointPairReady, topology2, substituents_0_2, refExec_left2_c1,
    refExec_left2_c3, Option.isSome_some]
  rfl

theorem pairReady_right2 :
    localizedSource.rule3EndpointPairReady topology2.right topology2.left
      topology2.rightCursor = true := by
  simp only [rule3EndpointPairReady, topology2, substituents_2_0, refExec_h6, refExec_h7,
    Option.isSome_some]
  rfl

/-- **Readiness of the second carbon endpoint.** -/
theorem ordinaryPairReady_c2 :
    localizedSource.ordinaryPairReady c2.occurrence = true := by
  simp only [ordinaryPairReady, physical_c2, topology2, rule3EndpointPairReady,
    substituents_0_2, substituents_2_0, refExec_left2_c1, refExec_left2_c3, refExec_h6,
    refExec_h7, Option.isSome_some]
  rfl

/-- The second carbon is a real node on an order-two bond. -/
theorem edge_c2 :
    localizedSource.LocalizedOccurrenceHasRule3DoubleBondEdge c2.occurrence := by
  refine ⟨rfl, atom2, atom0, rfl, rfl, ?_⟩
  decide

theorem c1_mem_executableChildren2 :
    c1 ∈ localizedSource.executableLocalizedRerootChildren leftCursor2 := by
  obtain ⟨children, computed, mem, _derived⟩ := exists_children_left2_c1
  have executableEq := localizedSource.localizedRerootChildren?_eq_some_executable leftCursor2
  have childrenEq : children = localizedSource.executableLocalizedRerootChildren leftCursor2 :=
    (Option.some.injEq _ _).mp (computed.symm.trans executableEq)
  rwa [childrenEq] at mem

theorem c3_mem_executableChildren2 :
    c3 ∈ localizedSource.executableLocalizedRerootChildren leftCursor2 := by
  obtain ⟨children, computed, mem, _derived⟩ := exists_children_left2_c3
  have executableEq := localizedSource.localizedRerootChildren?_eq_some_executable leftCursor2
  have childrenEq : children = localizedSource.executableLocalizedRerootChildren leftCursor2 :=
    (Option.some.injEq _ _).mp (computed.symm.trans executableEq)
  rwa [childrenEq] at mem

theorem axisContinuation_left2_c1 :
    localizedSource.LocalizedRule3AxisPhysicalContinuation leftCursor2 c1 := by
  refine ⟨leftCursor2_provenance, ?_, ?_⟩
  · decide
  · show localizedSource.moleculeGraph.bond atom0 atom1 = 2
    decide

theorem axisContinuation_left2_c3 :
    localizedSource.LocalizedRule3AxisPhysicalContinuation leftCursor2 c3 := by
  refine ⟨leftCursor2_provenance, ?_, ?_⟩
  · decide
  · show localizedSource.moleculeGraph.bond atom0 atom3 = 2
    decide

theorem c1_ne_c3 : c1 ≠ c3 := by
  intro equally
  have addresses := congrArg (fun cursor => cursor.occurrence.1.address) equally
  simp only at addresses
  rw [c1_address, c3_address] at addresses
  exact absurd addresses (by decide)

theorem axisContinuations_left2_two_le :
    2 ≤ (localizedSource.localizedRule3AxisPhysicalContinuationCursorsExec leftCursor2
      (localizedSource.executableLocalizedRerootChildren leftCursor2)).length := by
  apply two_le_length_of_mem_of_mem (first := c1) (second := c3)
  · simp only [localizedRule3AxisPhysicalContinuationCursorsExec, List.mem_filter]
    exact ⟨c1_mem_executableChildren2, decide_eq_true axisContinuation_left2_c1⟩
  · simp only [localizedRule3AxisPhysicalContinuationCursorsExec, List.mem_filter]
    exact ⟨c3_mem_executableChildren2, decide_eq_true axisContinuation_left2_c3⟩
  · exact c1_ne_c3

theorem axisTopology_left2_branched :
    ∃ first second rest,
      localizedSource.localizedRule3AxisTopologyExec? leftCursor2 =
        some (.branched first second rest) := by
  have long : 2 ≤ ((localizedSource.executableLocalizedRerootChildren leftCursor2).filter
      (fun child => decide (localizedSource.LocalizedRule3AxisPhysicalContinuation
        leftCursor2 child))).length := axisContinuations_left2_two_le
  obtain ⟨first, second, rest, shape⟩ := exists_two_cons_of_two_le_length long
  refine ⟨first, second, rest, ?_⟩
  have expanded :
      localizedSource.localizedRule3AxisPhysicalContinuationCursorsExec? leftCursor2 =
        some ((localizedSource.executableLocalizedRerootChildren leftCursor2).filter
          (fun child => decide (localizedSource.LocalizedRule3AxisPhysicalContinuation
            leftCursor2 child))) := by
    unfold localizedRule3AxisPhysicalContinuationCursorsExec?
      localizedRule3AxisPhysicalContinuationCursorsExec
    rw [executableLocalizedRerootChildren?_eq_some]
    rfl
  unfold localizedRule3AxisTopologyExec?
  rw [expanded, shape]
  rfl

theorem axisEntry_c2_branched :
    ∃ initial first second rest,
      localizedSource.localizedRule3CumulatedAxisEntryExec? c2.occurrence =
        some (.branched initial first second rest) := by
  obtain ⟨first, second, rest, topology⟩ := axisTopology_left2_branched
  refine ⟨topology2, first, second, rest, ?_⟩
  simp [localizedRule3CumulatedAxisEntryExec?, physical_c2, topology2, topology]

theorem oddRoute_c2_eq_none :
    localizedSource.localizedRule3OddRouteCertificate? c2.occurrence = none := by
  obtain ⟨initial, first, second, rest, entry⟩ := axisEntry_c2_branched
  simp only [localizedRule3OddRouteCertificate?]
  rw [dif_pos edge_c2]
  rw [entry]

theorem ordinaryRoute_c2_some :
    ∃ certificate,
      localizedSource.localizedRule3OrdinaryRouteCertificate? c2.occurrence = some certificate := by
  obtain ⟨initial, first, second, rest, entry⟩ := axisEntry_c2_branched
  unfold localizedRule3OrdinaryRouteCertificate?
  rw [dif_pos edge_c2]
  split
  next initial' first' second' rest' entryEq =>
    exact ⟨_, rfl⟩
  next initial' entryEq =>
    rw [entry] at entryEq
    simp at entryEq
  next notBranched notTerminal =>
    exact absurd entry (notBranched initial first second rest)

theorem requests_c2_eq :
    localizedSource.rule3PreflightExtendedNodeCallbackRequests c2.occurrence =
      localizedSource.rule3ShortSpatialCallbackRequests c2.occurrence := by
  obtain ⟨certificate, ordinary⟩ := ordinaryRoute_c2_some
  simp only [rule3PreflightExtendedNodeCallbackRequests, oddRoute_c2_eq_none, ordinary]
  exact localizedSource.rule3PreflightShortSpatialCallbackRequests_eq_of_ready
    c2.occurrence ordinaryPairReady_c2

theorem shortSpatial_c2_eq :
    localizedSource.rule3ShortSpatialCallbackRequests c2.occurrence =
      localizedSource.rule3ShortEndpointCallbackRequests atom0 atom2 leftCursor2 ++
        localizedSource.rule3ShortEndpointCallbackRequests atom2 atom0 rightCursor2 := by
  simp only [rule3ShortSpatialCallbackRequests, physical_c2, topology2]

theorem rootCompare_c1_c3 :
    localizedSource.compareLocalizedRerootCursorConstitutionalRoot c1 c3 = .eq := by
  decide

/-- The left endpoint request at the second carbon is `[[c1, c3]]`, conditional on the
constitutional tie of the two remaining carbon substituents. -/
theorem endpointRequests_0_2_eq_of_tie
    (tie : localizedSource.compareLocalizedConstitutionalCursors? c1 c3 = some .eq) :
    localizedSource.rule3ShortEndpointCallbackRequests atom0 atom2 leftCursor2 = [[c1, c3]] := by
  simp only [rule3ShortEndpointCallbackRequests, substituents_0_2, refExec_left2_c1,
    refExec_left2_c3, rootCompare_c1_c3, tie]

/-- The first carbon is demanded at the second carbon, conditional only on the carbon--carbon
constitutional tie. -/
theorem c1_mem_requests_c2_of_tie
    (tie : localizedSource.compareLocalizedConstitutionalCursors? c1 c3 = some .eq) :
    c1 ∈ (localizedSource.rule3PreflightExtendedNodeCallbackRequests c2.occurrence).flatten := by
  rw [requests_c2_eq, shortSpatial_c2_eq, endpointRequests_0_2_eq_of_tie tie]
  simp

/-! ## The explicit terminal children of the three carbon cursors

Every carbon cursor expands to one multiple-bond duplicate of the sulfur parent and its two
hydrogens.  These nine cursors are the exact reference frames used at the corresponding endpoints.
The duplicate leaves carry the sulfur atomic number with zero Rule-2 mass and distance one; the
hydrogen leaves carry the hydrogen label and distance two.  All nine are terminal.
-/

def sDup1Frame : localizedSource.LocalizedCIPOccurrenceFrame :=
  { root := atom0, address := [0, 0], node := c1Node0, remaining := fuel - 1 }

def sDup2Frame : localizedSource.LocalizedCIPOccurrenceFrame :=
  { root := atom0, address := [2, 0], node := c2Node0, remaining := fuel - 1 }

def sDup3Frame : localizedSource.LocalizedCIPOccurrenceFrame :=
  { root := atom0, address := [4, 0], node := c3Node0, remaining := fuel - 1 }

def h8Frame : localizedSource.LocalizedCIPOccurrenceFrame :=
  { root := atom0, address := [4, 1], node := c3NodeH8, remaining := fuel - 1 }

def h9Frame : localizedSource.LocalizedCIPOccurrenceFrame :=
  { root := atom0, address := [4, 2], node := c3NodeH9, remaining := fuel - 1 }

theorem sDup1Frame_mem : sDup1Frame ∈ localizedSource.localizedOccurrences fuel := by
  rw [localizedSource.mem_localizedOccurrences_iff]
  exact DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (path := []) (fuel := fuel) (node := rootNode) (child := node1) (slot := 0)
    (occurrence := sDup1Frame)
    (by rw [rootChildren_eq]; decide)
    (DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (path := [0]) (fuel := fuel - 1) (node := node1) (child := c1Node0) (slot := 0)
      (occurrence := sDup1Frame)
      (by
        show (c1Node0, 0) ∈
          (localizedSource.executableOfficialCIPChildren node1).zipIdx
        rw [c1Children_eq]; decide)
      (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot [0, 0] (fuel - 1) c1Node0))

theorem sDup2Frame_mem : sDup2Frame ∈ localizedSource.localizedOccurrences fuel := by
  rw [localizedSource.mem_localizedOccurrences_iff]
  exact DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (path := []) (fuel := fuel) (node := rootNode) (child := node2) (slot := 2)
    (occurrence := sDup2Frame)
    (by rw [rootChildren_eq]; decide)
    (DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (path := [2]) (fuel := fuel - 1) (node := node2) (child := c2Node0) (slot := 0)
      (occurrence := sDup2Frame)
      (by
        show (c2Node0, 0) ∈
          (localizedSource.executableOfficialCIPChildren node2).zipIdx
        rw [c2Children_eq]; decide)
      (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot [2, 0] (fuel - 1) c2Node0))

theorem sDup3Frame_mem : sDup3Frame ∈ localizedSource.localizedOccurrences fuel := by
  rw [localizedSource.mem_localizedOccurrences_iff]
  exact DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (path := []) (fuel := fuel) (node := rootNode) (child := node3) (slot := 4)
    (occurrence := sDup3Frame)
    (by rw [rootChildren_eq]; decide)
    (DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (path := [4]) (fuel := fuel - 1) (node := node3) (child := c3Node0) (slot := 0)
      (occurrence := sDup3Frame)
      (by
        show (c3Node0, 0) ∈
          (localizedSource.executableOfficialCIPChildren node3).zipIdx
        rw [c3Children_eq]; decide)
      (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot [4, 0] (fuel - 1) c3Node0))

theorem h8Frame_mem : h8Frame ∈ localizedSource.localizedOccurrences fuel := by
  rw [localizedSource.mem_localizedOccurrences_iff]
  exact DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (path := []) (fuel := fuel) (node := rootNode) (child := node3) (slot := 4)
    (occurrence := h8Frame)
    (by rw [rootChildren_eq]; decide)
    (DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (path := [4]) (fuel := fuel - 1) (node := node3) (child := c3NodeH8) (slot := 1)
      (occurrence := h8Frame)
      (by
        show (c3NodeH8, 1) ∈
          (localizedSource.executableOfficialCIPChildren node3).zipIdx
        rw [c3Children_eq]; decide)
      (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot [4, 1] (fuel - 1) c3NodeH8))

theorem h9Frame_mem : h9Frame ∈ localizedSource.localizedOccurrences fuel := by
  rw [localizedSource.mem_localizedOccurrences_iff]
  exact DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (path := []) (fuel := fuel) (node := rootNode) (child := node3) (slot := 4)
    (occurrence := h9Frame)
    (by rw [rootChildren_eq]; decide)
    (DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (path := [4]) (fuel := fuel - 1) (node := node3) (child := c3NodeH9) (slot := 2)
      (occurrence := h9Frame)
      (by
        show (c3NodeH9, 2) ∈
          (localizedSource.executableOfficialCIPChildren node3).zipIdx
        rw [c3Children_eq]; decide)
      (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot [4, 2] (fuel - 1) c3NodeH9))

def sDup1 : localizedSource.LocalizedRerootCursor fuel :=
  { occurrence := ⟨sDup1Frame, sDup1Frame_mem⟩, previous? := some c1.occurrence }

def sDup2 : localizedSource.LocalizedRerootCursor fuel :=
  { occurrence := ⟨sDup2Frame, sDup2Frame_mem⟩, previous? := some c2.occurrence }

def sDup3 : localizedSource.LocalizedRerootCursor fuel :=
  { occurrence := ⟨sDup3Frame, sDup3Frame_mem⟩, previous? := some c3.occurrence }

def h8 : localizedSource.LocalizedRerootCursor fuel :=
  { occurrence := ⟨h8Frame, h8Frame_mem⟩, previous? := some c3.occurrence }

def h9 : localizedSource.LocalizedRerootCursor fuel :=
  { occurrence := ⟨h9Frame, h9Frame_mem⟩, previous? := some c3.occurrence }

@[simp] theorem sDup1_previous : sDup1.previous? = some c1.occurrence := rfl
@[simp] theorem sDup2_previous : sDup2.previous? = some c2.occurrence := rfl
@[simp] theorem sDup3_previous : sDup3.previous? = some c3.occurrence := rfl
@[simp] theorem h8_previous : h8.previous? = some c3.occurrence := rfl
@[simp] theorem h9_previous : h9.previous? = some c3.occurrence := rfl

theorem sDup1_current : sDup1.occurrence.1.node.current? = some atom0 := rfl
theorem sDup2_current : sDup2.occurrence.1.node.current? = some atom0 := rfl
theorem sDup3_current : sDup3.occurrence.1.node.current? = some atom0 := rfl
theorem h8_current : h8.occurrence.1.node.current? = some atom8 := rfl
theorem h9_current : h9.occurrence.1.node.current? = some atom9 := rfl

theorem h8_provenance :
    h8.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom := by
  decide

theorem h9_provenance :
    h9.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom := by
  decide

/-! ### Duplicate leaves are terminal -/

/-- A duplicate node forces the intended child frame to be empty, hence the executable children
are empty at every carrier fuel. -/
theorem executableChildren_nil_of_duplicate
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (duplicate : cursor.occurrence.1.node.isDuplicateLeaf = true) :
    input.executableLocalizedRerootChildren cursor = [] := by
  unfold executableLocalizedRerootChildren
  have intended : input.intendedLocalizedRerootChildFrames cursor = [] := by
    unfold intendedLocalizedRerootChildFrames
    rw [if_pos duplicate]
  have attached : (input.intendedLocalizedRerootChildFrames cursor).attach = [] := by
    rw [intended]
    rfl
  rw [attached]
  rfl

theorem sDup1_children_nil :
    localizedSource.executableLocalizedRerootChildren sDup1 = [] :=
  executableChildren_nil_of_duplicate localizedSource sDup1 (by decide)

theorem sDup2_children_nil :
    localizedSource.executableLocalizedRerootChildren sDup2 = [] :=
  executableChildren_nil_of_duplicate localizedSource sDup2 (by decide)

theorem sDup3_children_nil :
    localizedSource.executableLocalizedRerootChildren sDup3 = [] :=
  executableChildren_nil_of_duplicate localizedSource sDup3 (by decide)

/-! ### Real hydrogen leaves are terminal -/

/-- A non-duplicate node with no official children has no intended children, provided the incoming
coordinate is its carrier parent (so every parent frame is cut) and the frame's address is one
official slot below the parent.  Outward children would be immediate official children, of which
there are none. -/
theorem executableChildren_nil_of_officialChildren_nil
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

theorem h4_children_nil :
    localizedSource.executableLocalizedRerootChildren h4 = [] := by
  apply executableChildren_nil_of_officialChildren_nil localizedSource rightCursor1 h4
    (incoming := rfl) (slot := 1) (address := rfl) (nonduplicate := by decide)
  unfold executableOfficialCIPChildren
  simp only [executableOfficialChildCopies, executableOfficialNeighborCopies,
    neighborSort_eq, c1NodeH4, node1, atom4, atom1]
  decide

theorem h5_children_nil :
    localizedSource.executableLocalizedRerootChildren h5 = [] := by
  apply executableChildren_nil_of_officialChildren_nil localizedSource rightCursor1 h5
    (incoming := rfl) (slot := 2) (address := rfl) (nonduplicate := by decide)
  unfold executableOfficialCIPChildren
  simp only [executableOfficialChildCopies, executableOfficialNeighborCopies,
    neighborSort_eq, c1NodeH5, node1, atom5, atom1]
  decide

theorem h6_children_nil :
    localizedSource.executableLocalizedRerootChildren h6 = [] := by
  apply executableChildren_nil_of_officialChildren_nil localizedSource rightCursor2 h6
    (incoming := rfl) (slot := 1) (address := rfl) (nonduplicate := by decide)
  unfold executableOfficialCIPChildren
  simp only [executableOfficialChildCopies, executableOfficialNeighborCopies,
    neighborSort_eq, c2NodeH6, node2, atom6, atom2]
  decide

theorem h7_children_nil :
    localizedSource.executableLocalizedRerootChildren h7 = [] := by
  apply executableChildren_nil_of_officialChildren_nil localizedSource rightCursor2 h7
    (incoming := rfl) (slot := 2) (address := rfl) (nonduplicate := by decide)
  unfold executableOfficialCIPChildren
  simp only [executableOfficialChildCopies, executableOfficialNeighborCopies,
    neighborSort_eq, c2NodeH7, node2, atom7, atom2]
  decide

theorem h8_children_nil :
    localizedSource.executableLocalizedRerootChildren h8 = [] := by
  apply executableChildren_nil_of_officialChildren_nil localizedSource c3 h8
    (incoming := rfl) (slot := 1) (address := rfl) (nonduplicate := by decide)
  unfold executableOfficialCIPChildren
  simp only [executableOfficialChildCopies, executableOfficialNeighborCopies,
    neighborSort_eq, c3NodeH8, node3, atom8, atom3]
  decide

theorem h9_children_nil :
    localizedSource.executableLocalizedRerootChildren h9 = [] := by
  apply executableChildren_nil_of_officialChildren_nil localizedSource c3 h9
    (incoming := rfl) (slot := 2) (address := rfl) (nonduplicate := by decide)
  unfold executableOfficialCIPChildren
  simp only [executableOfficialChildCopies, executableOfficialNeighborCopies,
    neighborSort_eq, c3NodeH9, node3, atom9, atom3]
  decide

/-- **Exact carbon expansion up to order.**  If a cursor is a real, nonterminal, positive-depth
frame at address `[slotC]` whose parent address is empty, and its official child list is
`[d, a, b]`, then its executable reroot children are a permutation of the three explicit cursors
whose frames are the official children in slots `0, 1, 2`.  This is the local replacement for a
global carrier enumeration. -/
theorem executableChildren_perm_explicit
    (C P : localizedSource.LocalizedRerootCursor fuel)
    (prev : C.previous? = some P.occurrence)
    (pAddr : P.occurrence.1.address = [])
    (slotC : Nat)
    (cAddr : C.occurrence.1.address = [slotC])
    (nondup : C.occurrence.1.node.isDuplicateLeaf = false)
    (positive : 0 < C.occurrence.1.remaining)
    (d a b : OfficialCIPNode localizedSource.Atom)
    (childrenEq : localizedSource.executableOfficialCIPChildren C.occurrence.1.node = [d, a, b])
    (Cd Ca Cb : localizedSource.LocalizedRerootCursor fuel)
    (CdOcc : Cd.occurrence.1 =
      { root := C.occurrence.1.root
        address := C.occurrence.1.address ++ [0]
        node := d
        remaining := C.occurrence.1.remaining - 1 })
    (CaOcc : Ca.occurrence.1 =
      { root := C.occurrence.1.root
        address := C.occurrence.1.address ++ [1]
        node := a
        remaining := C.occurrence.1.remaining - 1 })
    (CbOcc : Cb.occurrence.1 =
      { root := C.occurrence.1.root
        address := C.occurrence.1.address ++ [2]
        node := b
        remaining := C.occurrence.1.remaining - 1 })
    (CdPrev : Cd.previous? = some C.occurrence)
    (CaPrev : Ca.previous? = some C.occurrence)
    (CbPrev : Cb.previous? = some C.occurrence) :
    (localizedSource.executableLocalizedRerootChildren C).Perm [Cd, Ca, Cb] := by
  have actualNodup := localizedSource.executableLocalizedRerootChildren_nodup C
  have h01 : Cd ≠ Ca := by
    intro same
    have addresses := congrArg (fun child => child.occurrence.1.address) same
    dsimp only at addresses
    rw [CdOcc, CaOcc] at addresses
    have rest : ([0] : List Nat) = [1] := by simpa using addresses
    exact absurd rest (by decide)
  have h02 : Cd ≠ Cb := by
    intro same
    have addresses := congrArg (fun child => child.occurrence.1.address) same
    dsimp only at addresses
    rw [CdOcc, CbOcc] at addresses
    have rest : ([0] : List Nat) = [2] := by simpa using addresses
    exact absurd rest (by decide)
  have h12 : Ca ≠ Cb := by
    intro same
    have addresses := congrArg (fun child => child.occurrence.1.address) same
    dsimp only at addresses
    rw [CaOcc, CbOcc] at addresses
    have rest : ([1] : List Nat) = [2] := by simpa using addresses
    exact absurd rest (by decide)
  have explicitNodup : [Cd, Ca, Cb].Nodup := by
    rw [List.nodup_cons]
    refine ⟨by simp [h01, h02], ?_⟩
    rw [List.nodup_cons]
    exact ⟨by simp [h12], by simp⟩
  have memCd : Cd ∈ localizedSource.executableLocalizedRerootChildren C := by
    obtain ⟨children, childCursor, computed, childMem, frameResult⟩ :=
      localizedSource.exists_mem_localizedRerootChildren_of_executable_child
        (cursor := C) (nonduplicate := nondup) (positive := positive)
        (child := d) (slot := 0)
        (childAtSlot := by
          rw [childrenEq]
          show (d, 0) ∈ [(d, 0), (a, 1), (b, 2)]
          simp)
        (notIncoming := by
          intro previous obtained
          rw [prev] at obtained
          cases obtained
          rw [pAddr, cAddr]
          simp)
    have derived := localizedSource.localizedRerootChildren?_sound C children computed
    have executableEq : children =
        localizedSource.executableLocalizedRerootChildren C :=
      Option.some.inj (computed.symm.trans
        (localizedSource.localizedRerootChildren?_eq_some_executable C))
    have cursorEq : childCursor = Cd := by
      apply LocalizedRerootCursor.ext
      · apply Subtype.ext
        rw [frameResult, CdOcc]
      · rw [derived.2 childCursor childMem, CdPrev]
    rw [← executableEq, ← cursorEq]
    exact childMem
  have memCa : Ca ∈ localizedSource.executableLocalizedRerootChildren C := by
    obtain ⟨children, childCursor, computed, childMem, frameResult⟩ :=
      localizedSource.exists_mem_localizedRerootChildren_of_executable_child
        (cursor := C) (nonduplicate := nondup) (positive := positive)
        (child := a) (slot := 1)
        (childAtSlot := by
          rw [childrenEq]
          show (a, 1) ∈ [(d, 0), (a, 1), (b, 2)]
          simp)
        (notIncoming := by
          intro previous obtained
          rw [prev] at obtained
          cases obtained
          rw [pAddr, cAddr]
          simp)
    have derived := localizedSource.localizedRerootChildren?_sound C children computed
    have executableEq : children =
        localizedSource.executableLocalizedRerootChildren C :=
      Option.some.inj (computed.symm.trans
        (localizedSource.localizedRerootChildren?_eq_some_executable C))
    have cursorEq : childCursor = Ca := by
      apply LocalizedRerootCursor.ext
      · apply Subtype.ext
        rw [frameResult, CaOcc]
      · rw [derived.2 childCursor childMem, CaPrev]
    rw [← executableEq, ← cursorEq]
    exact childMem
  have memCb : Cb ∈ localizedSource.executableLocalizedRerootChildren C := by
    obtain ⟨children, childCursor, computed, childMem, frameResult⟩ :=
      localizedSource.exists_mem_localizedRerootChildren_of_executable_child
        (cursor := C) (nonduplicate := nondup) (positive := positive)
        (child := b) (slot := 2)
        (childAtSlot := by
          rw [childrenEq]
          show (b, 2) ∈ [(d, 0), (a, 1), (b, 2)]
          simp)
        (notIncoming := by
          intro previous obtained
          rw [prev] at obtained
          cases obtained
          rw [pAddr, cAddr]
          simp)
    have derived := localizedSource.localizedRerootChildren?_sound C children computed
    have executableEq : children =
        localizedSource.executableLocalizedRerootChildren C :=
      Option.some.inj (computed.symm.trans
        (localizedSource.localizedRerootChildren?_eq_some_executable C))
    have cursorEq : childCursor = Cb := by
      apply LocalizedRerootCursor.ext
      · apply Subtype.ext
        rw [frameResult, CbOcc]
      · rw [derived.2 childCursor childMem, CbPrev]
    rw [← executableEq, ← cursorEq]
    exact childMem
  have sameMembers : ∀ child : localizedSource.LocalizedRerootCursor fuel,
      child ∈ localizedSource.executableLocalizedRerootChildren C ↔
        child ∈ [Cd, Ca, Cb] := by
    intro child
    constructor
    · intro childPresent
      have intendedPresent :
          child.occurrence.1 ∈ localizedSource.intendedLocalizedRerootChildFrames C := by
        have declarative := localizedSource.executableLocalizedRerootChildren_declarative C
        rw [← declarative.1]
        exact List.mem_map.mpr ⟨child, childPresent, rfl⟩
      unfold intendedLocalizedRerootChildFrames at intendedPresent
      rw [if_neg (by simpa using nondup)] at intendedPresent
      rw [prev] at intendedPresent
      rw [List.mem_filter] at intendedPresent
      obtain ⟨neighbor, addressDifferent⟩ := intendedPresent
      have addressNonempty : child.occurrence.1.address ≠ [] := by
        intro empty
        simp [empty, pAddr] at addressDifferent
      rw [localizedRerootNeighborFrames, List.mem_append] at neighbor
      rcases neighbor with parent | outward
      · rw [localizedCarrierParentFrames, List.mem_filter] at parent
        obtain ⟨_, conditions⟩ := parent
        simp only [Bool.and_eq_true, beq_iff_eq] at conditions
        have parentAddress : child.occurrence.1.address = [] := by
          rw [conditions.2, cAddr]
          rfl
        exact absurd parentAddress addressNonempty
      · rw [localizedCarrierOutwardChildFrames, List.mem_filter] at outward
        obtain ⟨_, conditions⟩ := outward
        simp only [Bool.and_eq_true, beq_iff_eq] at conditions
        have childDerived :
            localizedSource.DeclarativeLocalizedOccurrence fuel child.occurrence.1 :=
          (localizedSource.mem_localizedOccurrences_iff fuel child.occurrence.1).mp
            child.occurrence.2
        have sourceDerived :
            localizedSource.DeclarativeLocalizedOccurrence fuel C.occurrence.1 :=
          (localizedSource.mem_localizedOccurrences_iff fuel C.occurrence.1).mp
            C.occurrence.2
        generalize slotEq :
          child.occurrence.1.address.getLast addressNonempty = slot
        have decomp : child.occurrence.1.address =
            child.occurrence.1.address.dropLast ++ [slot] := by
          rw [← slotEq]
          exact (List.dropLast_concat_getLast addressNonempty).symm
        have childAddress : child.occurrence.1.address =
            C.occurrence.1.address ++ [slot] := by
          calc
            child.occurrence.1.address =
                child.occurrence.1.address.dropLast ++ [slot] := decomp
            _ = C.occurrence.1.address ++ [slot] := by
              rw [conditions.2]
        obtain ⟨node, nodeAtSlot, frameResult⟩ :=
          localizedSource.declarativeLocalizedOccurrence_immediate_child
            sourceDerived childDerived conditions.1.1 slot childAddress
        rw [childrenEq] at nodeAtSlot
        have slotLt : slot < 3 := by
          have bounded := List.snd_lt_of_mem_zipIdx nodeAtSlot
          simpa using bounded
        interval_cases slot
        · have nodeEq : node = d := by simpa using nodeAtSlot
          have frameAt : child.occurrence.1 =
              { root := C.occurrence.1.root
                address := C.occurrence.1.address ++ [0]
                node := d
                remaining := C.occurrence.1.remaining - 1 } := by
            rw [frameResult, nodeEq]
          have cursorEq : child = Cd := by
            apply LocalizedRerootCursor.ext
            · apply Subtype.ext
              rw [frameAt, CdOcc]
            · rw [localizedSource.executableLocalizedRerootChildren_previous
                C child childPresent, CdPrev]
          rw [cursorEq]
          simp
        · have nodeEq : node = a := by simpa using nodeAtSlot
          have frameAt : child.occurrence.1 =
              { root := C.occurrence.1.root
                address := C.occurrence.1.address ++ [1]
                node := a
                remaining := C.occurrence.1.remaining - 1 } := by
            rw [frameResult, nodeEq]
          have cursorEq : child = Ca := by
            apply LocalizedRerootCursor.ext
            · apply Subtype.ext
              rw [frameAt, CaOcc]
            · rw [localizedSource.executableLocalizedRerootChildren_previous
                C child childPresent, CaPrev]
          rw [cursorEq]
          simp
        · have nodeEq : node = b := by simpa using nodeAtSlot
          have frameAt : child.occurrence.1 =
              { root := C.occurrence.1.root
                address := C.occurrence.1.address ++ [2]
                node := b
                remaining := C.occurrence.1.remaining - 1 } := by
            rw [frameResult, nodeEq]
          have cursorEq : child = Cb := by
            apply LocalizedRerootCursor.ext
            · apply Subtype.ext
              rw [frameAt, CbOcc]
            · rw [localizedSource.executableLocalizedRerootChildren_previous
                C child childPresent, CbPrev]
          rw [cursorEq]
          simp
    · intro childPresent
      rw [List.mem_cons] at childPresent
      rcases childPresent with rfl | childPresent
      · exact memCd
      · rw [List.mem_cons] at childPresent
        rcases childPresent with rfl | childPresent
        · exact memCa
        · rw [List.mem_cons, List.mem_nil_iff, or_false] at childPresent
          have childEq : child = Cb := by
            simpa [eq_comm] using childPresent
          rw [childEq]
          exact memCb
  exact (List.perm_ext_iff_of_nodup actualNodup explicitNodup).mpr sameMembers

/-- The first carbon expands to the duplicate sulfur copy and its two hydrogens. -/
theorem children_c1_perm :
    (localizedSource.executableLocalizedRerootChildren c1).Perm [sDup1, h4, h5] :=
  executableChildren_perm_explicit c1 root
    (prev := rfl) (pAddr := rfl) (slotC := 0) (cAddr := rfl) (nondup := by decide)
    (positive := by decide) (d := c1Node0) (a := c1NodeH4) (b := c1NodeH5)
    (childrenEq := c1Children_eq) (Cd := sDup1) (Ca := h4) (Cb := h5)
    (CdOcc := rfl) (CaOcc := rfl) (CbOcc := rfl)
    (CdPrev := rfl) (CaPrev := rfl) (CbPrev := rfl)

/-- The second carbon expands to the duplicate sulfur copy and its two hydrogens. -/
theorem children_c2_perm :
    (localizedSource.executableLocalizedRerootChildren c2).Perm [sDup2, h6, h7] :=
  executableChildren_perm_explicit c2 root
    (prev := rfl) (pAddr := rfl) (slotC := 2) (cAddr := rfl) (nondup := by decide)
    (positive := by decide) (d := c2Node0) (a := c2NodeH6) (b := c2NodeH7)
    (childrenEq := c2Children_eq) (Cd := sDup2) (Ca := h6) (Cb := h7)
    (CdOcc := rfl) (CaOcc := rfl) (CbOcc := rfl)
    (CdPrev := rfl) (CaPrev := rfl) (CbPrev := rfl)

/-- The third carbon expands to the duplicate sulfur copy and its two hydrogens. -/
theorem children_c3_perm :
    (localizedSource.executableLocalizedRerootChildren c3).Perm [sDup3, h8, h9] :=
  executableChildren_perm_explicit c3 root
    (prev := rfl) (pAddr := rfl) (slotC := 4) (cAddr := rfl) (nondup := by decide)
    (positive := by decide) (d := c3Node0) (a := c3NodeH8) (b := c3NodeH9)
    (childrenEq := c3Children_eq) (Cd := sDup3) (Ca := h8) (Cb := h9)
    (CdOcc := rfl) (CaOcc := rfl) (CbOcc := rfl)
    (CdPrev := rfl) (CaPrev := rfl) (CbPrev := rfl)

/-! ### Terminal child keys and one-level assembly -/

/-- The complete root key of a terminal cursor, with provenance metadata retained. -/
def terminalKey (cursor : localizedSource.LocalizedRerootCursor fuel) :
    OfficialRuleMajorKey localizedSource.Atom :=
  localizedSource.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node true

/-- A terminal cursor compiles at budget zero to its complete root key. -/
theorem build_zero_of_terminal
    (cursor : localizedSource.LocalizedRerootCursor fuel)
    (terminal : localizedSource.executableLocalizedRerootChildren cursor = []) :
    localizedSource.buildLocalizedRerootRuleMajorKeyExec? 0 cursor =
      some (terminalKey cursor) := by
  unfold buildLocalizedRerootRuleMajorKeyExec?
  rw [localizedSource.executableLocalizedRerootChildren?_eq_some]
  simp [terminal, terminalKey]

/-- If a monadic map succeeds pointwise with explicitly known values, it is the ordinary map. -/
theorem mapM_option_of_pointwise {α β : Type*} (f : α → Option β) (g : α → β) :
    ∀ (list : List α), (∀ item ∈ list, f item = some (g item)) →
      list.mapM f = some (list.map g)
  | [], _ => rfl
  | head :: tail, pointwise => by
      have headValue : f head = some (g head) := pointwise head (by simp)
      have tailValues : ∀ item ∈ tail, f item = some (g item) := by
        intro item present
        exact pointwise item (by simp [present])
      simp [List.mapM_cons, headValue, mapM_option_of_pointwise f g tail tailValues]

/-- One-level constitutional assembly from an exact terminal child list.  The actual child list may
be in any order; its keys are sorted, and the resulting key's observable projection is the
assembly of the identical sorted observable list. -/
theorem build_one_observable
    (C : localizedSource.LocalizedRerootCursor fuel)
    (explicit : List (localizedSource.LocalizedRerootCursor fuel))
    (permutation : (localizedSource.executableLocalizedRerootChildren C).Perm explicit)
    (explicitNonempty : explicit ≠ [])
    (terminalChildren : ∀ child ∈ explicit,
      localizedSource.executableLocalizedRerootChildren child = []) :
    ∃ key sorted,
      localizedSource.buildLocalizedRerootRuleMajorKeyExec? 1 C = some key ∧
      (explicit.map terminalKey).Perm sorted ∧
      OfficialRuleMajorKey.Descending sorted ∧
      constitutionalObservable key =
        constitutionalObservable
          (OfficialRuleMajorKey.assemble
            (localizedSource.moleculeGraph.officialRuleMajorRootKey C.occurrence.1.node false)
            sorted) := by
  have actualTerminal : ∀ child ∈
      localizedSource.executableLocalizedRerootChildren C,
      localizedSource.executableLocalizedRerootChildren child = [] := by
    intro child present
    exact terminalChildren child (permutation.mem_iff.mp present)
  have actualMap : (localizedSource.executableLocalizedRerootChildren C).mapM
      (localizedSource.buildLocalizedRerootRuleMajorKeyExec? 0) =
      some ((localizedSource.executableLocalizedRerootChildren C).map terminalKey) :=
    mapM_option_of_pointwise _ _ _
      (fun child present => build_zero_of_terminal child (actualTerminal child present))
  have actualNonempty : localizedSource.executableLocalizedRerootChildren C ≠ [] := by
    intro empty
    have lengths := permutation.length_eq
    rw [empty] at lengths
    exact explicitNonempty (List.eq_nil_of_length_eq_zero lengths.symm)
  have complete : ∀ key ∈
      (localizedSource.executableLocalizedRerootChildren C).map terminalKey,
      key.complete = true := by
    intro key present
    rcases List.mem_map.mp present with ⟨child, _, identity⟩
    rw [← identity]
    rfl
  obtain ⟨sorted, sortedComputation⟩ : ∃ sorted,
      OfficialRuleMajorKey.sort?
        ((localizedSource.executableLocalizedRerootChildren C).map terminalKey) =
        some sorted := by
    have existsSome := OfficialRuleMajorKey.sort?_isSome_of_complete
      ((localizedSource.executableLocalizedRerootChildren C).map terminalKey) complete
    cases computed : OfficialRuleMajorKey.sort?
        ((localizedSource.executableLocalizedRerootChildren C).map terminalKey) with
    | none => simp [computed] at existsSome
    | some sorted => exact ⟨sorted, rfl⟩
  have build : localizedSource.buildLocalizedRerootRuleMajorKeyExec? 1 C =
      some (OfficialRuleMajorKey.assemble
        (localizedSource.moleculeGraph.officialRuleMajorRootKey C.occurrence.1.node false)
        sorted) := by
    unfold buildLocalizedRerootRuleMajorKeyExec?
    rw [localizedSource.executableLocalizedRerootChildren?_eq_some]
    change (if localizedSource.executableLocalizedRerootChildren C = [] then
          some (localizedSource.moleculeGraph.officialRuleMajorRootKey
            C.occurrence.1.node true)
        else
          Option.bind
            (List.mapM (localizedSource.buildLocalizedRerootRuleMajorKeyExec? 0)
              (localizedSource.executableLocalizedRerootChildren C))
            (fun childKeys =>
              Option.bind (OfficialRuleMajorKey.sort? childKeys)
                (fun sorted =>
                  some (OfficialRuleMajorKey.assemble
                    (localizedSource.moleculeGraph.officialRuleMajorRootKey
                      C.occurrence.1.node false) sorted)))) =
        some (OfficialRuleMajorKey.assemble
          (localizedSource.moleculeGraph.officialRuleMajorRootKey
            C.occurrence.1.node false) sorted)
    rw [if_neg actualNonempty, actualMap, Option.bind_some, sortedComputation,
      Option.bind_some]
  refine ⟨_, sorted, build, ?_,
    OfficialRuleMajorKey.sort?_descending _ _ sortedComputation, rfl⟩
  exact (permutation.map terminalKey).symm.trans
    (OfficialRuleMajorKey.sort?_perm _ _ sortedComputation).symm

/-- The observable of an assembled key depends on its children only through their observable
sequence and on its root only through the three rule projections. -/
private def mergeObserved {α : Type*}
    (children : List (List (List (OfficialSparseEntry α)))) :=
  let count := children.foldl (fun longest child => max longest child.length) 0
  (List.range count).map fun depth =>
    children.zipIdx.flatMap fun child =>
      OfficialRuleMajorKey.prefixLayer child.2 (child.1.getD depth [])

private theorem mergeChildren_eq_observed {V α : Type*}
    (children : List (OfficialRuleMajorKey V))
    (layers : OfficialRuleMajorKey V → List (List (OfficialSparseEntry α))) :
    OfficialRuleMajorKey.mergeChildren children layers =
      mergeObserved (children.map layers) := by
  simp only [OfficialRuleMajorKey.mergeChildren, OfficialRuleMajorKey.childLayerCount,
    mergeObserved, List.foldl_map, List.zipIdx_map, List.flatMap_map]
  rfl

/-- Assembly is congruent for roots that are observationally equal but may differ in provenance,
and for child lists whose observable sequences coincide. -/
theorem assembled_observable_eq_of_root_observable {V : Type*}
    (rootLeft rootRight : OfficialRuleMajorKey V)
    (left right : List (OfficialRuleMajorKey V))
    (rootObservation : constitutionalObservable rootLeft =
      constitutionalObservable rootRight)
    (observations : left.map constitutionalObservable =
      right.map constitutionalObservable) :
    constitutionalObservable (OfficialRuleMajorKey.assemble rootLeft left) =
      constitutionalObservable (OfficialRuleMajorKey.assemble rootRight right) := by
  have left1a := congrArg (List.map LocalizedConstitutionalObservable.rule1a) observations
  have left1b := congrArg (List.map LocalizedConstitutionalObservable.rule1b) observations
  have left2 := congrArg (List.map LocalizedConstitutionalObservable.rule2) observations
  have root1a := congrArg LocalizedConstitutionalObservable.rule1a rootObservation
  have root1b := congrArg LocalizedConstitutionalObservable.rule1b rootObservation
  have root2 := congrArg LocalizedConstitutionalObservable.rule2 rootObservation
  simp only [List.map_map, Function.comp_def, constitutionalObservable] at left1a left1b left2 root1a root1b root2
  simp only [constitutionalObservable, OfficialRuleMajorKey.assemble,
    mergeChildren_eq_observed, left1a, left1b, left2, root1a, root1b, root2]

/-! ### Explicit one-level keys for the three carbons -/

theorem terminal_explicit_c1 :
    ∀ child ∈ [sDup1, h4, h5],
      localizedSource.executableLocalizedRerootChildren child = [] := by
  intro child present
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at present
  rcases present with rfl | rfl | rfl
  · exact sDup1_children_nil
  · exact h4_children_nil
  · exact h5_children_nil

theorem terminal_explicit_c2 :
    ∀ child ∈ [sDup2, h6, h7],
      localizedSource.executableLocalizedRerootChildren child = [] := by
  intro child present
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at present
  rcases present with rfl | rfl | rfl
  · exact sDup2_children_nil
  · exact h6_children_nil
  · exact h7_children_nil

theorem terminal_explicit_c3 :
    ∀ child ∈ [sDup3, h8, h9],
      localizedSource.executableLocalizedRerootChildren child = [] := by
  intro child present
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at present
  rcases present with rfl | rfl | rfl
  · exact sDup3_children_nil
  · exact h8_children_nil
  · exact h9_children_nil

theorem build_one_c1_observable :
    ∃ key sorted,
      localizedSource.buildLocalizedRerootRuleMajorKeyExec? 1 c1 = some key ∧
      ([sDup1, h4, h5].map terminalKey).Perm sorted ∧
      OfficialRuleMajorKey.Descending sorted ∧
      constitutionalObservable key =
        constitutionalObservable
          (OfficialRuleMajorKey.assemble
            (localizedSource.moleculeGraph.officialRuleMajorRootKey
              c1.occurrence.1.node false) sorted) :=
  build_one_observable c1 [sDup1, h4, h5] children_c1_perm (by simp)
    terminal_explicit_c1

theorem build_one_c2_observable :
    ∃ key sorted,
      localizedSource.buildLocalizedRerootRuleMajorKeyExec? 1 c2 = some key ∧
      ([sDup2, h6, h7].map terminalKey).Perm sorted ∧
      OfficialRuleMajorKey.Descending sorted ∧
      constitutionalObservable key =
        constitutionalObservable
          (OfficialRuleMajorKey.assemble
            (localizedSource.moleculeGraph.officialRuleMajorRootKey
              c2.occurrence.1.node false) sorted) :=
  build_one_observable c2 [sDup2, h6, h7] children_c2_perm (by simp)
    terminal_explicit_c2

theorem build_one_c3_observable :
    ∃ key sorted,
      localizedSource.buildLocalizedRerootRuleMajorKeyExec? 1 c3 = some key ∧
      ([sDup3, h8, h9].map terminalKey).Perm sorted ∧
      OfficialRuleMajorKey.Descending sorted ∧
      constitutionalObservable key =
        constitutionalObservable
          (OfficialRuleMajorKey.assemble
            (localizedSource.moleculeGraph.officialRuleMajorRootKey
              c3.occurrence.1.node false) sorted) :=
  build_one_observable c3 [sDup3, h8, h9] children_c3_perm (by simp)
    terminal_explicit_c3

/-! ### Equal observable child sequences -/

/-- The first and second carbon have the same terminal-child observable multiset: one duplicate
sulfur copy and two hydrogens. -/
theorem explicitObservables_c1_c2 :
    ([sDup1, h4, h5].map terminalKey).map constitutionalObservable =
      ([sDup2, h6, h7].map terminalKey).map constitutionalObservable := by
  simp only [List.map_map]
  decide

theorem explicitObservables_c1_c3 :
    ([sDup1, h4, h5].map terminalKey).map constitutionalObservable =
      ([sDup3, h8, h9].map terminalKey).map constitutionalObservable := by
  simp only [List.map_map]
  decide

theorem explicitObservables_c2_c3 :
    ([sDup2, h6, h7].map terminalKey).map constitutionalObservable =
      ([sDup3, h8, h9].map terminalKey).map constitutionalObservable := by
  simp only [List.map_map]
  decide

/-- The three real carbon roots have identical constitutional projections. -/
theorem rootObservable_c1_c2 :
    constitutionalObservable
        (localizedSource.moleculeGraph.officialRuleMajorRootKey
          c1.occurrence.1.node false) =
      constitutionalObservable
        (localizedSource.moleculeGraph.officialRuleMajorRootKey
          c2.occurrence.1.node false) := by
  decide

theorem rootObservable_c1_c3 :
    constitutionalObservable
        (localizedSource.moleculeGraph.officialRuleMajorRootKey
          c1.occurrence.1.node false) =
      constitutionalObservable
        (localizedSource.moleculeGraph.officialRuleMajorRootKey
          c3.occurrence.1.node false) := by
  decide

theorem rootObservable_c2_c3 :
    constitutionalObservable
        (localizedSource.moleculeGraph.officialRuleMajorRootKey
          c2.occurrence.1.node false) =
      constitutionalObservable
        (localizedSource.moleculeGraph.officialRuleMajorRootKey
          c3.occurrence.1.node false) := by
  decide

/-! ### Equal one-level keys -/

/-- Two cursors whose explicit terminal expansions have equal observations and equal root
observations have equal one-level constitutional observations. -/
theorem build_one_observables_eq
    (C D : localizedSource.LocalizedRerootCursor fuel)
    (explicitC explicitD : List (localizedSource.LocalizedRerootCursor fuel))
    (permC : (localizedSource.executableLocalizedRerootChildren C).Perm explicitC)
    (permD : (localizedSource.executableLocalizedRerootChildren D).Perm explicitD)
    (nonemptyC : explicitC ≠ []) (nonemptyD : explicitD ≠ [])
    (terminalC : ∀ child ∈ explicitC,
      localizedSource.executableLocalizedRerootChildren child = [])
    (terminalD : ∀ child ∈ explicitD,
      localizedSource.executableLocalizedRerootChildren child = [])
    (explicitObservation :
      (explicitC.map terminalKey).map constitutionalObservable =
        (explicitD.map terminalKey).map constitutionalObservable)
    (rootObservation :
      constitutionalObservable
          (localizedSource.moleculeGraph.officialRuleMajorRootKey
            C.occurrence.1.node false) =
        constitutionalObservable
          (localizedSource.moleculeGraph.officialRuleMajorRootKey
            D.occurrence.1.node false))
    {keyC keyD : OfficialRuleMajorKey localizedSource.Atom}
    (buildC : localizedSource.buildLocalizedRerootRuleMajorKeyExec? 1 C = some keyC)
    (buildD : localizedSource.buildLocalizedRerootRuleMajorKeyExec? 1 D = some keyD) :
    constitutionalObservable keyC = constitutionalObservable keyD := by
  obtain ⟨keyC', sortedC, buildC', permSortedC, descendingC, observedC⟩ :=
    build_one_observable C explicitC permC nonemptyC terminalC
  obtain ⟨keyD', sortedD, buildD', permSortedD, descendingD, observedD⟩ :=
    build_one_observable D explicitD permD nonemptyD terminalD
  have keyCEq : keyC' = keyC := Option.some.inj (buildC'.symm.trans buildC)
  have keyDEq : keyD' = keyD := Option.some.inj (buildD'.symm.trans buildD)
  rw [keyCEq] at observedC
  rw [keyDEq] at observedD
  have sortedPermutation :
      (sortedC.map constitutionalObservable).Perm
        (sortedD.map constitutionalObservable) := by
    have leftStep :
        (sortedC.map constitutionalObservable).Perm
          ((explicitC.map terminalKey).map constitutionalObservable) :=
      (permSortedC.map constitutionalObservable).symm
    rw [explicitObservation] at leftStep
    exact leftStep.trans (permSortedD.map constitutionalObservable)
  have sortedObservation :=
    constitutional_observables_eq_of_perm sortedC sortedD sortedPermutation
      descendingC descendingD
  have assembledObservation :=
    assembled_observable_eq_of_root_observable
      (localizedSource.moleculeGraph.officialRuleMajorRootKey C.occurrence.1.node false)
      (localizedSource.moleculeGraph.officialRuleMajorRootKey D.occurrence.1.node false)
      sortedC sortedD rootObservation sortedObservation
  exact observedC.trans (assembledObservation.trans observedD.symm)

theorem lowObservables_c1_c2
    {left right : OfficialRuleMajorKey localizedSource.Atom}
    (buildLeft : localizedSource.buildLocalizedRerootRuleMajorKeyExec? 1 c1 = some left)
    (buildRight : localizedSource.buildLocalizedRerootRuleMajorKeyExec? 1 c2 = some right) :
    constitutionalObservable left = constitutionalObservable right :=
  build_one_observables_eq c1 c2 [sDup1, h4, h5] [sDup2, h6, h7]
    children_c1_perm children_c2_perm (by simp) (by simp)
    terminal_explicit_c1 terminal_explicit_c2 explicitObservables_c1_c2
    rootObservable_c1_c2 buildLeft buildRight

theorem lowObservables_c1_c3
    {left right : OfficialRuleMajorKey localizedSource.Atom}
    (buildLeft : localizedSource.buildLocalizedRerootRuleMajorKeyExec? 1 c1 = some left)
    (buildRight : localizedSource.buildLocalizedRerootRuleMajorKeyExec? 1 c3 = some right) :
    constitutionalObservable left = constitutionalObservable right :=
  build_one_observables_eq c1 c3 [sDup1, h4, h5] [sDup3, h8, h9]
    children_c1_perm children_c3_perm (by simp) (by simp)
    terminal_explicit_c1 terminal_explicit_c3 explicitObservables_c1_c3
    rootObservable_c1_c3 buildLeft buildRight

theorem lowObservables_c2_c3
    {left right : OfficialRuleMajorKey localizedSource.Atom}
    (buildLeft : localizedSource.buildLocalizedRerootRuleMajorKeyExec? 1 c2 = some left)
    (buildRight : localizedSource.buildLocalizedRerootRuleMajorKeyExec? 1 c3 = some right) :
    constitutionalObservable left = constitutionalObservable right :=
  build_one_observables_eq c2 c3 [sDup2, h6, h7] [sDup3, h8, h9]
    children_c2_perm children_c3_perm (by simp) (by simp)
    terminal_explicit_c2 terminal_explicit_c3 explicitObservables_c2_c3
    rootObservable_c2_c3 buildLeft buildRight

/-! ### Path validity of the carbon cursors -/

theorem valid_c1 : localizedSource.LocalizedRerootCursorValid c1 :=
  localizedSource.localizedRerootChild_valid root c1
    (localizedSource.executableLocalizedRerootChildren root)
    (localizedSource.executableLocalizedRerootChildren_declarative root) c1_mem

theorem valid_c2 : localizedSource.LocalizedRerootCursorValid c2 :=
  localizedSource.localizedRerootChild_valid root c2
    (localizedSource.executableLocalizedRerootChildren root)
    (localizedSource.executableLocalizedRerootChildren_declarative root) c2_mem

theorem valid_c3 : localizedSource.LocalizedRerootCursorValid c3 :=
  localizedSource.localizedRerootChild_valid root c3
    (localizedSource.executableLocalizedRerootChildren root)
    (localizedSource.executableLocalizedRerootChildren_declarative root) c3_mem

/-! ### From observations to exact comparisons

Success at the common structural budget is stable, so any two successful low-budget observations
that agree determine an exact `eq` comparison at the budget used by the production comparison
function. -/

theorem compare_eq_of_low_observations
    {carrierFuel : Nat}
    (C D : localizedSource.LocalizedRerootCursor carrierFuel)
    (leftFuel rightFuel : Nat)
    (lowC lowD : OfficialRuleMajorKey localizedSource.Atom)
    (buildC : localizedSource.buildLocalizedRerootRuleMajorKeyExec? leftFuel C = some lowC)
    (buildD : localizedSource.buildLocalizedRerootRuleMajorKeyExec? rightFuel D = some lowD)
    (lowObservation : constitutionalObservable lowC = constitutionalObservable lowD)
    (validC : localizedSource.LocalizedRerootCursorValid C)
    (validD : localizedSource.LocalizedRerootCursorValid D) :
    localizedSource.compareLocalizedConstitutionalCursors? C D = some .eq := by
  obtain ⟨keyC, keyBuildC⟩ :=
    localizedSource.exists_constitutionalKey_at_linear_bound C validC
  obtain ⟨keyD, keyBuildD⟩ :=
    localizedSource.exists_constitutionalKey_at_linear_bound D validD
  have stableC : constitutionalObservable lowC = constitutionalObservable keyC :=
    localizedSource.constitutionalKeyExec_observable_stable leftFuel
      (2 * (carrierFuel + 1) + 1) C lowC keyC buildC keyBuildC
  have stableD : constitutionalObservable lowD = constitutionalObservable keyD :=
    localizedSource.constitutionalKeyExec_observable_stable rightFuel
      (2 * (carrierFuel + 1) + 1) D lowD keyD buildD keyBuildD
  have keyObservation :
      constitutionalObservable keyC = constitutionalObservable keyD :=
    stableC.symm.trans (lowObservation.trans stableD)
  have exactComparison : OfficialRuleMajorKey.compare keyC keyD = .eq := by
    rw [ruleMajor_compare_eq_observable]
    exact (compareConstitutionalObservable_eq_iff _ _).mpr keyObservation
  unfold compareLocalizedConstitutionalCursors?
  simp only [keyBuildC, keyBuildD, Option.bind_some]
  exact congrArg some exactComparison

theorem tie_c1_c2 :
    localizedSource.compareLocalizedConstitutionalCursors? c1 c2 = some .eq := by
  obtain ⟨key1, sorted1, build1, _perm1, _descending1, _observed1⟩ :=
    build_one_c1_observable
  obtain ⟨key2, sorted2, build2, _perm2, _descending2, _observed2⟩ :=
    build_one_c2_observable
  exact compare_eq_of_low_observations c1 c2 1 1 key1 key2 build1 build2
    (lowObservables_c1_c2 build1 build2) valid_c1 valid_c2

theorem tie_c1_c3 :
    localizedSource.compareLocalizedConstitutionalCursors? c1 c3 = some .eq := by
  obtain ⟨key1, sorted1, build1, _perm1, _descending1, _observed1⟩ :=
    build_one_c1_observable
  obtain ⟨key3, sorted3, build3, _perm3, _descending3, _observed3⟩ :=
    build_one_c3_observable
  exact compare_eq_of_low_observations c1 c3 1 1 key1 key3 build1 build3
    (lowObservables_c1_c3 build1 build3) valid_c1 valid_c3

theorem tie_c2_c3 :
    localizedSource.compareLocalizedConstitutionalCursors? c2 c3 = some .eq := by
  obtain ⟨key2, sorted2, build2, _perm2, _descending2, _observed2⟩ :=
    build_one_c2_observable
  obtain ⟨key3, sorted3, build3, _perm3, _descending3, _observed3⟩ :=
    build_one_c3_observable
  exact compare_eq_of_low_observations c2 c3 1 1 key2 key3 build2 build3
    (lowObservables_c2_c3 build2 build3) valid_c2 valid_c3

/-! ### The hydrogen--hydrogen tie at the first carbon -/

theorem h4_children_terminal :
    localizedSource.executableLocalizedRerootChildren h4 = [] := h4_children_nil

theorem h5_children_terminal :
    localizedSource.executableLocalizedRerootChildren h5 = [] := h5_children_nil

theorem h4_build_zero :
    localizedSource.buildLocalizedRerootRuleMajorKeyExec? 0 h4 =
      some (terminalKey h4) :=
  build_zero_of_terminal h4 h4_children_nil

theorem h5_build_zero :
    localizedSource.buildLocalizedRerootRuleMajorKeyExec? 0 h5 =
      some (terminalKey h5) :=
  build_zero_of_terminal h5 h5_children_nil

theorem terminalObservable_h4_h5 :
    constitutionalObservable (terminalKey h4) =
      constitutionalObservable (terminalKey h5) := by
  decide

theorem valid_h4 : localizedSource.LocalizedRerootCursorValid h4 :=
  localizedSource.localizedRerootChild_valid c1 h4
    (localizedSource.executableLocalizedRerootChildren c1)
    (localizedSource.executableLocalizedRerootChildren_declarative c1)
    (children_c1_perm.mem_iff.mpr (by simp))

theorem valid_h5 : localizedSource.LocalizedRerootCursorValid h5 :=
  localizedSource.localizedRerootChild_valid c1 h5
    (localizedSource.executableLocalizedRerootChildren c1)
    (localizedSource.executableLocalizedRerootChildren_declarative c1)
    (children_c1_perm.mem_iff.mpr (by simp))

theorem tie_h4_h5 :
    localizedSource.compareLocalizedConstitutionalCursors? h4 h5 = some .eq :=
  compare_eq_of_low_observations h4 h5 0 0 (terminalKey h4) (terminalKey h5)
    h4_build_zero h5_build_zero terminalObservable_h4_h5 valid_h4 valid_h5

/-! ### Unconditional production request membership -/

/-- The second carbon is an actual retained request at the first carbon. -/
theorem c2_mem_requests_c1 :
    c2 ∈ (localizedSource.rule3PreflightExtendedNodeCallbackRequests c1.occurrence).flatten :=
  c2_mem_requests_c1_of_ties tie_c2_c3 tie_h4_h5

/-- The first carbon is an actual retained request at the second carbon. -/
theorem c1_mem_requests_c2 :
    c1 ∈ (localizedSource.rule3PreflightExtendedNodeCallbackRequests c2.occurrence).flatten :=
  c1_mem_requests_c2_of_tie tie_c1_c3

/-- The first carbon's entire production preflight request list, with no tie hypotheses. -/
theorem requests_c1_eq_unconditional :
    localizedSource.rule3PreflightExtendedNodeCallbackRequests c1.occurrence =
      [[c2, c3], [h4, h5]] :=
  requests_c1_eq_pairs_of_ties tie_c2_c3 tie_h4_h5

/-- The nontrivial sulfur-side endpoint request at the second carbon, with no tie hypotheses. -/
theorem endpointRequests_c2_eq_unconditional :
    localizedSource.rule3ShortEndpointCallbackRequests atom0 atom2 leftCursor2 =
      [[c1, c3]] :=
  endpointRequests_0_2_eq_of_tie tie_c1_c3

/-! ## The actual two-cycle -/

def demandGraph : Graph (localizedSource.LocalizedRerootCursor fuel) :=
  localizedSource.preflightExtendedWeightedDemandGraph fuel

theorem edge_root_c1 : Edge demandGraph root c1 := by
  unfold Edge successors demandGraph
  exact List.mem_append_left _ c1_mem

theorem edge_c1_c2 : Edge demandGraph c1 c2 := by
  unfold Edge successors demandGraph
  exact List.mem_append_right _ c2_mem_requests_c1

theorem edge_c2_c1 : Edge demandGraph c2 c1 := by
  unfold Edge successors demandGraph
  exact List.mem_append_right _ c1_mem_requests_c2

/-- The actual demand graph contains the genuinely reachable cycle `c1 → c2 → c1`. -/
theorem demandCycle_c1 : Relation.TransGen (Edge demandGraph) c1 c1 :=
  Relation.TransGen.head edge_c1_c2 (Relation.TransGen.single edge_c2_c1)

theorem reachable_c1 :
    Reachable demandGraph [root] c1 :=
  ⟨root, by simp, Relation.ReflTransGen.head edge_root_c1 Relation.ReflTransGen.refl⟩

/-- The actual admitted fixture graph is not acyclic from its root. -/
theorem not_acyclic_fixture : ¬ Acyclic demandGraph [root] := by
  intro acyclic
  exact acyclic c1 reachable_c1 demandCycle_c1

theorem plan_error_exists :
    ∃ failure,
      localizedSource.preparePreflightExtendedDemandPlan [root] = .error failure :=
  (localizedSource.preparePreflightExtendedDemandPlan_error_iff_reachableCycle [root]).mpr
    ⟨c1, reachable_c1, demandCycle_c1⟩

/-- The production constructor refuses the actual fixture occurrence at every evaluation budget,
for every dependency view. -/
theorem allFuelRefusal_c1_allViews :
    ∀ view,
      UniversalRule3AllFuelRefusal localizedSource [root] c1.occurrence view := by
  intro view
  obtain ⟨failure, failed⟩ := plan_error_exists
  exact localizedSource.preparePreflightExtendedDemandPlan_error_allFuelRefusal [root]
    failure failed c1.occurrence view

theorem allFuelRefusal_c1 :
    UniversalRule3AllFuelRefusal localizedSource [root] c1.occurrence
      (fun _ _ => none) :=
  allFuelRefusal_c1_allViews (fun _ _ => none)

/-! ## The admitted fixture refutes domain-wide preflight acyclicity

The domain is an input-graph/admission fact: the exact supplied authoritative source is admitted.
It says nothing about the evaluator succeeding or about a desired descriptor.  The theorem shows
that no claim of the form "every admitted instance of this source, at every carrier fuel and every
root list, has an acyclic preflight demand graph" can hold. -/

def FixtureAdmittedAcyclic : Prop :=
  ∀ (input : LocalizedReference.Input),
    LocalizedReference.admitSource? source = some input →
    ∀ (carrierFuel : Nat)
      (roots : List (input.certified.LocalizedRerootCursor carrierFuel)),
      Acyclic (input.certified.preflightExtendedWeightedDemandGraph carrierFuel) roots

theorem fixture_input_admitted :
    LocalizedReference.admitSource? source = some input := admission

theorem fixtureAdmittedAcyclic_false : ¬ FixtureAdmittedAcyclic := by
  intro universal
  exact not_acyclic_fixture (universal input admission fuel [root])

/-! ## A tiny independent priority-skeleton repair lemma

The Rule-3 spatial skeleton returns a nonstereogenic unit as soon as either complete endpoint
priority is `nonstereogenic`, before inspecting the other endpoint's reference or any spatial
coordinate.  Thus, if one physical endpoint can be shown nonstereogenic from its own terminal
subtree, the other endpoint's callback references are semantically unnecessary for this double
bond.  The lemma below records only this branch; it does not assert that the fixture's hydrogen
endpoint has been proved nonstereogenic, nor does it change production behavior. -/

theorem nonstereogenicEndpoint_shortCircuit
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftPriority : input.LocalizedRule3EndpointPriority)
    (doubleBond : input.moleculeGraph.bond left right = 2) :
    input.localizedRule3DescriptorBearingSpatialUnitOfPriorities? left right
        leftPriority .nonstereogenic =
      some { leftPriority := leftPriority, rightPriority := .nonstereogenic,
             geometry := OfficialRule3Geometry.nonstereogenic } := by
  unfold localizedRule3DescriptorBearingSpatialUnitOfPriorities?
  rw [if_pos doubleBond]
  cases leftPriority <;> rfl

/-! ## Kernel-authority guards for the main results -/

assert_kernel_only tie_c1_c3
assert_kernel_only tie_c2_c3
assert_kernel_only tie_h4_h5
assert_kernel_only c2_mem_requests_c1
assert_kernel_only c1_mem_requests_c2
assert_kernel_only requests_c1_eq_unconditional
assert_kernel_only endpointRequests_c2_eq_unconditional
assert_kernel_only demandCycle_c1
assert_kernel_only not_acyclic_fixture
assert_kernel_only plan_error_exists
assert_kernel_only allFuelRefusal_c1_allViews
assert_kernel_only allFuelRefusal_c1
assert_kernel_only fixtureAdmittedAcyclic_false
assert_kernel_only nonstereogenicEndpoint_shortCircuit
