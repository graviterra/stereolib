import TetraStereo.OneCenter.LocalizedTerminalGuardedRule3Node
import TetraStereo.OneCenter.LocalizedPreflightDemandDiscovery
import TetraStereo.OneCenter.LocalizedPreflightDemandTotality
import TetraStereo.OneCenter.LocalizedExtendedMandatoryRecursion
import TetraStereo.OneCenter.LocalizedOccurrenceExecutableRoots
import TetraStereo.OneCenter.LocalizedShortCircuitPipeline
import TetraStereo.OneCenter.LocalizedRule3DemandRankProducer
import TetraStereo.OneCenter.LocalizedRule3RouteCompleteness
import TetraStereo.OneCenter.LocalizedPhysicalReferenceUniqueness
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-!
# Kernel witness: the terminal guard accepts the H/H endpoints of the ten-atom
# `S(=CH₂)₃` retained-demand-cycle fixture

This module is a concrete, executable end-to-end validation of the terminal guard
`terminalReferencePair?` / `localizedRule3TerminalGuard?` on the syntactically admitted ten-atom
fixture already used by the retained-demand-cycle investigation:

* sulfur at atom `0`, the three doubly bonded carbons at atoms `1,2,3`, and one hydrogen pair
  (`4,5`), (`6,7`), (`8,9`) on the three carbons;
* no coordinates, no diagram; the input passes the real structural admission and localized graph
  readiness gates.

Everything below is a statement about the **actual** executable definitions, evaluated by the
Lean kernel.  The only fixture-specific proofs that use computation are small closed finite facts
(neighbour sorts, child lists, root labels and distances, an executable double-bond decision).
No guard certificate is assumed: `terminalReferencePair?` itself performs the candidate lookup,
the reference-cursor lookups, the leaf and structural-nonunit checks, the root observations, the
compound Rules-4b--5 key compilations, their comparison, and the production two-terminal frame
computation.

For the first two carbons the incoming double bond is recovered as the physical endpoint frame
with sulfur on the left and the carbon on the right.  The right endpoint carries the two hydrogen
references; the left endpoint carries two non-terminal carbons.  The guard therefore rejects the
left endpoint and accepts the right one.  The resulting identities are nonstereogenic.  In
addition, the reduced callback demand is literally the empty list at both cycle origins, and the
guarded evaluator's result is independent of an arbitrary callback.

The dependency view is fixed to the constant-`none` reader.  This is a view-dependent result: the
guard consumes the restricted Rules-4b--5 view, and arbitrary-reader locality is not claimed here.
The fixture leaves are finite carrier leaves; the statements do not by themselves assert general
chemical terminality, and nothing below claims that the whole guarded graph is acyclic merely
because these two named occurrences demand no sibling callback.
-/

namespace TetraStereo.OneCenter.LocalizedTerminalGuardedCycleWitness

open TetraStereo.OneCenter
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalEndpointObservation
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedRule3Node

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

/-- The fixture passes the Boolean structural admission gate. -/
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

/-- The real source-admission pipeline returns exactly the constructed input. -/
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

/-! ## Kernel computation of the sorted neighbour lists -/

/-- If `l` is a nodup, sorted enumeration of `s`, then `s.sort` is `l`. -/
theorem sort_of_toFinset_eq (a : localizedSource.Atom) (l : List localizedSource.Atom)
    (hset : l.toFinset = localizedSource.moleculeGraph.neighborFinset a)
    (hnd : l.Nodup) (hpw : l.Pairwise (· ≤ ·)) :
    (localizedSource.moleculeGraph.neighborFinset a).sort (· ≤ ·) = l := by
  rw [← hset]
  exact (List.toFinset_sort (r := (· ≤ ·)) (l := l) hnd).mpr hpw

/-- The sorted neighbour list of every atom of the fixture. -/
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

def root : localizedSource.LocalizedRerootCursor fuel :=
  { occurrence := localizedSource.localizedAtomRootOccurrenceExecutable fuel atom0 }

theorem root_previous : root.previous? = none := rfl

def rootNode : OfficialCIPNode localizedSource.Atom := OfficialCIPNode.root atom0

def node1 : OfficialCIPNode localizedSource.Atom := rootNode.extend atom1 0
def node1d : OfficialCIPNode localizedSource.Atom := rootNode.extend atom1 1
def node2 : OfficialCIPNode localizedSource.Atom := rootNode.extend atom2 0
def node2d : OfficialCIPNode localizedSource.Atom := rootNode.extend atom2 1
def node3 : OfficialCIPNode localizedSource.Atom := rootNode.extend atom3 0
def node3d : OfficialCIPNode localizedSource.Atom := rootNode.extend atom3 1

theorem rootChildren_eq :
    localizedSource.executableOfficialCIPChildren rootNode =
      [node1, node1d, node2, node2d, node3, node3d] := by
  simp only [executableOfficialCIPChildren, executableOfficialChildCopies,
    executableOfficialNeighborCopies, neighborSort_eq, rootNode, node1, node1d, node2, node2d,
    node3, node3d, atom0]
  decide

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

def frame1 : localizedSource.LocalizedCIPOccurrenceFrame :=
  { root := atom0, address := [0], node := node1, remaining := fuel }

def frame2 : localizedSource.LocalizedCIPOccurrenceFrame :=
  { root := atom0, address := [2], node := node2, remaining := fuel }

def frame3 : localizedSource.LocalizedCIPOccurrenceFrame :=
  { root := atom0, address := [4], node := node3, remaining := fuel }

theorem frame1_mem : frame1 ∈ localizedSource.localizedOccurrences fuel := by
  rw [localizedSource.mem_localizedOccurrences_iff]
  exact DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (path := []) (fuel := fuel) (node := rootNode) (child := node1) (slot := 0)
    (occurrence := frame1)
    (by rw [rootChildren_eq]; decide)
    (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot [0] fuel node1)

theorem frame2_mem : frame2 ∈ localizedSource.localizedOccurrences fuel := by
  rw [localizedSource.mem_localizedOccurrences_iff]
  exact DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (path := []) (fuel := fuel) (node := rootNode) (child := node2) (slot := 2)
    (occurrence := frame2)
    (by rw [rootChildren_eq]; decide)
    (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot [2] fuel node2)

theorem frame3_mem : frame3 ∈ localizedSource.localizedOccurrences fuel := by
  rw [localizedSource.mem_localizedOccurrences_iff]
  exact DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (path := []) (fuel := fuel) (node := rootNode) (child := node3) (slot := 4)
    (occurrence := frame3)
    (by rw [rootChildren_eq]; decide)
    (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot [4] fuel node3)

def c1 : localizedSource.LocalizedRerootCursor fuel :=
  { occurrence := ⟨frame1, frame1_mem⟩, previous? := some root.occurrence }

def c2 : localizedSource.LocalizedRerootCursor fuel :=
  { occurrence := ⟨frame2, frame2_mem⟩, previous? := some root.occurrence }

def c3 : localizedSource.LocalizedRerootCursor fuel :=
  { occurrence := ⟨frame3, frame3_mem⟩, previous? := some root.occurrence }

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
erase.  This removes the second kernel obstruction: the explicit Rule-3 substituent list sorts an
*erased* neighbour finset. -/
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

/-! ## Root coordinates -/

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

/-- The declarative meaning of `topology1`. -/
theorem topology1_spec :
    localizedSource.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame c1.occurrence topology1 := by
  refine ⟨rfl, rfl, rfl, by decide, carrierParent_c1, rfl, rfl, rfl, rfl⟩

/-- Physical endpoint recovery at the first carbon. -/
theorem physical_c1 :
    localizedSource.localizedRule3PhysicalEndpointCursorFrameExec? c1.occurrence =
      some topology1 :=
  localizedSource.localizedRule3PhysicalEndpointCursorFrameExec?_eq_some_of_declarative
    c1.occurrence topology1 topology1_spec

/-! ## Endpoint substituent lists -/

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

/-- Reference selection at the left endpoint for atom `2`. -/
theorem refExec_c2 :
    localizedSource.localizedRule3ReferenceCursorExec? leftCursor1 atom2 = some c2 := by
  have declarative : localizedSource.DeclarativeLocalizedRule3ReferenceCursor
      leftCursor1 c2 atom2 := by
    obtain ⟨children, computed, mem, derived⟩ := exists_children_c2
    exact ⟨children, computed, derived, mem, rfl, trivial, rfl⟩
  rw [← localizedSource.localizedRule3ReferenceCursor?_eq_localizedRule3ReferenceCursorExec?]
  exact localizedSource.localizedRule3ReferenceCursor?_eq_some_of_declarative
    leftCursor1 c2 atom2 declarative

/-- Reference selection at the left endpoint for atom `3`. -/
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

/-- Reference selection at the right endpoint for atom `4`. -/
theorem refExec_h4 :
    localizedSource.localizedRule3ReferenceCursorExec? rightCursor1 atom4 = some h4 := by
  have declarative : localizedSource.DeclarativeLocalizedRule3ReferenceCursor
      rightCursor1 h4 atom4 := by
    obtain ⟨children, computed, mem, derived⟩ := exists_children_h4
    exact ⟨children, computed, derived, mem, rfl, trivial, rfl⟩
  rw [← localizedSource.localizedRule3ReferenceCursor?_eq_localizedRule3ReferenceCursorExec?]
  exact localizedSource.localizedRule3ReferenceCursor?_eq_some_of_declarative
    rightCursor1 h4 atom4 declarative

/-- Reference selection at the right endpoint for atom `5`. -/
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

/-- Readiness of the first carbon endpoint. -/
theorem ordinaryPairReady_c1 :
    localizedSource.ordinaryPairReady c1.occurrence = true := by
  simp only [ordinaryPairReady, physical_c1, topology1, rule3EndpointPairReady,
    substituents_0_1, substituents_1_0, refExec_c2, refExec_c3, refExec_h4, refExec_h5,
    Option.isSome_some]
  rfl

/-! ## The physical route certificate of the first carbon -/

theorem edge_c1 :
    localizedSource.LocalizedOccurrenceHasRule3DoubleBondEdge c1.occurrence := by
  refine ⟨rfl, atom1, atom0, rfl, rfl, ?_⟩
  decide

theorem c2_mem_executableChildren :
    c2 ∈ localizedSource.executableLocalizedRerootChildren leftCursor1 := by
  obtain ⟨children, computed, mem, _derived⟩ := exists_children_c2
  have executableEq := localizedSource.localizedRerootChildren?_eq_some_executable leftCursor1
  have childrenEq : children = localizedSource.executableLocalizedRerootChildren leftCursor1 :=
    (Option.some.injEq _ _).mp (computed.symm.trans executableEq)
  rwa [childrenEq] at mem

theorem c3_mem_executableChildren :
    c3 ∈ localizedSource.executableLocalizedRerootChildren leftCursor1 := by
  obtain ⟨children, computed, mem, _derived⟩ := exists_children_c3
  have executableEq := localizedSource.localizedRerootChildren?_eq_some_executable leftCursor1
  have childrenEq : children = localizedSource.executableLocalizedRerootChildren leftCursor1 :=
    (Option.some.injEq _ _).mp (computed.symm.trans executableEq)
  rwa [childrenEq] at mem

theorem axisContinuation_c2 :
    localizedSource.LocalizedRule3AxisPhysicalContinuation leftCursor1 c2 := by
  refine ⟨leftCursor1_provenance, ?_, ?_⟩
  · decide
  · show localizedSource.moleculeGraph.bond atom0 atom2 = 2
    decide

theorem axisContinuation_c3 :
    localizedSource.LocalizedRule3AxisPhysicalContinuation leftCursor1 c3 := by
  refine ⟨leftCursor1_provenance, ?_, ?_⟩
  · decide
  · show localizedSource.moleculeGraph.bond atom0 atom3 = 2
    decide

theorem c2_ne_c3 : c2 ≠ c3 := by
  intro equally
  have addresses := congrArg (fun cursor => cursor.occurrence.1.address) equally
  simp only at addresses
  rw [c2_address, c3_address] at addresses
  exact absurd addresses (by decide)

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

theorem exists_two_cons_of_two_le_length {α : Type*} {values : List α}
    (long : 2 ≤ values.length) : ∃ first second rest, values = first :: second :: rest := by
  cases values with
  | nil => simp at long
  | cons head tail =>
      cases tail with
      | nil => simp at long
      | cons next rest => exact ⟨head, next, rest, rfl⟩

theorem axisContinuations_two_le :
    2 ≤ (localizedSource.localizedRule3AxisPhysicalContinuationCursorsExec leftCursor1
      (localizedSource.executableLocalizedRerootChildren leftCursor1)).length := by
  apply two_le_length_of_mem_of_mem (first := c2) (second := c3)
  · simp only [localizedRule3AxisPhysicalContinuationCursorsExec, List.mem_filter]
    exact ⟨c2_mem_executableChildren, decide_eq_true axisContinuation_c2⟩
  · simp only [localizedRule3AxisPhysicalContinuationCursorsExec, List.mem_filter]
    exact ⟨c3_mem_executableChildren, decide_eq_true axisContinuation_c3⟩
  · exact c2_ne_c3

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

theorem axisEntry_c1_branched :
    ∃ initial first second rest,
      localizedSource.localizedRule3CumulatedAxisEntryExec? c1.occurrence =
        some (.branched initial first second rest) := by
  obtain ⟨first, second, rest, topology⟩ := axisTopology_c1_branched
  refine ⟨topology1, first, second, rest, ?_⟩
  simp [localizedRule3CumulatedAxisEntryExec?, physical_c1, topology1, topology]

theorem oddRoute_c1_eq_none :
    localizedSource.localizedRule3OddRouteCertificate? c1.occurrence = none := by
  obtain ⟨initial, first, second, rest, entry⟩ := axisEntry_c1_branched
  simp only [localizedRule3OddRouteCertificate?]
  rw [dif_pos edge_c1]
  rw [entry]

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

/-! ## Real hydrogen leaves have no executable children -/

/-- A non-duplicate node with no official children has no intended children, provided the incoming
coordinate is its carrier parent (so every parent frame is cut) and the frame's address is one
official slot below the parent.  Outward children would be immediate official children, of which
there are none.  This is the general finite-carrier leaf criterion used for the two hydrogens; it
does not claim chemical terminality of truncated carrier leaves. -/
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

@[simp] theorem c1NodeH4_parent : c1NodeH4.parent? = some atom1 := rfl
@[simp] theorem c1NodeH5_parent : c1NodeH5.parent? = some atom1 := rfl
@[simp] theorem c2NodeH6_parent : c2NodeH6.parent? = some atom2 := rfl
@[simp] theorem c2NodeH7_parent : c2NodeH7.parent? = some atom2 := rfl
@[simp] theorem h4_parent : h4.occurrence.1.node.parent? = some atom1 := rfl
@[simp] theorem h5_parent : h5.occurrence.1.node.parent? = some atom1 := rfl

theorem h4_children_nil :
    localizedSource.executableLocalizedRerootChildren h4 = [] := by
  apply executableChildren_nil_of_officialChildren_nil localizedSource rightCursor1 h4
    (incoming := rfl) (slot := 1) (address := rfl) (nonduplicate := by decide)
  unfold executableOfficialCIPChildren
  simp only [executableOfficialChildCopies, executableOfficialNeighborCopies,
    neighborSort_eq, atom1]
  decide

theorem h5_children_nil :
    localizedSource.executableLocalizedRerootChildren h5 = [] := by
  apply executableChildren_nil_of_officialChildren_nil localizedSource rightCursor1 h5
    (incoming := rfl) (slot := 2) (address := rfl) (nonduplicate := by decide)
  unfold executableOfficialCIPChildren
  simp only [executableOfficialChildCopies, executableOfficialNeighborCopies,
    neighborSort_eq, atom1]
  decide

theorem h4_terminal :
    localizedSource.executableLocalizedRerootChildren? h4 = some [] := by
  rw [executableLocalizedRerootChildren?_eq_some, h4_children_nil]

theorem h5_terminal :
    localizedSource.executableLocalizedRerootChildren? h5 = some [] := by
  rw [executableLocalizedRerootChildren?_eq_some, h5_children_nil]

/-- A hydrogen cannot be on an order-two bond to its parent carbon. -/
theorem h4_nonunit :
    ¬ localizedSource.LocalizedOccurrenceHasRule3DoubleBondEdge h4.occurrence := by
  rintro ⟨_, current, parent, currentEq, parentEq, bondEq⟩
  rw [h4_current, Option.some.injEq] at currentEq
  rw [h4_parent, Option.some.injEq] at parentEq
  subst currentEq
  subst parentEq
  exact absurd bondEq (by decide)

theorem h5_nonunit :
    ¬ localizedSource.LocalizedOccurrenceHasRule3DoubleBondEdge h5.occurrence := by
  rintro ⟨_, current, parent, currentEq, parentEq, bondEq⟩
  rw [h5_current, Option.some.injEq] at currentEq
  rw [h5_parent, Option.some.injEq] at parentEq
  subst currentEq
  subst parentEq
  exact absurd bondEq (by decide)

/-- Both hydrogens of the first carbon carry the same official atom label. -/
theorem labelEq_h4_h5 :
    localizedSource.moleculeGraph.officialNodeAtomLabel h4.occurrence.1.node =
      localizedSource.moleculeGraph.officialNodeAtomLabel h5.occurrence.1.node := by
  decide

/-- Both hydrogens of the first carbon are at the same Rule-1b root distance. -/
theorem distanceEq_h4_h5 :
    h4.occurrence.1.node.rule1bRootDistance =
      h5.occurrence.1.node.rule1bRootDistance := by
  decide

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

/-- The `do`-notation form of the `Option` bind on a successful value.  This is the syntactic
shape produced by the executable compilers, whose intermediate results are all known `some`s. -/
private theorem option_some_bind_apply {α β : Type} (value : α)
    (continuation : α → Option β) :
    (some value : Option α) >>= continuation = continuation value :=
  rfl

/-- The empty dependency view reads no auxiliary label anywhere. -/
theorem dependencyLabel_const_none (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    input.localizedDependencyLabel target (fun _ _ => none) cursor = none := by
  unfold localizedDependencyLabel
  split
  · rfl
  · rfl

/-- The executable cumulative compiler returns the canonical terminal cumulative key at every
stage and every budget. -/
theorem buildCumulative_terminal (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (terminal : input.executableLocalizedRerootChildren? cursor = some [])
    (stage : LocalizedCumulativeRule45Stage) (fuel : Nat) :
    input.buildLocalizedRerootCumulativeRule45KeyExec? stage target (fun _ _ => none) fuel
        cursor =
      some (terminalCumulativeKey input cursor.occurrence.1.node stage) := by
  cases fuel with
  | zero =>
      simp only [buildLocalizedRerootCumulativeRule45KeyExec?, terminal,
        dependencyLabel_const_none]
      rfl
  | succ fuel =>
      simp only [buildLocalizedRerootCumulativeRule45KeyExec?, terminal,
        dependencyLabel_const_none]
      rfl

/-- The executable no-reference Rule-4b/4c reading compiler returns the canonical terminal
reading. -/
theorem buildReading_none_terminal (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (terminal : input.executableLocalizedRerootChildren? cursor = some [])
    (fuel : Nat) :
    input.buildLocalizedRerootRule4bcReadingExec? target (fun _ _ => none) fuel cursor none =
      some (terminalReading input cursor.occurrence.1.node) := by
  simp only [buildLocalizedRerootRule4bcReadingExec?, option_some_bind_apply,
    buildCumulative_terminal input target cursor terminal .rule4a fuel,
    buildCumulative_terminal input target cursor terminal .rule4cNoReference fuel]
  rfl

/-- The executable alternative-list compiler returns the single canonical terminal reading. -/
theorem buildReadings_terminal (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (terminal : input.executableLocalizedRerootChildren? cursor = some [])
    (fuel : Nat) :
    input.buildLocalizedRerootRule4bcReadingsExec? target (fun _ _ => none) fuel cursor [none] =
      some [terminalReading input cursor.occurrence.1.node] := by
  simp only [buildLocalizedRerootRule4bcReadingsExec?, option_some_bind_apply,
    buildReading_none_terminal input target cursor terminal fuel]

/-- The executable compound Rules-4b/4c compiler returns the canonical terminal compound key. -/
theorem buildCompound4bc_terminal (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (terminal : input.executableLocalizedRerootChildren? cursor = some [])
    (fuel : Nat) :
    input.buildLocalizedRerootCompoundRule4bcKeyExec? target (fun _ _ => none) fuel cursor =
      some (terminalCompound4bc input cursor.occurrence.1.node) := by
  simp only [buildLocalizedRerootCompoundRule4bcKeyExec?, option_some_bind_apply,
    buildCumulative_terminal input target cursor terminal .rule4a fuel,
    terminalCumulativeKey, terminalCompound4bc, List.isEmpty_nil, if_true,
    localizedRule4bReferencesFromRankedLabels, localizedFirstChiralRankPopulation,
    localizedFirstChiralRankPopulationInLayer, localizedRule4bReferencesFromPopulation,
    localizedRule4bcReferenceAlternatives, constitutionalRule4bReferenceCountPriority,
    buildReadings_terminal input target cursor terminal fuel]

/-- The executable Rule-5 reading compiler returns the canonical terminal common reading. -/
theorem buildRule5Reading_terminal (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (terminal : input.executableLocalizedRerootChildren? cursor = some [])
    (fuel : Nat) :
    input.buildLocalizedRerootRule5ReadingExec? target (fun _ _ => none) fuel cursor
        (terminalReading input cursor.occurrence.1.node) =
      some (terminalRule5Reading input cursor.occurrence.1.node) := by
  simp only [buildLocalizedRerootRule5ReadingExec?, option_some_bind_apply, localizedRule5StageFor,
    terminalReading,
    buildCumulative_terminal input target cursor terminal (.rule5NoRule4bReference .R) fuel,
    buildCumulative_terminal input target cursor terminal (.rule5NoRule4bReference .S) fuel]
  rfl

/-- The executable Rule-5 reading-list compiler returns the single canonical terminal reading. -/
theorem buildRule5Readings_terminal (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (terminal : input.executableLocalizedRerootChildren? cursor = some [])
    (fuel : Nat) :
    input.buildLocalizedRerootRule5ReadingsExec? target (fun _ _ => none) fuel cursor
        [terminalReading input cursor.occurrence.1.node] =
      some [terminalRule5Reading input cursor.occurrence.1.node] := by
  simp only [buildLocalizedRerootRule5ReadingsExec?, option_some_bind_apply,
    buildRule5Reading_terminal input target cursor terminal fuel]

/-- The executable through-Rule-5 compound compiler returns the canonical terminal compound key. -/
theorem buildCompound45_terminal (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (terminal : input.executableLocalizedRerootChildren? cursor = some []) (fuel : Nat) :
    input.buildLocalizedRerootCompoundRule45KeyExec? target (fun _ _ => none) fuel cursor =
      some (terminalCompound45 input cursor.occurrence.1.node) := by
  simp only [buildLocalizedRerootCompoundRule45KeyExec?, option_some_bind_apply,
    terminalCompound45, terminalCompound4bc,
    buildCompound4bc_terminal input target cursor terminal fuel,
    buildRule5Readings_terminal input target cursor terminal fuel]

/-! ## Self-comparison of identical descriptor layers -/

private theorem witnessTie_compareNat_self (value : Nat) :
    OfficialRuleMajorKey.compareNat value value = Ordering.eq := by
  unfold OfficialRuleMajorKey.compareNat
  exact Std.ReflOrd.compare_self

private theorem witnessTie_list_compareLex_self {α : Type*} (cmp : α → α → Ordering)
    (refl : ∀ value, cmp value value = Ordering.eq) :
    ∀ values : List α, List.compareLex cmp values values = Ordering.eq
  | [] => rfl
  | value :: values => by
      rw [List.compareLex_cons_cons, refl value]
      exact witnessTie_list_compareLex_self cmp refl values

private theorem witnessTie_compareSparseEntry_self {α : Type*} (cmp : α → α → Ordering)
    (refl : ∀ value, cmp value value = Ordering.eq)
    (entry : OfficialSparseEntry α) :
    OfficialRuleMajorKey.compareSparseEntry cmp entry entry = Ordering.eq := by
  rcases entry with ⟨path, observation⟩
  have pathEqual :
      Ordering.byKey Prod.fst (flip (List.compareLex OfficialRuleMajorKey.compareNat))
          (path, observation) (path, observation) = Ordering.eq := by
    show List.compareLex OfficialRuleMajorKey.compareNat path path = Ordering.eq
    exact witnessTie_list_compareLex_self OfficialRuleMajorKey.compareNat
      witnessTie_compareNat_self path
  have observationEqual :
      Ordering.byKey Prod.snd cmp (path, observation) (path, observation) = Ordering.eq := by
    show cmp observation observation = Ordering.eq
    exact refl observation
  unfold OfficialRuleMajorKey.compareSparseEntry
  simp only [compareLex]
  rw [pathEqual, observationEqual]
  rfl

private theorem witnessTie_compareSparseLayer_self {α : Type*} (cmp : α → α → Ordering)
    (refl : ∀ value, cmp value value = Ordering.eq)
    (layer : List (OfficialSparseEntry α)) :
    OfficialRuleMajorKey.compareSparseLayer cmp layer layer = Ordering.eq :=
  witnessTie_list_compareLex_self (OfficialRuleMajorKey.compareSparseEntry cmp)
    (fun entry => witnessTie_compareSparseEntry_self cmp refl entry) layer

private theorem witnessTie_compareSparseLayers_self {α : Type*} (cmp : α → α → Ordering)
    (refl : ∀ value, cmp value value = Ordering.eq)
    (layers : List (List (OfficialSparseEntry α))) :
    OfficialRuleMajorKey.compareSparseLayers cmp layers layers = Ordering.eq :=
  witnessTie_list_compareLex_self (OfficialRuleMajorKey.compareSparseLayer cmp)
    (fun layer => witnessTie_compareSparseLayer_self cmp refl layer) layers

private theorem witnessTie_compare_zero : compare (0 : Nat) 0 = Ordering.eq := by
  decide

/-- Identical canonical terminal descriptors compare equal. -/
private theorem terminalDescriptor_compare_eq (input : CertifiedLocalizedCIPInput)
    (first second : OfficialCIPNode input.Atom) (stage : LocalizedCumulativeRule45Stage) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
      (terminalCumulativeKey input first stage).descriptor
      (terminalCumulativeKey input second stage).descriptor = Ordering.eq := by
  unfold terminalCumulativeKey
  exact witnessTie_compareSparseLayers_self compareLocalizedCumulativeRule45Priority
    (fun value => witnessTie_list_compareLex_self OfficialRuleMajorKey.compareNat
      witnessTie_compareNat_self value) _

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
    witnessTie_compareSparseLayers_self compareLocalizedCumulativeRule45Priority
      (fun value => witnessTie_list_compareLex_self OfficialRuleMajorKey.compareNat
        witnessTie_compareNat_self value)]
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
    witnessTie_compare_zero,
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

/-- Two canonical terminal compound through-Rule-5 keys with equal constitutional comparison tie.
This is the executive tie checked by `TerminalReferencePair.rule45Tied`. -/
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

/-! ## The production two-terminal frame at the descriptor budget -/

/-- An own local spelling of the `Option` bind equation, so the frame computation reduces without
importing private lemmas. -/
private theorem witnessTie_option_some_bind_apply {α β : Type} (value : α)
    (continuation : α → Option β) :
    (some value : Option α) >>= continuation = continuation value :=
  rfl

/-- The descriptor-bearing evaluation budget is strictly positive. -/
theorem descriptorFuel_positive (carrierFuel : Nat) :
    0 < localizedDescriptorBearingRule3EvaluationFuel carrierFuel := by
  unfold localizedDescriptorBearingRule3EvaluationFuel
  dsimp only
  have positive : 0 < 2 * (carrierFuel + 1) + 1 := by omega
  exact Nat.mul_pos positive positive

/-- The canonical terminal frame value produced by the production two-terminal computation. -/
def frame1Value : localizedSource.LocalizedRule3CanonicalKeyFrame :=
  { rawKeys := [terminalRule3Key localizedSource h4, terminalRule3Key localizedSource h5]
    coupled := false
    excluded := localizedSource.localizedRule3SharedPhysicalUnits
      [terminalRule3Key localizedSource h4, terminalRule3Key localizedSource h5]
    keys := [terminalRule3Key localizedSource h4, terminalRule3Key localizedSource h5] }

/-- The actual production frame of the two terminal hydrogens at the descriptor budget: both
passes retain exactly the two canonical terminal Rule-3 keys, and a two-key frame can only resolve
to ordinary shared-unit cancellation (it has no coupled matching). -/
theorem frameExec_c1_eq :
    localizedSource.buildLocalizedExtendedShortCircuitRule3FrameExec?
        c1.occurrence (fun _ _ => none)
        (localizedDescriptorBearingRule3EvaluationFuel fuel) [h4, h5] =
      some frame1Value := by
  have positive := descriptorFuel_positive fuel
  cases hbudget : localizedDescriptorBearingRule3EvaluationFuel fuel with
  | zero => omega
  | succ budget =>
      unfold buildLocalizedExtendedShortCircuitRule3FrameExec?
      simp only [List.mapM_cons, List.mapM_nil, Option.pure_def,
        witnessTie_option_some_bind_apply,
        terminalRule3Key_computed localizedSource c1.occurrence (fun _ _ => none) h4
          h4_terminal h4_nonunit budget [],
        terminalRule3Key_computed localizedSource c1.occurrence (fun _ _ => none) h5
          h5_terminal h5_nonunit budget []]
      have resolution :
          localizedSource.localizedRule3CoupledTopologyResolutionExec?
              [terminalRule3Key localizedSource h4, terminalRule3Key localizedSource h5] =
            some .ordinary := by
        rw [localizedRule3CoupledTopologyResolutionExec?_eq_original]
        exact localizedSource.localizedRule3CoupledTopologyResolution?_eq_ordinary_of_length_ne_four
          _ (by simp)
      rw [resolution]
      simp only [witnessTie_option_some_bind_apply,
        localizedRule3CoupledExcludedPhysicalUnits]
      rw [terminalRule3Key_computed localizedSource c1.occurrence (fun _ _ => none) h4
          h4_terminal h4_nonunit budget
          (localizedSource.localizedRule3SharedPhysicalUnits
            [terminalRule3Key localizedSource h4, terminalRule3Key localizedSource h5]),
        terminalRule3Key_computed localizedSource c1.occurrence (fun _ _ => none) h5
          h5_terminal h5_nonunit budget
          (localizedSource.localizedRule3SharedPhysicalUnits
            [terminalRule3Key localizedSource h4, terminalRule3Key localizedSource h5])]
      rfl

/-! ## Carbon continuations are not leaves -/

/-- The second carbon has at least one executable child (its hydrogen `atom6`), so its intended
child list is a genuine cons and the terminal-reference check cannot treat it as terminal. -/
theorem c2_children?_eq_some_cons :
    ∃ first rest, localizedSource.executableLocalizedRerootChildren? c2 =
      some (first :: rest) := by
  obtain ⟨children, childCursor, computed, memChild, _frameEq⟩ :=
    localizedSource.exists_mem_localizedRerootChildren_of_executable_child
      (cursor := c2) (nonduplicate := by decide) (positive := by decide)
      (child := c2NodeH6) (slot := 1)
      (childAtSlot := by
        show (c2NodeH6, 1) ∈
          (localizedSource.executableOfficialCIPChildren node2).zipIdx
        rw [c2Children_eq]; decide)
      (notIncoming := by
        intro previous h
        rw [c2_previous] at h
        cases h
        decide)
  have childrenEq : children =
      localizedSource.executableLocalizedRerootChildren c2 := by
    apply Option.some.inj
    exact computed.symm.trans
      (localizedSource.localizedRerootChildren?_eq_some_executable c2)
  have nonempty : children ≠ [] := by
    intro empty
    rw [empty] at memChild
    simp at memChild
  cases children with
  | nil => exact absurd rfl nonempty
  | cons first rest =>
      exact ⟨first, rest, by
        rw [localizedSource.executableLocalizedRerootChildren?_eq_some, ← childrenEq]⟩

/-- The third carbon has at least one executable child (its hydrogen `atom8`). -/
theorem c3_children?_eq_some_cons :
    ∃ first rest, localizedSource.executableLocalizedRerootChildren? c3 =
      some (first :: rest) := by
  obtain ⟨children, childCursor, computed, memChild, _frameEq⟩ :=
    localizedSource.exists_mem_localizedRerootChildren_of_executable_child
      (cursor := c3) (nonduplicate := by decide) (positive := by decide)
      (child := c3NodeH8) (slot := 1)
      (childAtSlot := by
        show (c3NodeH8, 1) ∈
          (localizedSource.executableOfficialCIPChildren node3).zipIdx
        rw [c3Children_eq]; decide)
      (notIncoming := by
        intro previous h
        rw [c3_previous] at h
        cases h
        decide)
  have childrenEq : children =
      localizedSource.executableLocalizedRerootChildren c3 := by
    apply Option.some.inj
    exact computed.symm.trans
      (localizedSource.localizedRerootChildren?_eq_some_executable c3)
  have nonempty : children ≠ [] := by
    intro empty
    rw [empty] at memChild
    simp at memChild
  cases children with
  | nil => exact absurd rfl nonempty
  | cons first rest =>
      exact ⟨first, rest, by
        rw [localizedSource.executableLocalizedRerootChildren?_eq_some, ← childrenEq]⟩

/-! ## The accepted right endpoint of the first carbon -/

/-- The actual certificate produced by the terminal-reference check on the first carbon's right
endpoint.  Every field is a computation already proved above; the certificate is a *result*, not an
assumption. -/
def certificate1 :
    TerminalReferencePair localizedSource c1.occurrence (fun _ _ => none) atom1 atom0
      rightCursor1 :=
  { first := atom4
    second := atom5
    candidates := substituents_1_0
    firstCursor := h4
    secondCursor := h5
    firstComputed := refExec_h4
    secondComputed := refExec_h5
    firstChildren := h4_terminal
    secondChildren := h5_terminal
    firstNonunit := h4_nonunit
    secondNonunit := h5_nonunit
    labelEq := labelEq_h4_h5
    distanceEq := distanceEq_h4_h5
    firstRule45 := terminalCompound45 localizedSource c1NodeH4
    secondRule45 := terminalCompound45 localizedSource c1NodeH5
    firstRule45Computed :=
      buildCompound45_terminal localizedSource c1.occurrence h4 h4_terminal
        (localizedOccurrenceRerootEvaluationFuel fuel)
    secondRule45Computed :=
      buildCompound45_terminal localizedSource c1.occurrence h5 h5_terminal
        (localizedOccurrenceRerootEvaluationFuel fuel)
    rule45Tied :=
      terminalCompound45_compare_eq localizedSource c1NodeH4 c1NodeH5
        (officialRuleMajorRootKey_compare_eq_of_label_distance localizedSource h4 h5
          labelEq_h4_h5 distanceEq_h4_h5)
    frame := frame1Value
    frameComputed := frameExec_c1_eq }

/-- The staged terminal-reference check accepts the right (hydrogen) endpoint of the first carbon.
This is an equality with an explicitly constructed certificate, so no certificate is assumed. -/
theorem terminalReferencePair_right1_eq_some :
    terminalReferencePair? localizedSource c1.occurrence (fun _ _ => none) atom1 atom0
        rightCursor1 =
      some certificate1 := by
  unfold terminalReferencePair?
  split
  · rename_i first second candidatesEq
    rw [substituents_1_0] at candidatesEq
    simp at candidatesEq
    obtain ⟨hfirst, hsecond⟩ := candidatesEq
    subst first
    subst second
    split
    · rename_i firstComputedEq
      rw [refExec_h4] at firstComputedEq
      simp at firstComputedEq
    · rename_i firstCursor firstComputedEq
      rw [refExec_h4] at firstComputedEq
      simp at firstComputedEq
      subst firstCursor
      split
      · rename_i secondComputedEq
        rw [refExec_h5] at secondComputedEq
        simp at secondComputedEq
      · rename_i secondCursor secondComputedEq
        rw [refExec_h5] at secondComputedEq
        simp at secondComputedEq
        subst secondCursor
        split
        · rename_i firstChildrenEq
          split
          · rename_i secondChildrenEq
            split
            · rename_i firstNonunitProof
              split
              · rename_i secondNonunitProof
                split
                · rename_i labelEqProof
                  split
                  · rename_i distanceEqProof
                    split
                    · rename_i firstRule45ComputedEq
                      rw [buildCompound45_terminal localizedSource c1.occurrence h4 h4_terminal
                            (localizedOccurrenceRerootEvaluationFuel fuel)] at firstRule45ComputedEq
                      simp at firstRule45ComputedEq
                    · rename_i firstRule45 firstRule45ComputedEq
                      rw [buildCompound45_terminal localizedSource c1.occurrence h4 h4_terminal
                            (localizedOccurrenceRerootEvaluationFuel fuel)] at firstRule45ComputedEq
                      simp at firstRule45ComputedEq
                      subst firstRule45
                      split
                      · rename_i secondRule45ComputedEq
                        rw [buildCompound45_terminal localizedSource c1.occurrence h5 h5_terminal
                              (localizedOccurrenceRerootEvaluationFuel fuel)] at secondRule45ComputedEq
                        simp at secondRule45ComputedEq
                      · rename_i secondRule45 secondRule45ComputedEq
                        rw [buildCompound45_terminal localizedSource c1.occurrence h5 h5_terminal
                              (localizedOccurrenceRerootEvaluationFuel fuel)] at secondRule45ComputedEq
                        simp at secondRule45ComputedEq
                        subst secondRule45
                        split
                        · split
                          · rename_i frameComputedEq
                            rw [frameExec_c1_eq] at frameComputedEq
                            simp at frameComputedEq
                          · rename_i frame frameComputedEq
                            rw [frameExec_c1_eq] at frameComputedEq
                            simp at frameComputedEq
                            subst frame
                            rfl
                        · rename_i tiedNeg
                          exact (tiedNeg
                            (terminalCompound45_compare_eq localizedSource c1NodeH4 c1NodeH5
                              (officialRuleMajorRootKey_compare_eq_of_label_distance localizedSource
                                h4 h5 labelEq_h4_h5 distanceEq_h4_h5))).elim
                  · rename_i distanceNeg
                    exact (distanceNeg distanceEq_h4_h5).elim
                · rename_i labelNeg
                  exact (labelNeg labelEq_h4_h5).elim
              · rename_i secondNonunitNeg
                exact (secondNonunitNeg h5_nonunit).elim
            · rename_i firstNonunitNeg
              exact (firstNonunitNeg h4_nonunit).elim
          · rename_i secondChildrenNeg
            exact (secondChildrenNeg h5_terminal).elim
        · rename_i firstChildrenNeg
          exact (firstChildrenNeg h4_terminal).elim
  · rename_i candidatesNeg
    exact (candidatesNeg atom4 atom5 substituents_1_0).elim

/-- The staged terminal-reference check rejects the left (sulfur-side carbon) endpoint of the first
carbon, because both reference cursors are real carbons with executable children.  This is the
mirror-image check, computed rather than assumed. -/
theorem terminalReferencePair_left1_eq_none :
    terminalReferencePair? localizedSource c1.occurrence (fun _ _ => none) atom0 atom1
        leftCursor1 = none := by
  obtain ⟨first, rest, children⟩ := c2_children?_eq_some_cons
  unfold terminalReferencePair?
  split
  · rename_i candFirst candSecond candidatesEq
    rw [substituents_0_1] at candidatesEq
    simp at candidatesEq
    obtain ⟨hfirst, hsecond⟩ := candidatesEq
    subst candFirst
    subst candSecond
    split
    · rename_i firstComputedEq
      rfl
    · rename_i firstCursor firstComputedEq
      rw [refExec_c2] at firstComputedEq
      simp at firstComputedEq
      subst firstCursor
      split
      · rename_i secondComputedEq
        rfl
      · rename_i secondCursor secondComputedEq
        rw [refExec_c3] at secondComputedEq
        simp at secondComputedEq
        subst secondCursor
        split
        · rename_i firstChildrenEq
          rw [children] at firstChildrenEq
          simp at firstChildrenEq
        · rfl
  · rename_i candidatesNeg
    exact (candidatesNeg atom2 atom3 substituents_0_1).elim

/-! ## The second cycle origin: the same sulfur-double-bond endpoint machinery at atom `2` -/

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

/-- The declarative meaning of `topology2`, component by component. -/
theorem topology2_spec :
    localizedSource.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame c2.occurrence topology2 := by
  refine ⟨rfl, rfl, rfl, by decide, carrierParent_c2, rfl, rfl, rfl, rfl⟩

/-- Physical endpoint recovery at the second carbon. -/
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
        show (node3, 4) ∈ (localizedSource.executableOfficialCIPChildren rootNode).zipIdx
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

/-- Readiness of the second carbon endpoint. -/
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

/-! ## Real hydrogen leaves of the second carbon have no executable children -/

@[simp] theorem h6_parent : h6.occurrence.1.node.parent? = some atom2 := rfl
@[simp] theorem h7_parent : h7.occurrence.1.node.parent? = some atom2 := rfl

theorem h6_children_nil :
    localizedSource.executableLocalizedRerootChildren h6 = [] := by
  apply executableChildren_nil_of_officialChildren_nil localizedSource rightCursor2 h6
    (incoming := rfl) (slot := 1) (address := rfl) (nonduplicate := by decide)
  unfold executableOfficialCIPChildren
  simp only [executableOfficialChildCopies, executableOfficialNeighborCopies,
    neighborSort_eq, atom2]
  decide

theorem h7_children_nil :
    localizedSource.executableLocalizedRerootChildren h7 = [] := by
  apply executableChildren_nil_of_officialChildren_nil localizedSource rightCursor2 h7
    (incoming := rfl) (slot := 2) (address := rfl) (nonduplicate := by decide)
  unfold executableOfficialCIPChildren
  simp only [executableOfficialChildCopies, executableOfficialNeighborCopies,
    neighborSort_eq, atom2]
  decide

theorem h6_terminal :
    localizedSource.executableLocalizedRerootChildren? h6 = some [] := by
  rw [executableLocalizedRerootChildren?_eq_some, h6_children_nil]

theorem h7_terminal :
    localizedSource.executableLocalizedRerootChildren? h7 = some [] := by
  rw [executableLocalizedRerootChildren?_eq_some, h7_children_nil]

/-- A hydrogen cannot be on an order-two bond to its parent carbon. -/
theorem h6_nonunit :
    ¬ localizedSource.LocalizedOccurrenceHasRule3DoubleBondEdge h6.occurrence := by
  rintro ⟨_, current, parent, currentEq, parentEq, bondEq⟩
  rw [h6_current, Option.some.injEq] at currentEq
  rw [h6_parent, Option.some.injEq] at parentEq
  subst currentEq
  subst parentEq
  exact absurd bondEq (by decide)

theorem h7_nonunit :
    ¬ localizedSource.LocalizedOccurrenceHasRule3DoubleBondEdge h7.occurrence := by
  rintro ⟨_, current, parent, currentEq, parentEq, bondEq⟩
  rw [h7_current, Option.some.injEq] at currentEq
  rw [h7_parent, Option.some.injEq] at parentEq
  subst currentEq
  subst parentEq
  exact absurd bondEq (by decide)

/-- Both hydrogens of the second carbon have the same official root label. -/
theorem labelEq_h6_h7 :
    localizedSource.moleculeGraph.officialNodeAtomLabel h6.occurrence.1.node =
      localizedSource.moleculeGraph.officialNodeAtomLabel h7.occurrence.1.node := by
  decide

/-- Both hydrogens of the second carbon are at the same Rule-1b root distance. -/
theorem distanceEq_h6_h7 :
    h6.occurrence.1.node.rule1bRootDistance =
      h7.occurrence.1.node.rule1bRootDistance := by
  decide

/-- The first carbon has at least one executable child (its hydrogen `atom4`), so it is not a
terminal leaf either. -/
theorem c1_children?_eq_some_cons :
    ∃ first rest, localizedSource.executableLocalizedRerootChildren? c1 =
      some (first :: rest) := by
  obtain ⟨children, computed, mem, _derived⟩ := exists_children_h4
  have executableEq := localizedSource.localizedRerootChildren?_eq_some_executable rightCursor1
  have childrenEq : children = localizedSource.executableLocalizedRerootChildren rightCursor1 :=
    (Option.some.injEq _ _).mp (computed.symm.trans executableEq)
  have nonempty : children ≠ [] := by
    intro empty
    rw [empty] at mem
    simp at mem
  cases children with
  | nil => exact absurd rfl nonempty
  | cons first rest =>
      exact ⟨first, rest, by
        rw [show c1 = rightCursor1 from rfl]
        rw [localizedSource.executableLocalizedRerootChildren?_eq_some, ← childrenEq]⟩

/-! ## The guarded node at the first cycle origin -/

/-- The production terminal guard accepts the right (hydrogen) endpoint of the first carbon after
actually rejecting the left (sulfur-side carbon) endpoint. -/
theorem guard_c1 :
    localizedRule3TerminalGuard? localizedSource c1.occurrence (fun _ _ => none) topology1 =
      some (.right certificate1) := by
  simp only [localizedRule3TerminalGuard?, topology1, terminalReferencePair_left1_eq_none,
    terminalReferencePair_right1_eq_some]

/-- The direct nonstereogenic identity emitted by the accepted guard at the first carbon. -/
def identity1 : LocalizedRule3TerminalGuardedIdentity localizedSource fuel :=
  { topology := topology1
    side := .right }

/-- The actual reduced callback demand at the first cycle origin is literally empty. -/
theorem requests_c1_eq_nil :
    rule3TerminalGuardedNodeCallbackRequests localizedSource c1.occurrence c1.occurrence
        (fun _ _ => none) = [] := by
  obtain ⟨ordinaryCertificate, ordinaryRoute⟩ := ordinaryRoute_c1_some
  exact rule3TerminalGuardedNodeCallbackRequests_eq_nil_of_guard localizedSource c1.occurrence
    c1.occurrence (fun _ _ => none) topology1 (.right certificate1) oddRoute_c1_eq_none
    ordinaryRoute physical_c1 guard_c1

/-- The actual guarded evaluator at the first cycle origin emits the direct identity. -/
theorem guardExec_c1 :
    localizedRule3TerminalGuardedNodeWithExec? localizedSource c1.occurrence c1.occurrence
        (fun _ _ => none) (fun _ => none) [] =
      some (some (.direct identity1)) := by
  obtain ⟨ordinaryCertificate, ordinaryRoute⟩ := ordinaryRoute_c1_some
  simp only [localizedRule3TerminalGuardedNodeWithExec?, oddRoute_c1_eq_none, ordinaryRoute,
    physical_c1, guard_c1, identity1, LocalizedRule3TerminalGuardedIdentity.physicalUnitId,
    List.contains_nil, LocalizedRule3TerminalGuardWitness.side]
  rfl

/-- The guarded evaluator at the first cycle origin is independent of an arbitrary callback. -/
theorem guardExec_c1_callback_independent
    (callback : List (localizedSource.LocalizedRerootCursor fuel) →
      Option localizedSource.LocalizedRule3CanonicalKeyFrame) :
    localizedRule3TerminalGuardedNodeWithExec? localizedSource c1.occurrence c1.occurrence
        (fun _ _ => none) callback [] =
      some (some (.direct identity1)) := by
  obtain ⟨ordinaryCertificate, ordinaryRoute⟩ := ordinaryRoute_c1_some
  rw [localizedRule3TerminalGuardedNodeWithExec?_guard_callback_independent localizedSource
    c1.occurrence c1.occurrence (fun _ _ => none) topology1 (.right certificate1)
    callback (fun _ => none) [] oddRoute_c1_eq_none ordinaryRoute physical_c1 guard_c1]
  exact guardExec_c1

/-- The common observable of the emitted identity is exactly the physical endpoint pair of the
double bond with nonstereogenic geometry; no opposite reference is projected. -/
theorem guardObservable_c1 :
    (LocalizedRule3TerminalGuardedNodeResult.direct identity1).observable =
      { left := atom0
        right := atom1
        geometry := OfficialRule3Geometry.nonstereogenic } :=
  rfl

/-- The physical unit identity of the emitted identity is the canonical ordered pair of the actual
endpoint atoms. -/
theorem guardPhysicalUnitId_c1 :
    identity1.physicalUnitId =
      localizedSource.localizedRule3PhysicalUnitId atom0 atom1 :=
  rfl

/-! ## The two-terminal computation and certificate at the second cycle origin -/

/-- The canonical terminal frame value produced by the production two-terminal computation at the
second carbon. -/
def frame2Value : localizedSource.LocalizedRule3CanonicalKeyFrame :=
  { rawKeys := [terminalRule3Key localizedSource h6, terminalRule3Key localizedSource h7]
    coupled := false
    excluded := localizedSource.localizedRule3SharedPhysicalUnits
      [terminalRule3Key localizedSource h6, terminalRule3Key localizedSource h7]
    keys := [terminalRule3Key localizedSource h6, terminalRule3Key localizedSource h7] }

/-- The actual production frame of the two terminal hydrogens of the second carbon at the
descriptor budget. -/
theorem frameExec_c2_eq :
    localizedSource.buildLocalizedExtendedShortCircuitRule3FrameExec?
        c2.occurrence (fun _ _ => none)
        (localizedDescriptorBearingRule3EvaluationFuel fuel) [h6, h7] =
      some frame2Value := by
  have positive := descriptorFuel_positive fuel
  cases hbudget : localizedDescriptorBearingRule3EvaluationFuel fuel with
  | zero => omega
  | succ budget =>
      unfold buildLocalizedExtendedShortCircuitRule3FrameExec?
      simp only [List.mapM_cons, List.mapM_nil, Option.pure_def,
        witnessTie_option_some_bind_apply,
        terminalRule3Key_computed localizedSource c2.occurrence (fun _ _ => none) h6
          h6_terminal h6_nonunit budget [],
        terminalRule3Key_computed localizedSource c2.occurrence (fun _ _ => none) h7
          h7_terminal h7_nonunit budget []]
      have resolution :
          localizedSource.localizedRule3CoupledTopologyResolutionExec?
              [terminalRule3Key localizedSource h6, terminalRule3Key localizedSource h7] =
            some .ordinary := by
        rw [localizedRule3CoupledTopologyResolutionExec?_eq_original]
        exact localizedSource.localizedRule3CoupledTopologyResolution?_eq_ordinary_of_length_ne_four
          _ (by simp)
      rw [resolution]
      simp only [witnessTie_option_some_bind_apply,
        localizedRule3CoupledExcludedPhysicalUnits]
      rw [terminalRule3Key_computed localizedSource c2.occurrence (fun _ _ => none) h6
          h6_terminal h6_nonunit budget
          (localizedSource.localizedRule3SharedPhysicalUnits
            [terminalRule3Key localizedSource h6, terminalRule3Key localizedSource h7]),
        terminalRule3Key_computed localizedSource c2.occurrence (fun _ _ => none) h7
          h7_terminal h7_nonunit budget
          (localizedSource.localizedRule3SharedPhysicalUnits
            [terminalRule3Key localizedSource h6, terminalRule3Key localizedSource h7])]
      rfl

/-- The actual certificate produced by the terminal-reference check on the second carbon's right
endpoint. -/
def certificate2 :
    TerminalReferencePair localizedSource c2.occurrence (fun _ _ => none) atom2 atom0
      rightCursor2 :=
  { first := atom6
    second := atom7
    candidates := substituents_2_0
    firstCursor := h6
    secondCursor := h7
    firstComputed := refExec_h6
    secondComputed := refExec_h7
    firstChildren := h6_terminal
    secondChildren := h7_terminal
    firstNonunit := h6_nonunit
    secondNonunit := h7_nonunit
    labelEq := labelEq_h6_h7
    distanceEq := distanceEq_h6_h7
    firstRule45 := terminalCompound45 localizedSource c2NodeH6
    secondRule45 := terminalCompound45 localizedSource c2NodeH7
    firstRule45Computed :=
      buildCompound45_terminal localizedSource c2.occurrence h6 h6_terminal
        (localizedOccurrenceRerootEvaluationFuel fuel)
    secondRule45Computed :=
      buildCompound45_terminal localizedSource c2.occurrence h7 h7_terminal
        (localizedOccurrenceRerootEvaluationFuel fuel)
    rule45Tied :=
      terminalCompound45_compare_eq localizedSource c2NodeH6 c2NodeH7
        (officialRuleMajorRootKey_compare_eq_of_label_distance localizedSource h6 h7
          labelEq_h6_h7 distanceEq_h6_h7)
    frame := frame2Value
    frameComputed := frameExec_c2_eq }

/-- The staged terminal-reference check rejects the left (sulfur-side carbon) endpoint of the
second carbon, because the first reference cursor is the real carbon `atom1` with executable
children. -/
theorem terminalReferencePair_left2_eq_none :
    terminalReferencePair? localizedSource c2.occurrence (fun _ _ => none) atom0 atom2
        leftCursor2 = none := by
  obtain ⟨first, rest, children⟩ := c1_children?_eq_some_cons
  unfold terminalReferencePair?
  split
  · rename_i candFirst candSecond candidatesEq
    rw [substituents_0_2] at candidatesEq
    simp at candidatesEq
    obtain ⟨hfirst, hsecond⟩ := candidatesEq
    subst candFirst
    subst candSecond
    split
    · rename_i firstComputedEq
      rfl
    · rename_i firstCursor firstComputedEq
      rw [refExec_left2_c1] at firstComputedEq
      simp at firstComputedEq
      subst firstCursor
      split
      · rename_i secondComputedEq
        rfl
      · rename_i secondCursor secondComputedEq
        rw [refExec_left2_c3] at secondComputedEq
        simp at secondComputedEq
        subst secondCursor
        split
        · rename_i firstChildrenEq
          rw [children] at firstChildrenEq
          simp at firstChildrenEq
        · rfl
  · rename_i candidatesNeg
    exact (candidatesNeg atom1 atom3 substituents_0_2).elim

/-- The staged terminal-reference check accepts the right (hydrogen) endpoint of the second carbon
with the actual computed certificate. -/
theorem terminalReferencePair_right2_eq_some :
    terminalReferencePair? localizedSource c2.occurrence (fun _ _ => none) atom2 atom0
        rightCursor2 =
      some certificate2 := by
  unfold terminalReferencePair?
  split
  · rename_i first second candidatesEq
    rw [substituents_2_0] at candidatesEq
    simp at candidatesEq
    obtain ⟨hfirst, hsecond⟩ := candidatesEq
    subst first
    subst second
    split
    · rename_i firstComputedEq
      rw [refExec_h6] at firstComputedEq
      simp at firstComputedEq
    · rename_i firstCursor firstComputedEq
      rw [refExec_h6] at firstComputedEq
      simp at firstComputedEq
      subst firstCursor
      split
      · rename_i secondComputedEq
        rw [refExec_h7] at secondComputedEq
        simp at secondComputedEq
      · rename_i secondCursor secondComputedEq
        rw [refExec_h7] at secondComputedEq
        simp at secondComputedEq
        subst secondCursor
        split
        · rename_i firstChildrenEq
          split
          · rename_i secondChildrenEq
            split
            · rename_i firstNonunitProof
              split
              · rename_i secondNonunitProof
                split
                · rename_i labelEqProof
                  split
                  · rename_i distanceEqProof
                    split
                    · rename_i firstRule45ComputedEq
                      rw [buildCompound45_terminal localizedSource c2.occurrence h6 h6_terminal
                            (localizedOccurrenceRerootEvaluationFuel fuel)] at firstRule45ComputedEq
                      simp at firstRule45ComputedEq
                    · rename_i firstRule45 firstRule45ComputedEq
                      rw [buildCompound45_terminal localizedSource c2.occurrence h6 h6_terminal
                            (localizedOccurrenceRerootEvaluationFuel fuel)] at firstRule45ComputedEq
                      simp at firstRule45ComputedEq
                      subst firstRule45
                      split
                      · rename_i secondRule45ComputedEq
                        rw [buildCompound45_terminal localizedSource c2.occurrence h7 h7_terminal
                              (localizedOccurrenceRerootEvaluationFuel fuel)] at secondRule45ComputedEq
                        simp at secondRule45ComputedEq
                      · rename_i secondRule45 secondRule45ComputedEq
                        rw [buildCompound45_terminal localizedSource c2.occurrence h7 h7_terminal
                              (localizedOccurrenceRerootEvaluationFuel fuel)] at secondRule45ComputedEq
                        simp at secondRule45ComputedEq
                        subst secondRule45
                        split
                        · split
                          · rename_i frameComputedEq
                            rw [frameExec_c2_eq] at frameComputedEq
                            simp at frameComputedEq
                          · rename_i frame frameComputedEq
                            rw [frameExec_c2_eq] at frameComputedEq
                            simp at frameComputedEq
                            subst frame
                            rfl
                        · rename_i tiedNeg
                          exact (tiedNeg
                            (terminalCompound45_compare_eq localizedSource c2NodeH6 c2NodeH7
                              (officialRuleMajorRootKey_compare_eq_of_label_distance localizedSource
                                h6 h7 labelEq_h6_h7 distanceEq_h6_h7))).elim
                  · rename_i distanceNeg
                    exact (distanceNeg distanceEq_h6_h7).elim
                · rename_i labelNeg
                  exact (labelNeg labelEq_h6_h7).elim
              · rename_i secondNonunitNeg
                exact (secondNonunitNeg h7_nonunit).elim
            · rename_i firstNonunitNeg
              exact (firstNonunitNeg h6_nonunit).elim
          · rename_i secondChildrenNeg
            exact (secondChildrenNeg h7_terminal).elim
        · rename_i firstChildrenNeg
          exact (firstChildrenNeg h6_terminal).elim
  · rename_i candidatesNeg
    exact (candidatesNeg atom6 atom7 substituents_2_0).elim

/-! ## The guarded node at the second cycle origin -/

/-- The production terminal guard accepts the right (hydrogen) endpoint of the second carbon after
actually rejecting the left (sulfur-side carbon) endpoint. -/
theorem guard_c2 :
    localizedRule3TerminalGuard? localizedSource c2.occurrence (fun _ _ => none) topology2 =
      some (.right certificate2) := by
  simp only [localizedRule3TerminalGuard?, topology2, terminalReferencePair_left2_eq_none,
    terminalReferencePair_right2_eq_some]

/-- The direct nonstereogenic identity emitted by the accepted guard at the second carbon. -/
def identity2 : LocalizedRule3TerminalGuardedIdentity localizedSource fuel :=
  { topology := topology2
    side := .right }

/-- The actual reduced callback demand at the second cycle origin is literally empty. -/
theorem requests_c2_eq_nil :
    rule3TerminalGuardedNodeCallbackRequests localizedSource c2.occurrence c2.occurrence
        (fun _ _ => none) = [] := by
  obtain ⟨ordinaryCertificate, ordinaryRoute⟩ := ordinaryRoute_c2_some
  exact rule3TerminalGuardedNodeCallbackRequests_eq_nil_of_guard localizedSource c2.occurrence
    c2.occurrence (fun _ _ => none) topology2 (.right certificate2) oddRoute_c2_eq_none
    ordinaryRoute physical_c2 guard_c2

/-- The actual guarded evaluator at the second cycle origin emits the direct identity. -/
theorem guardExec_c2 :
    localizedRule3TerminalGuardedNodeWithExec? localizedSource c2.occurrence c2.occurrence
        (fun _ _ => none) (fun _ => none) [] =
      some (some (.direct identity2)) := by
  obtain ⟨ordinaryCertificate, ordinaryRoute⟩ := ordinaryRoute_c2_some
  simp only [localizedRule3TerminalGuardedNodeWithExec?, oddRoute_c2_eq_none, ordinaryRoute,
    physical_c2, guard_c2, identity2, LocalizedRule3TerminalGuardedIdentity.physicalUnitId,
    List.contains_nil, LocalizedRule3TerminalGuardWitness.side]
  rfl

/-- The guarded evaluator at the second cycle origin is independent of an arbitrary callback. -/
theorem guardExec_c2_callback_independent
    (callback : List (localizedSource.LocalizedRerootCursor fuel) →
      Option localizedSource.LocalizedRule3CanonicalKeyFrame) :
    localizedRule3TerminalGuardedNodeWithExec? localizedSource c2.occurrence c2.occurrence
        (fun _ _ => none) callback [] =
      some (some (.direct identity2)) := by
  obtain ⟨ordinaryCertificate, ordinaryRoute⟩ := ordinaryRoute_c2_some
  rw [localizedRule3TerminalGuardedNodeWithExec?_guard_callback_independent localizedSource
    c2.occurrence c2.occurrence (fun _ _ => none) topology2 (.right certificate2)
    callback (fun _ => none) [] oddRoute_c2_eq_none ordinaryRoute physical_c2 guard_c2]
  exact guardExec_c2

/-- The common observable of the identity emitted at the second carbon. -/
theorem guardObservable_c2 :
    (LocalizedRule3TerminalGuardedNodeResult.direct identity2).observable =
      { left := atom0
        right := atom2
        geometry := OfficialRule3Geometry.nonstereogenic } :=
  rfl

/-- The physical unit identity of the identity emitted at the second carbon. -/
theorem guardPhysicalUnitId_c2 :
    identity2.physicalUnitId =
      localizedSource.localizedRule3PhysicalUnitId atom0 atom2 :=
  rfl

/-! ## Kernel-authority guards for every export -/

assert_kernel_only source
assert_kernel_only source_structurallyWellFormed
assert_kernel_only source_localizedGraphReady
assert_kernel_only certifiedSource
assert_kernel_only localizedSource
assert_kernel_only input
assert_kernel_only admission
assert_kernel_only fuel
assert_kernel_only fuel_eq
assert_kernel_only atom0
assert_kernel_only atom1
assert_kernel_only atom2
assert_kernel_only atom3
assert_kernel_only atom4
assert_kernel_only atom5
assert_kernel_only atom6
assert_kernel_only atom7
assert_kernel_only atom8
assert_kernel_only atom9
assert_kernel_only sort_of_toFinset_eq
assert_kernel_only neighborSort_eq
assert_kernel_only root
assert_kernel_only root_previous
assert_kernel_only rootNode
assert_kernel_only node1
assert_kernel_only node1d
assert_kernel_only node2
assert_kernel_only node2d
assert_kernel_only node3
assert_kernel_only node3d
assert_kernel_only rootChildren_eq
assert_kernel_only c1Node0
assert_kernel_only c1NodeH4
assert_kernel_only c1NodeH5
assert_kernel_only c1Children_eq
assert_kernel_only c2Node0
assert_kernel_only c2NodeH6
assert_kernel_only c2NodeH7
assert_kernel_only c2Children_eq
assert_kernel_only c3Node0
assert_kernel_only c3NodeH8
assert_kernel_only c3NodeH9
assert_kernel_only c3Children_eq
assert_kernel_only frame1
assert_kernel_only frame2
assert_kernel_only frame3
assert_kernel_only frame1_mem
assert_kernel_only frame2_mem
assert_kernel_only frame3_mem
assert_kernel_only c1
assert_kernel_only c2
assert_kernel_only c3
assert_kernel_only c1_mem
assert_kernel_only c2_mem
assert_kernel_only c3_mem
assert_kernel_only c1_address
assert_kernel_only c2_address
assert_kernel_only c3_address
assert_kernel_only c1_current
assert_kernel_only c2_current
assert_kernel_only c3_current
assert_kernel_only c1_provenance
assert_kernel_only c2_provenance
assert_kernel_only c3_provenance
assert_kernel_only c1_previous
assert_kernel_only c2_previous
assert_kernel_only c3_previous
assert_kernel_only sort_erase_eq
assert_kernel_only explicitSubstituents_eq
assert_kernel_only root_address
assert_kernel_only root_remaining
assert_kernel_only root_node
assert_kernel_only root_current
assert_kernel_only root_provenance
assert_kernel_only node1_parent
assert_kernel_only node1_current
assert_kernel_only node1_provenance
assert_kernel_only node1_not_duplicate
assert_kernel_only carrierParent_c1
assert_kernel_only leftCursor1
assert_kernel_only rightCursor1
assert_kernel_only topology1
assert_kernel_only topology1_spec
assert_kernel_only physical_c1
assert_kernel_only substituents_0_1
assert_kernel_only substituents_1_0
assert_kernel_only leftCursor1_previous
assert_kernel_only leftCursor1_address
assert_kernel_only leftCursor1_remaining
assert_kernel_only leftCursor1_current
assert_kernel_only leftCursor1_provenance
assert_kernel_only rightCursor1_previous
assert_kernel_only rightCursor1_address
assert_kernel_only rightCursor1_remaining
assert_kernel_only rightCursor1_current
assert_kernel_only rightCursor1_provenance
assert_kernel_only exists_children_c2
assert_kernel_only exists_children_c3
assert_kernel_only refExec_c2
assert_kernel_only refExec_c3
assert_kernel_only h4Frame
assert_kernel_only h5Frame
assert_kernel_only h4Frame_mem
assert_kernel_only h5Frame_mem
assert_kernel_only h4
assert_kernel_only h5
assert_kernel_only h4_previous
assert_kernel_only h5_previous
assert_kernel_only h4_current
assert_kernel_only h5_current
assert_kernel_only h4_provenance
assert_kernel_only h5_provenance
assert_kernel_only exists_children_h4
assert_kernel_only exists_children_h5
assert_kernel_only refExec_h4
assert_kernel_only refExec_h5
assert_kernel_only pairReady_left1
assert_kernel_only pairReady_right1
assert_kernel_only ordinaryPairReady_c1
assert_kernel_only edge_c1
assert_kernel_only c2_mem_executableChildren
assert_kernel_only c3_mem_executableChildren
assert_kernel_only axisContinuation_c2
assert_kernel_only axisContinuation_c3
assert_kernel_only c2_ne_c3
assert_kernel_only two_le_length_of_mem_of_mem
assert_kernel_only exists_two_cons_of_two_le_length
assert_kernel_only axisContinuations_two_le
assert_kernel_only axisTopology_c1_branched
assert_kernel_only axisEntry_c1_branched
assert_kernel_only oddRoute_c1_eq_none
assert_kernel_only ordinaryRoute_c1_some
assert_kernel_only executableChildren_nil_of_officialChildren_nil
assert_kernel_only c1NodeH4_parent
assert_kernel_only c1NodeH5_parent
assert_kernel_only c2NodeH6_parent
assert_kernel_only c2NodeH7_parent
assert_kernel_only h4_parent
assert_kernel_only h5_parent
assert_kernel_only h4_children_nil
assert_kernel_only h5_children_nil
assert_kernel_only h4_terminal
assert_kernel_only h5_terminal
assert_kernel_only h4_nonunit
assert_kernel_only h5_nonunit
assert_kernel_only labelEq_h4_h5
assert_kernel_only distanceEq_h4_h5
assert_kernel_only terminalCumulativeKey
assert_kernel_only terminalReading
assert_kernel_only terminalCompound4bc
assert_kernel_only terminalRule5Reading
assert_kernel_only terminalCompound45
assert_kernel_only dependencyLabel_const_none
assert_kernel_only buildCumulative_terminal
assert_kernel_only buildReading_none_terminal
assert_kernel_only buildReadings_terminal
assert_kernel_only buildCompound4bc_terminal
assert_kernel_only buildRule5Reading_terminal
assert_kernel_only buildRule5Readings_terminal
assert_kernel_only buildCompound45_terminal
assert_kernel_only terminalCumulative_compare_eq
assert_kernel_only terminalReadingByRule4b_compare_eq
assert_kernel_only terminalReadingsByRule4b_compare_eq
assert_kernel_only terminalReadingByRule4cDescriptor_compare_eq
assert_kernel_only terminalReadingsByRule4c_compare_eq
assert_kernel_only terminalCompound4bc_compare_eq
assert_kernel_only terminalRule5Descriptor_compare_eq
assert_kernel_only terminalRule5Readings_compare_eq
assert_kernel_only terminalCompound45_compare_eq
assert_kernel_only descriptorFuel_positive
assert_kernel_only frame1Value
assert_kernel_only frameExec_c1_eq
assert_kernel_only c2_children?_eq_some_cons
assert_kernel_only c3_children?_eq_some_cons
assert_kernel_only certificate1
assert_kernel_only terminalReferencePair_right1_eq_some
assert_kernel_only terminalReferencePair_left1_eq_none
assert_kernel_only carrierParent_c2
assert_kernel_only leftCursor2
assert_kernel_only rightCursor2
assert_kernel_only topology2
assert_kernel_only topology2_spec
assert_kernel_only physical_c2
assert_kernel_only leftCursor2_previous
assert_kernel_only leftCursor2_address
assert_kernel_only leftCursor2_remaining
assert_kernel_only leftCursor2_current
assert_kernel_only leftCursor2_provenance
assert_kernel_only rightCursor2_previous
assert_kernel_only rightCursor2_address
assert_kernel_only rightCursor2_remaining
assert_kernel_only rightCursor2_current
assert_kernel_only rightCursor2_provenance
assert_kernel_only substituents_0_2
assert_kernel_only substituents_2_0
assert_kernel_only exists_children_left2_c1
assert_kernel_only exists_children_left2_c3
assert_kernel_only refExec_left2_c1
assert_kernel_only refExec_left2_c3
assert_kernel_only h6Frame
assert_kernel_only h7Frame
assert_kernel_only h6Frame_mem
assert_kernel_only h7Frame_mem
assert_kernel_only h6
assert_kernel_only h7
assert_kernel_only h6_previous
assert_kernel_only h7_previous
assert_kernel_only h6_current
assert_kernel_only h7_current
assert_kernel_only h6_provenance
assert_kernel_only h7_provenance
assert_kernel_only exists_children_h6
assert_kernel_only exists_children_h7
assert_kernel_only refExec_h6
assert_kernel_only refExec_h7
assert_kernel_only pairReady_left2
assert_kernel_only pairReady_right2
assert_kernel_only ordinaryPairReady_c2
assert_kernel_only edge_c2
assert_kernel_only c1_mem_executableChildren2
assert_kernel_only c3_mem_executableChildren2
assert_kernel_only axisContinuation_left2_c1
assert_kernel_only axisContinuation_left2_c3
assert_kernel_only c1_ne_c3
assert_kernel_only axisContinuations_left2_two_le
assert_kernel_only axisTopology_left2_branched
assert_kernel_only axisEntry_c2_branched
assert_kernel_only oddRoute_c2_eq_none
assert_kernel_only ordinaryRoute_c2_some
assert_kernel_only h6_parent
assert_kernel_only h7_parent
assert_kernel_only h6_children_nil
assert_kernel_only h7_children_nil
assert_kernel_only h6_terminal
assert_kernel_only h7_terminal
assert_kernel_only h6_nonunit
assert_kernel_only h7_nonunit
assert_kernel_only labelEq_h6_h7
assert_kernel_only distanceEq_h6_h7
assert_kernel_only c1_children?_eq_some_cons
assert_kernel_only guard_c1
assert_kernel_only identity1
assert_kernel_only requests_c1_eq_nil
assert_kernel_only guardExec_c1
assert_kernel_only guardExec_c1_callback_independent
assert_kernel_only guardObservable_c1
assert_kernel_only guardPhysicalUnitId_c1
assert_kernel_only frame2Value
assert_kernel_only frameExec_c2_eq
assert_kernel_only certificate2
assert_kernel_only terminalReferencePair_left2_eq_none
assert_kernel_only terminalReferencePair_right2_eq_some
assert_kernel_only guard_c2
assert_kernel_only identity2
assert_kernel_only requests_c2_eq_nil
assert_kernel_only guardExec_c2
assert_kernel_only guardExec_c2_callback_independent
assert_kernel_only guardObservable_c2
assert_kernel_only guardPhysicalUnitId_c2

end TetraStereo.OneCenter.LocalizedTerminalGuardedCycleWitness
