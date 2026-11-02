import TetraStereo.OneCenter.LocalizedPreflightDemandDiscovery
import TetraStereo.OneCenter.LocalizedPreflightDemandTotality
import TetraStereo.OneCenter.LocalizedExtendedMandatoryRecursion
import TetraStereo.OneCenter.LocalizedOccurrenceExecutableRoots
import TetraStereo.OneCenter.LocalizedShortCircuitPipeline
import TetraStereo.OneCenter.LocalizedRule3DemandRankProducer
import TetraStereo.OneCenter.LocalizedRule3RouteCompleteness
import TetraStereo.OneCenter.LocalizedPhysicalReferenceUniqueness

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace TetraStereo.OneCenter.LocalizedRetainedDemandCycleKernel

open TetraStereo.OneCenter
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.Certificate.WeightedDemand

/-!
# Kernel certificate for the retained-demand cycle of the ten-atom `S(=CH₂)₃` fixture

This module converts the runtime observations of
`TetraStereo.Examples.LocalizedRetainedDemandCycleProbe` into kernel-checked statements about the
actual executable pipeline.  Nothing here is a new semantic assumption: every concrete fact is
established by reduction of the existing definitions, and every general step is an existing
theorem.

The fixture is the ten-atom source

* sulfur at atom `0`, the three doubly bonded carbons at atoms `1,2,3`, and one hydrogen pair
  (`4,5`), (`6,7`), (`8,9`) on the three carbons;
* no coordinates, no diagram.

This source is *syntactically admitted* by the real admission pipeline.  `graphReady` checks
structural well-formedness (closed shells, known Rule-2 masses, covalent pair records, unique
records); it is **not** a chemical-validity claim.  In particular the sulfur valence sum is six and
the fixture is not asserted to be an ordinary organic molecule.  The negative result below is a
statement about the exact executable localized pipeline on this syntactically admitted input, not a
claim that all intended organic input fails.

## Kernel-reduction note

The executable enumeration of neighbor copies uses `Finset.sort`, which is `Multiset.sort`, whose
body is a well-founded `List.mergeSort` (Lean's runtime replaces it by a `@[csimp]` compiled
version, but the kernel does not unfold it).  Consequently `decide` cannot traverse any term that
still contains a `Finset.sort`.  The lemma `neighborSort_eq` below computes the sorted neighbor
list of *every* atom of the fixture in one kernel proof, using the sort-free characterization
`List.toFinset_sort`; rewriting with it before `decide` makes the whole remaining pipeline
structural and hence kernel-reducible.  This is a proof step, not a compiled constant.
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

/-- The fixture passes the structural admission gate.  This is the Boolean structural predicate,
not a chemical-validity assertion. -/
theorem source_structurallyWellFormed : source.structurallyWellFormed? = true := by
  decide

/-- The fixture passes the localized-graph readiness gate (closed shells, Rule-2 masses, covalent
pair records, unique records). -/
theorem source_localizedGraphReady :
    source.molecule.localizedCIPGraphReady? = true := by
  decide

/-- The certified authoritative input built from the fixture, using the real admission proof
bridges.  The proof fields are propositions and are erased computationally. -/
def certifiedSource : CertifiedAuthoritativeChemicalInput :=
  { input := source
    structurallyWellFormed :=
      (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff source).mp
        source_structurallyWellFormed }

/-- The certified localized input built from the fixture, using the real readiness proof
bridge. -/
def localizedSource : CertifiedLocalizedCIPInput :=
  { certified := certifiedSource
    graphReady :=
      (certifiedSource.input.molecule.localizedCIPGraphReady?_eq_true_iff).mp
        source_localizedGraphReady }

/-- The runtime input of the complete localized evaluator. -/
def input : LocalizedReference.Input :=
  { certified := localizedSource }

/-- **Admission.**  The real source-admission pipeline returns exactly the constructed input.  The
proof is pure reduction of the actual `admitSource?`, `certify?` and `certifyLocalizedCIP?`
definitions; the proof fields of the certified records are propositional and identified by proof
irrelevance. -/
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

/-! ## Kernel computation of the sorted neighbor lists

`Finset.sort` does not reduce in the kernel.  The next two declarations replace it by an explicit
list, once and for all atoms, using the sort-free theorem `List.toFinset_sort`.
-/

/-- If `l` is a nodup, sorted enumeration of `s`, then `s.sort` is `l`. -/
theorem sort_of_toFinset_eq (a : localizedSource.Atom) (l : List localizedSource.Atom)
    (hset : l.toFinset = localizedSource.moleculeGraph.neighborFinset a)
    (hnd : l.Nodup) (hpw : l.Pairwise (· ≤ ·)) :
    (localizedSource.moleculeGraph.neighborFinset a).sort (· ≤ ·) = l := by
  rw [← hset]
  exact (List.toFinset_sort (r := (· ≤ ·)) (l := l) hnd).mpr hpw

/-- The sorted neighbor list of every atom of the fixture.  The right-hand side is a `match` on
the atom value, so it rewrites uniformly at every atom occurrence in any executable term. -/
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

/-! ## Kernel-reduction probes

The key comparison is evaluated by the kernel.  Two reduction behaviours of the actual
definitions decide how the concrete computation is organised: whether the simplifier can unfold a
`Nat`-recursive definition at a literal budget, and whether an `Option` do-block reduces by
`Option.bind_some`.  Both are checked here on the definitions themselves, not assumed. -/

private def literalUnfoldProbe : Nat → Nat
  | 0 => 0
  | n + 1 => n

theorem literalUnfoldProbe_three : literalUnfoldProbe 3 = 2 := by
  simp only [literalUnfoldProbe]

theorem optionBindDoProbe :
    (do let x ← (some 3 : Option Nat); pure (x + 1)) = some 4 := by
  simp

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

/-- **Exact root children.**  The atom-`0` root has exactly the six executable children: one real
copy and one multiple-bond duplicate copy for each of the three doubly bonded carbons.  This is a
kernel computation: the only non-structural operation in it is `Finset.sort`, which
`neighborSort_eq` has already replaced by an explicit list. -/
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

/-- The first carbon occurrence belongs to the molecule-wide carrier, because it is the official
child at slot `0` of the atom-`0` root subtree. -/
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

/-- **Exact membership.**  The first carbon is one of the executable children of the atom-`0`
root.  The proof goes through the existing exact-child recovery theorem: its occurrence frame is
the official child at slot `0`, which is a member of the pinned child list, and any other child
with that frame agrees on the incoming cut as well. -/
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
erase.  This eliminates the second kernel obstruction: `localizedRule3ExplicitSubstituents` sorts
an *erased* neighbor finset, so `neighborSort_eq` alone does not cover it. -/
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

/-- The explicit Rule-3 substituent list of every ordered pair of atoms: the sorted neighbor list
with the partner removed.  The right-hand side is the sorted list erased at the *variable* partner,
so the lemma applies uniformly while the endpoint is still a variable of an unfolded executable
match.  Every `Finset.sort` in the spatial pipeline is thereby removed. -/
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

/-! ## Root coordinate and the two endpoint cursors of the first carbon

The physical endpoint machinery can be driven entirely by its *declarative* completeness
theorems.  No enumeration of the carrier is required: the carrier-parent membership below is a
single `List.mem_filter` fact, and the four reference lookups are constructed from the exact
child-recovery theorem `exists_mem_localizedRerootChildren_of_executable_child`. -/

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

/-- The oriented physical endpoint frame of the double bond `0 = 1`: sulfur on the left, the first
carbon on the right, and each endpoint cursor carrying the other endpoint as its incoming cut. -/
def topology1 : localizedSource.LocalizedRule3PhysicalEndpointCursorFrame fuel :=
  { left := atom0
    right := atom1
    leftCursor := leftCursor1
    rightCursor := rightCursor1 }

/-- The declarative meaning of `topology1`, component by component. -/
theorem topology1_spec :
    localizedSource.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame c1.occurrence topology1 := by
  refine ⟨rfl, rfl, rfl, by decide, carrierParent_c1, rfl, rfl, rfl, rfl⟩

/-- **Physical endpoint recovery.**  The executable physical endpoint frame of the first carbon is
exactly `topology1`. -/
theorem physical_c1 :
    localizedSource.localizedRule3PhysicalEndpointCursorFrameExec? c1.occurrence =
      some topology1 :=
  localizedSource.localizedRule3PhysicalEndpointCursorFrameExec?_eq_some_of_declarative
    c1.occurrence topology1 topology1_spec

/-! ## Diagnostic probe: readiness of the first carbon -/

/-! ## Endpoint substituent lists

`explicitSubstituents_eq` removes every erased sort, so the concrete substituent lists of the
endpoint pairs are pure kernel reduction. -/

theorem substituents_0_1 :
    localizedSource.localizedRule3ExplicitSubstituents atom0 atom1 = [atom2, atom3] := by
  rw [explicitSubstituents_eq]
  rfl

theorem substituents_1_0 :
    localizedSource.localizedRule3ExplicitSubstituents atom1 atom0 = [atom4, atom5] := by
  rw [explicitSubstituents_eq]
  rfl

/-! ## The two endpoint cursors and their declarative reference selections -/

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

/-- **Reference selection at the left endpoint.**  The executable lookup at the sulfur cursor for
atom `2` returns exactly the second-carbon cursor. -/
theorem refExec_c2 :
    localizedSource.localizedRule3ReferenceCursorExec? leftCursor1 atom2 = some c2 := by
  have declarative : localizedSource.DeclarativeLocalizedRule3ReferenceCursor
      leftCursor1 c2 atom2 := by
    obtain ⟨children, computed, mem, derived⟩ := exists_children_c2
    exact ⟨children, computed, derived, mem, rfl, trivial, rfl⟩
  rw [← localizedSource.localizedRule3ReferenceCursor?_eq_localizedRule3ReferenceCursorExec?]
  exact localizedSource.localizedRule3ReferenceCursor?_eq_some_of_declarative
    leftCursor1 c2 atom2 declarative

/-- **Reference selection at the left endpoint.**  The executable lookup at the sulfur cursor for
atom `3` returns exactly the third-carbon cursor. -/
theorem refExec_c3 :
    localizedSource.localizedRule3ReferenceCursorExec? leftCursor1 atom3 = some c3 := by
  have declarative : localizedSource.DeclarativeLocalizedRule3ReferenceCursor
      leftCursor1 c3 atom3 := by
    obtain ⟨children, computed, mem, derived⟩ := exists_children_c3
    exact ⟨children, computed, derived, mem, rfl, trivial, rfl⟩
  rw [← localizedSource.localizedRule3ReferenceCursor?_eq_localizedRule3ReferenceCursorExec?]
  exact localizedSource.localizedRule3ReferenceCursor?_eq_some_of_declarative
    leftCursor1 c3 atom3 declarative

/-! ### The hydrogen children of the first carbon

Their occurrence frames are the exact outward children at addresses `[0,1]` and `[0,2]`, with the
remaining depth decremented once. -/

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

/-- **Reference selection at the right endpoint.**  The executable lookup at the first-carbon
cursor for atom `4` returns the first hydrogen cursor. -/
theorem refExec_h4 :
    localizedSource.localizedRule3ReferenceCursorExec? rightCursor1 atom4 = some h4 := by
  have declarative : localizedSource.DeclarativeLocalizedRule3ReferenceCursor
      rightCursor1 h4 atom4 := by
    obtain ⟨children, computed, mem, derived⟩ := exists_children_h4
    exact ⟨children, computed, derived, mem, rfl, trivial, rfl⟩
  rw [← localizedSource.localizedRule3ReferenceCursor?_eq_localizedRule3ReferenceCursorExec?]
  exact localizedSource.localizedRule3ReferenceCursor?_eq_some_of_declarative
    rightCursor1 h4 atom4 declarative

/-- **Reference selection at the right endpoint.**  The executable lookup at the first-carbon
cursor for atom `5` returns the second hydrogen cursor. -/
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

/-- **Readiness of the first carbon endpoint.**  The executable physical endpoint frame exists and
both oriented endpoint pairs are reference-ready. -/
theorem ordinaryPairReady_c1 :
    localizedSource.ordinaryPairReady c1.occurrence = true := by
  simp only [ordinaryPairReady, physical_c1, topology1, rule3EndpointPairReady,
    substituents_0_1, substituents_1_0, refExec_c2, refExec_c3, refExec_h4, refExec_h5,
    Option.isSome_some]
  rfl

/-! ## The physical route certificate of the first carbon

The first carbon carries a real order-two bond to sulfur, and both real carbon continuations of the
left endpoint cursor are physical order-two continuations.  Hence the cumulated axis entry is the
`branched` constructor, the odd-cumulene route is empty, and the ordinary route certificate is
present.  All of these are proved from the declarative recovery theorems above, without unfolding
the occurrence carrier. -/

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

/-- The executable physical continuations of the left endpoint cursor number at least two: the
second and third carbons are both retained. -/
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
requests: the odd route is absent and the ordinary route certificate is present. -/
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

/-- The root constitutional comparison of the second and third carbons defers: both roots are
carbon atoms. -/
theorem rootCompare_c2_c3 :
    localizedSource.compareLocalizedRerootCursorConstitutionalRoot c2 c3 = .eq := by
  decide

/-- The root constitutional comparison of the two hydrogens defers: both roots are hydrogen
atoms. -/
theorem rootCompare_h4_h5 :
    localizedSource.compareLocalizedRerootCursorConstitutionalRoot h4 h5 = .eq := by
  decide

/-- The left endpoint request of the first carbon is `[[c2, c3]]`, conditional on the constitutional
tie of the two carbon substituents.  The carbon\(-\)carbon comparison is the remaining kernel
computation obligation; no strict outcome is assumed away. -/
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
ties.  This is the retained-demand statement of the cycle kernel: the incoming cut at the sulfur
root does not suppress the two carbon branches, and each oriented endpoint contributes one tied
pair. -/
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

/-! ## The second sulfur--carbon endpoint: the incoming carbon is not cut from the axis

The same physical endpoint machinery is driven at atom `2`.  The incoming cut removes the sulfur
root from the parent side but, exactly as at the first carbon, the two other real carbons remain
physical order-two continuations of the sulfur endpoint.  Thus the second carbon also carries a
branched axis entry, an ordinary route certificate, and a tied carbon request pair. -/

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
`2`; the incoming cut removes the root coordinate, not slot `0`. -/
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
`2`; the incoming cut removes slot `2`, not slot `4`. -/
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
constitutional tie.  The hydrogen tie at the right endpoint is irrelevant to this membership. -/
theorem c1_mem_requests_c2_of_tie
    (tie : localizedSource.compareLocalizedConstitutionalCursors? c1 c3 = some .eq) :
    c1 ∈ (localizedSource.rule3PreflightExtendedNodeCallbackRequests c2.occurrence).flatten := by
  rw [requests_c2_eq, shortSpatial_c2_eq, endpointRequests_0_2_eq_of_tie tie]
  simp

/-! ## Kernel computation of the carbon constitutional keys

The two carbon substituents are constitutionally tied.  The key compiler is recursive in its
budget, and the carrier enumerator contains `Finset.sort`.  Unfolding the actual executable
definitions at a literal budget and replacing each sort by `neighborSort_eq` reduces both keys to a
closed term, which the kernel evaluates.  The small budget `3` already exceeds the height of both
carbon subtrees, so the reduction is local to the two carbon cursors. -/

/-- Eta-expanded form of the per-atom enumerator, so that the simplifier can see it beneath the
partial application used by `List.flatMap`. -/
theorem localizedOccurrencesAtAtom_partial (fuel : Nat) :
    (localizedSource.localizedOccurrencesAtAtom fuel) =
      fun atom => localizedSource.localizedOccurrencesAtAtom fuel atom :=
  rfl

theorem build_c2_three_isSome :
    (localizedSource.buildLocalizedRerootRuleMajorKeyExec? 3 c2).isSome = true := by
  simp only [buildLocalizedRerootRuleMajorKeyExec?, executableLocalizedRerootChildren?,
    executableLocalizedRerootChildren, intendedLocalizedRerootChildFrames,
    localizedRerootNeighborFrames, localizedCarrierParentFrames,
    localizedCarrierOutwardChildFrames, localizedOccurrences,
    localizedOccurrencesAtAtom_partial, localizedOccurrencesAtAtom,
    localizedOccurrenceSubtree, executableOfficialCIPChildren,
    executableOfficialChildCopies, executableOfficialNeighborCopies, neighborSort_eq, fuel]
  decide

theorem build_c3_three_isSome :
    (localizedSource.buildLocalizedRerootRuleMajorKeyExec? 3 c3).isSome = true := by
  simp only [buildLocalizedRerootRuleMajorKeyExec?, executableLocalizedRerootChildren?,
    executableLocalizedRerootChildren, intendedLocalizedRerootChildFrames,
    localizedRerootNeighborFrames, localizedCarrierParentFrames,
    localizedCarrierOutwardChildFrames, localizedOccurrences,
    localizedOccurrencesAtAtom_partial, localizedOccurrencesAtAtom,
    localizedOccurrenceSubtree, executableOfficialCIPChildren,
    executableOfficialChildCopies, executableOfficialNeighborCopies, neighborSort_eq, fuel]
  decide

end TetraStereo.OneCenter.LocalizedRetainedDemandCycleKernel
