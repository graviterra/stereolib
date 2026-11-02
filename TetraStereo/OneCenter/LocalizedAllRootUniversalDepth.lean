import TetraStereo.OneCenter.LocalizedOccurrenceUniversalDepth
import TetraStereo.OneCenter.LocalizedOccurrenceFiniteCarrier

set_option autoImplicit false

/-!
# Universal occurrence-expansion depth at arbitrary atom roots

`LocalizedOccurrenceUniversalDepth` removed fuel truncation for the canonical tetrahedral ligand
roots.  That theorem was stated only for `OfficialCIPNode.rootFromEdge center ligand` with
`center` an automatically detected tetrahedral center.  The present module removes both
specializations: for an *arbitrary* atom root of an *arbitrary* `CertifiedLocalizedCIPInput` the
executable official expansion is complete at the carrier depth `atomCount + 1`, and therefore
every `UnboundedOfficialSubtree` descendant of `OfficialCIPNode.root atom` is stored in every
layer of the shared occurrence carrier with its exact address, provenance node and remaining
depth.

The proof is a direct reuse of the finite simple-history / visited-set frontier theorem
(`MoleculeGraph.officialCIPFrontier_root_eq_nil_card_add_one`, derived from
`officialCIPFrontier_eq_nil_of_activeSimple_length_bound`) together with the existing
permutation transfer between the executable and proof-facing child enumerations.  No new
expansion procedure is introduced, no completeness hypothesis is assumed, and no per-molecule
evidence is required: the only inputs are the `CertifiedLocalizedCIPInput` structure and its
atom.

## Carrier convention (checked off-by-one)

`localizedOccurrencesAtAtom fuel atom` enumerates
`localizedOccurrenceSubtree atom (fuel + 1) [] (root atom)`.  This module fixes

* carrier fuel `fuel = atomCount + 1`, hence
* recursive subtree budget `fuel + 1 = atomCount + 2`.

Completeness is proved at `atomCount + 1`, so every unbounded descendant has address length at
most `atomCount + 1 = budget - 1`.  Consequently its stored remaining depth is
`atomCount + 2 - address.length ≥ 1`: the carrier has not bottomed out at any unbounded
descendant, and the node's executable children are still enumerated.  Addressing is never
lowered to fit a narrower budget; the one extra level is exactly the `fuel + 1` root budget
convention.

## Scope

The result is purely structural occurrence completeness for *all* atom roots, including ring
and multiple-bond duplicate leaves.  It makes no claim about, and is not used to bound, any
Rule 3 callback recursion.
-/

namespace TetraStereo.OneCenter

namespace MoleculeGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The singleton official frontier at an atom root is active-simple: the root is a real node and
its history `[atom]` has no duplicate. -/
theorem officialFrontierActiveSimple_singleton_root (m : MoleculeGraph V) (atom : V) :
    m.OfficialFrontierActiveSimple [OfficialCIPNode.root atom] := by
  intro node hnode _nonduplicate
  simp only [List.mem_singleton] at hnode
  subst node
  exact ⟨rfl, by simp [OfficialCIPNode.root]⟩

/-- The visited-set frontier bound specialised to an arbitrary atom root: the official
breadth-first expansion of `OfficialCIPNode.root atom` is empty at depth
`Fintype.card V + 1`. -/
theorem officialCIPFrontier_root_eq_nil_card_add_one (m : MoleculeGraph V) (atom : V) :
    m.officialCIPFrontier (Fintype.card V + 1) [OfficialCIPNode.root atom] = [] := by
  refine m.officialCIPFrontier_eq_nil_of_activeSimple_length_bound
    (fuel := Fintype.card V)
    (m.officialFrontierActiveSimple_singleton_root atom) ?_
  intro root hroot
  simp only [List.mem_singleton] at hroot
  subst root
  simp [OfficialCIPNode.root]

/-- Generic official expansion completeness at an arbitrary atom root, at depth
`Fintype.card V + 1`. -/
theorem officialExpansionCompleteWithin_root_default (m : MoleculeGraph V) (atom : V) :
    OfficialExpansionCompleteWithin m.officialCIPChildren (Fintype.card V + 1)
      (OfficialCIPNode.root atom) := by
  apply (officialExpansionCompleteWithin_iff_frontier_succ_nil m
    (Fintype.card V + 1) (OfficialCIPNode.root atom)).mpr
  have exhausted := m.officialCIPFrontier_root_eq_nil_card_add_one atom
  rw [show Fintype.card V + 1 + 1 = 1 + (Fintype.card V + 1) by omega]
  rw [m.officialCIPFrontier_add 1 (Fintype.card V + 1)]
  rw [exhausted]
  simp

end MoleculeGraph

namespace CertifiedLocalizedCIPInput

/-- Executable official expansion completeness at an arbitrary atom root of an arbitrary
certified localized input, at the carrier depth `atomCount + 1`.  The proof transfers the generic
proof-facing completeness across the executable/proof-facing child permutation; it assumes no
tetrahedral center and no expansion-completeness hypothesis. -/
theorem executableOfficialExpansionCompleteWithin_root_default
    (input : CertifiedLocalizedCIPInput) (atom : input.Atom) :
    MoleculeGraph.OfficialExpansionCompleteWithin input.executableOfficialCIPChildren
      (input.certified.input.molecule.atomCount + 1)
      (OfficialCIPNode.root atom) := by
  have reference := input.moleculeGraph.officialExpansionCompleteWithin_root_default atom
  have same := MoleculeGraph.officialExpansionCompleteWithin_iff_of_children_perm
    input.executableOfficialCIPChildren input.moleculeGraph.officialCIPChildren
    input.executableOfficialCIPChildren_perm_officialCIPChildren
    (input.certified.input.molecule.atomCount + 1)
    (OfficialCIPNode.root atom)
  exact same.mpr (by simpa using reference)

/-- Every canonical directed bond root `OfficialCIPNode.rootFromEdge parent current` with
`current ≠ parent` is also complete at the same carrier depth.  This is the arbitrary-parent
generalisation of the tetrahedral ligand-root completeness theorem. -/
theorem executableOfficialExpansionCompleteWithin_rootFromEdge_arbitrary
    (input : CertifiedLocalizedCIPInput) {parent current : input.Atom}
    (different : current ≠ parent) :
    MoleculeGraph.OfficialExpansionCompleteWithin input.executableOfficialCIPChildren
      (input.certified.input.molecule.atomCount + 1)
      (OfficialCIPNode.rootFromEdge parent current) := by
  have reference := input.moleculeGraph.officialExpansionCompleteWithin_rootFromEdge_default
    (center := parent) (ligand := current) different
  have same := MoleculeGraph.officialExpansionCompleteWithin_iff_of_children_perm
    input.executableOfficialCIPChildren input.moleculeGraph.officialCIPChildren
    input.executableOfficialCIPChildren_perm_officialCIPChildren
    (input.certified.input.molecule.atomCount + 1)
    (OfficialCIPNode.rootFromEdge parent current)
  exact same.mpr (by simpa using reference)

/-! ## Universal coverage of atom-rooted unbounded descendants -/

/-- Every unbounded descendant of `OfficialCIPNode.root atom` is present in the atom-rooted
occurrence enumeration at carrier fuel `atomCount + 1`, with the exact full address, provenance
node and remaining depth left by the `fuel + 1 = atomCount + 2` subtree budget. -/
theorem localizedOccurrenceUniversalDepth_covers_atom
    (input : CertifiedLocalizedCIPInput) (atom : input.Atom)
    {address : List Nat} {descendant : OfficialCIPNode input.Atom}
    (reachable : input.UnboundedOfficialSubtree (OfficialCIPNode.root atom) address descendant) :
    { root := atom
      address := address
      node := descendant
      remaining := input.certified.input.molecule.atomCount + 1 + 1 - address.length } ∈
      input.localizedOccurrencesAtAtom
        (input.certified.input.molecule.atomCount + 1) atom := by
  have complete := input.executableOfficialExpansionCompleteWithin_root_default atom
  have addressBound : address.length ≤ input.certified.input.molecule.atomCount + 1 :=
    input.unboundedOfficialSubtree_address_length_le_of_complete
      (input.certified.input.molecule.atomCount + 1) complete reachable
  have enough : address.length ≤ input.certified.input.molecule.atomCount + 1 + 1 := by
    omega
  have covered := input.mem_localizedOccurrenceSubtree_of_unbounded
    (root := atom) (fuel := input.certified.input.molecule.atomCount + 1 + 1)
    (path := []) reachable enough
  simpa [localizedOccurrencesAtAtom] using covered

/-- Molecule-wide form: the deduplicated shared enumeration at carrier fuel `atomCount + 1`
contains the same atom-rooted unbounded descendant with exact address, node and remaining
depth. -/
theorem localizedOccurrenceUniversalDepth_covers_atom_moleculeWide
    (input : CertifiedLocalizedCIPInput) (atom : input.Atom)
    {address : List Nat} {descendant : OfficialCIPNode input.Atom}
    (reachable : input.UnboundedOfficialSubtree (OfficialCIPNode.root atom) address descendant) :
    { root := atom
      address := address
      node := descendant
      remaining := input.certified.input.molecule.atomCount + 1 + 1 - address.length } ∈
      input.localizedOccurrences (input.certified.input.molecule.atomCount + 1) := by
  have covered := input.localizedOccurrenceUniversalDepth_covers_atom atom reachable
  unfold localizedOccurrences
  rw [List.mem_dedup, List.mem_flatMap]
  exact ⟨atom, by simp, covered⟩

/-- Proof-relevant carrier occurrence assigned to an unbounded descendant of an arbitrary atom
root, at the universal carrier fuel `atomCount + 1`.  Its remaining depth is the exact budget
left after the address has been consumed. -/
def localizedUnboundedOccurrenceAtAtom
    (input : CertifiedLocalizedCIPInput) (atom : input.Atom)
    {address : List Nat} {descendant : OfficialCIPNode input.Atom}
    (reachable : input.UnboundedOfficialSubtree (OfficialCIPNode.root atom) address descendant) :
    input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1) :=
  ⟨{ root := atom
     address := address
     node := descendant
     remaining := input.certified.input.molecule.atomCount + 1 + 1 - address.length },
   input.localizedOccurrenceUniversalDepth_covers_atom_moleculeWide atom reachable⟩

@[simp] theorem localizedUnboundedOccurrenceAtAtom_root
    (input : CertifiedLocalizedCIPInput) (atom : input.Atom)
    {address : List Nat} {descendant : OfficialCIPNode input.Atom}
    (reachable : input.UnboundedOfficialSubtree (OfficialCIPNode.root atom) address descendant) :
    (input.localizedUnboundedOccurrenceAtAtom atom reachable).1.root = atom := rfl

@[simp] theorem localizedUnboundedOccurrenceAtAtom_address
    (input : CertifiedLocalizedCIPInput) (atom : input.Atom)
    {address : List Nat} {descendant : OfficialCIPNode input.Atom}
    (reachable : input.UnboundedOfficialSubtree (OfficialCIPNode.root atom) address descendant) :
    (input.localizedUnboundedOccurrenceAtAtom atom reachable).1.address = address := rfl

@[simp] theorem localizedUnboundedOccurrenceAtAtom_node
    (input : CertifiedLocalizedCIPInput) (atom : input.Atom)
    {address : List Nat} {descendant : OfficialCIPNode input.Atom}
    (reachable : input.UnboundedOfficialSubtree (OfficialCIPNode.root atom) address descendant) :
    (input.localizedUnboundedOccurrenceAtAtom atom reachable).1.node = descendant := rfl

@[simp] theorem localizedUnboundedOccurrenceAtAtom_remaining
    (input : CertifiedLocalizedCIPInput) (atom : input.Atom)
    {address : List Nat} {descendant : OfficialCIPNode input.Atom}
    (reachable : input.UnboundedOfficialSubtree (OfficialCIPNode.root atom) address descendant) :
    (input.localizedUnboundedOccurrenceAtAtom atom reachable).1.remaining =
      input.certified.input.molecule.atomCount + 1 + 1 - address.length := rfl

/-- The proof-relevant occurrence is a member of the executable finite carrier. -/
theorem localizedUnboundedOccurrenceAtAtom_mem_carrier
    (input : CertifiedLocalizedCIPInput) (atom : input.Atom)
    {address : List Nat} {descendant : OfficialCIPNode input.Atom}
    (reachable : input.UnboundedOfficialSubtree (OfficialCIPNode.root atom) address descendant) :
    input.localizedUnboundedOccurrenceAtAtom atom reachable ∈
      input.localizedOccurrenceCarrier
        (input.certified.input.molecule.atomCount + 1) :=
  List.mem_attach (input.localizedOccurrences
      (input.certified.input.molecule.atomCount + 1))
    (input.localizedUnboundedOccurrenceAtAtom atom reachable)

/-- The constructed occurrence satisfies the common carrier depth grading
`address.length + remaining = fuel + 1`, confirming that no depth was lost or lowered. -/
theorem localizedUnboundedOccurrenceAtAtom_depthGrade
    (input : CertifiedLocalizedCIPInput) (atom : input.Atom)
    {address : List Nat} {descendant : OfficialCIPNode input.Atom}
    (reachable : input.UnboundedOfficialSubtree (OfficialCIPNode.root atom) address descendant) :
    (input.localizedUnboundedOccurrenceAtAtom atom reachable).1.address.length +
        (input.localizedUnboundedOccurrenceAtAtom atom reachable).1.remaining =
      (input.certified.input.molecule.atomCount + 1) + 1 :=
  input.localizedCIPOccurrence_depthGrade
    (input.localizedUnboundedOccurrenceAtAtom atom reachable)

/-! ## The frontier is not truncation

At the universal carrier budget `atomCount + 2`, every unbounded atom-rooted descendant keeps a
strictly positive remaining depth, so the executable enumeration always still expands its
children.  The descendants at the completeness frontier `atomCount + 1` are genuine terminal
nodes, so the extra level is not needed to recover any further occurrence. -/

/-- No unbounded atom-rooted descendant reaches the zero-remaining carrier frontier: its stored
remaining depth is strictly positive at fuel `atomCount + 1`. -/
theorem localizedOccurrenceUniversalDepth_atom_remaining_pos
    (input : CertifiedLocalizedCIPInput) (atom : input.Atom)
    {address : List Nat} {descendant : OfficialCIPNode input.Atom}
    (reachable : input.UnboundedOfficialSubtree (OfficialCIPNode.root atom) address descendant) :
    0 < input.certified.input.molecule.atomCount + 1 + 1 - address.length := by
  have complete := input.executableOfficialExpansionCompleteWithin_root_default atom
  have addressBound : address.length ≤ input.certified.input.molecule.atomCount + 1 :=
    input.unboundedOfficialSubtree_address_length_le_of_complete
      (input.certified.input.molecule.atomCount + 1) complete reachable
  omega

/-- An unbounded atom-rooted descendant at the completeness frontier `atomCount + 1` has no
executable children.  The one remaining level of the carrier budget therefore cannot hide any
independent semantic occurrence. -/
theorem localizedOccurrenceUniversalDepth_atom_frontier_terminal
    (input : CertifiedLocalizedCIPInput) (atom : input.Atom)
    {address : List Nat} {descendant : OfficialCIPNode input.Atom}
    (reachable : input.UnboundedOfficialSubtree (OfficialCIPNode.root atom) address descendant)
    (atDepth : address.length = input.certified.input.molecule.atomCount + 1) :
    input.executableOfficialCIPChildren descendant = [] := by
  have complete := input.executableOfficialExpansionCompleteWithin_root_default atom
  exact input.unboundedOfficialSubtree_children_nil_of_complete_at_depth
    complete reachable atDepth

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
