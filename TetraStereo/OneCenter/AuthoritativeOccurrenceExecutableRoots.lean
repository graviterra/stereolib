import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceFixedPoint

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Plain source-canonical occurrence roots

`AuthoritativeSemanticMancudeOccurrenceFixedPoint` defines the distinguished occurrence of a
perceived source-canonical tetrahedral center through a `classical` tactic block:

```
noncomputable def aromaticCanonicalFinalOccurrence
    (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    source.AromaticCanonicalOccurrence fuel := by
  classical
  refine ⟨{ root := center.1, address := [], node := OfficialCIPNode.root center.1,
            remaining := fuel + 1 }, ?_⟩
  ...
```

The frame component of that definition is a plain structure literal over `center.1`; only the
membership component needs reasoning, and that component is a proof of a proposition.  The
`noncomputable` marker is inherited from the tactic block and propagates to
`aromaticCanonicalOccurrenceSystem` and to every theorem stated for that system.

This module writes the same frame data directly, without `classical`.

* `aromaticCanonicalExecutableRootFrame` is the root frame of an arbitrary source atom, written
  directly from the atom.
* `aromaticCanonicalExecutableRootOccurrence` pairs that frame with a membership witness for an
  *arbitrary* source atom, perceived center or not, and
  `aromaticCanonicalExecutableRootOccurrence_unique` proves it is the unique carrier member with
  the prescribed root and the empty relative address.
* `aromaticCanonicalExecutableFinalOccurrence` is the final occurrence of a center, computed
  through `center.1`, and `aromaticCanonicalExecutableFinalOccurrence_eq` proves with
  `Subtype.ext`/`rfl` that it is exactly `aromaticCanonicalFinalOccurrence`.
* `aromaticCanonicalExecutableOccurrenceSystem` is the same occurrence system written with the
  plain final occurrence, and `aromaticCanonicalExecutableOccurrenceSystem_eq` proves that it *is*
  the system of `AuthoritativeSemanticMancudeOccurrenceFixedPoint`; the two headline model
  statements for that system follow.

None of the definitions below invokes `classical`.  The frames are structure literals over atom
indices and the occurrences add only a membership proof.

## What is deliberately not done here

The concrete chemical evaluator remains a separate integration object.  This module is not a
complete chemical evaluator.  `AromaticCanonicalRuleSemantics` still demands three independently
supplied things: a declarative derivation relation on complete optional outcomes, a
dependency-restricted executable rule, and a proof that the two agree at every occurrence and
outcome.  Writing the occurrence *carrier* plainly does not discharge that obligation, and this
module does not define the derivation relation to be execution by fiat.

`AuthoritativeSemanticOrdinaryDoubleBondEndpointRule3Through5` contains the same root frame for an
arbitrary atom, also introduced under a `noncomputable` definition.  That module is intentionally
not imported: comparing the two constructions is a `Subtype.ext`/`rfl` computation comparing two
propositional proofs, it has no chemical content, and importing the rules-engine development to
obtain it is not justified.  The comparison is omitted.
-/

namespace AuthoritativeChemicalInput

open DeclarativeCIP

/-! ## Plain root frame -/

/-- Plain data of the distinguished occurrence at one source-canonical atom: that atom as the
root, the empty relative address, the official root cursor, and the full remaining expansion
budget `fuel + 1`.  The value is a structure literal over `atom`, so it involves no choice and no
decidable instance. -/
def aromaticCanonicalExecutableRootFrame (source : AuthoritativeChemicalInput) (fuel : Nat)
    (atom : source.AromaticCanonicalAtom) : source.AromaticCanonicalOccurrenceFrame :=
  { root := atom
    address := []
    node := OfficialCIPNode.root atom
    remaining := fuel + 1 }

@[simp] theorem aromaticCanonicalExecutableRootFrame_root
    (source : AuthoritativeChemicalInput) (fuel : Nat) (atom : source.AromaticCanonicalAtom) :
    (source.aromaticCanonicalExecutableRootFrame fuel atom).root = atom := rfl

@[simp] theorem aromaticCanonicalExecutableRootFrame_address
    (source : AuthoritativeChemicalInput) (fuel : Nat) (atom : source.AromaticCanonicalAtom) :
    (source.aromaticCanonicalExecutableRootFrame fuel atom).address = [] := rfl

@[simp] theorem aromaticCanonicalExecutableRootFrame_node
    (source : AuthoritativeChemicalInput) (fuel : Nat) (atom : source.AromaticCanonicalAtom) :
    (source.aromaticCanonicalExecutableRootFrame fuel atom).node =
      OfficialCIPNode.root atom := rfl

@[simp] theorem aromaticCanonicalExecutableRootFrame_remaining
    (source : AuthoritativeChemicalInput) (fuel : Nat) (atom : source.AromaticCanonicalAtom) :
    (source.aromaticCanonicalExecutableRootFrame fuel atom).remaining = fuel + 1 := rfl

/-- The plain root frame is carried by the finite molecule-wide source-canonical occurrence
enumeration.  The witness is the root constructor of the independently stated reachability
relation of `AuthoritativeSemanticMancudeOccurrenceFixedPoint`; it is a proof of a proposition. -/
theorem aromaticCanonicalExecutableRootFrame_mem
    (source : AuthoritativeChemicalInput) (fuel : Nat) (atom : source.AromaticCanonicalAtom) :
    source.aromaticCanonicalExecutableRootFrame fuel atom ∈
      source.aromaticCanonicalOccurrences fuel := by
  apply (source.mem_aromaticCanonicalOccurrences_iff fuel
    (source.aromaticCanonicalExecutableRootFrame fuel atom)).mpr
  exact DeclarativeAromaticCanonicalOccurrenceSubtree.subtreeRoot [] (fuel + 1)
    (OfficialCIPNode.root atom)

/-- Distinguished root occurrence of an arbitrary source-canonical atom.  Contrast the
`noncomputable` `AromaticCanonicalOccurrenceFixedPoint`-level definition for centers: this one is
stated for any atom index and its frame component is exactly
`aromaticCanonicalExecutableRootFrame`. -/
def aromaticCanonicalExecutableRootOccurrence
    (source : AuthoritativeChemicalInput) (fuel : Nat) (atom : source.AromaticCanonicalAtom) :
    source.AromaticCanonicalOccurrence fuel :=
  ⟨source.aromaticCanonicalExecutableRootFrame fuel atom,
    source.aromaticCanonicalExecutableRootFrame_mem fuel atom⟩

@[simp] theorem aromaticCanonicalExecutableRootOccurrence_root
    (source : AuthoritativeChemicalInput) (fuel : Nat) (atom : source.AromaticCanonicalAtom) :
    (source.aromaticCanonicalExecutableRootOccurrence fuel atom).1.root = atom := rfl

@[simp] theorem aromaticCanonicalExecutableRootOccurrence_address
    (source : AuthoritativeChemicalInput) (fuel : Nat) (atom : source.AromaticCanonicalAtom) :
    (source.aromaticCanonicalExecutableRootOccurrence fuel atom).1.address = [] := rfl

@[simp] theorem aromaticCanonicalExecutableRootOccurrence_node
    (source : AuthoritativeChemicalInput) (fuel : Nat) (atom : source.AromaticCanonicalAtom) :
    (source.aromaticCanonicalExecutableRootOccurrence fuel atom).1.node =
      OfficialCIPNode.root atom := rfl

@[simp] theorem aromaticCanonicalExecutableRootOccurrence_remaining
    (source : AuthoritativeChemicalInput) (fuel : Nat) (atom : source.AromaticCanonicalAtom) :
    (source.aromaticCanonicalExecutableRootOccurrence fuel atom).1.remaining = fuel + 1 := rfl

/-- The plain root occurrence satisfies the independent reachability meaning of a root occurrence
at its atom.  In particular the membership witness stored in the carrier is the declarative root
constructor, not an assertion about evaluator behaviour. -/
theorem aromaticCanonicalExecutableRootOccurrence_declarative
    (source : AuthoritativeChemicalInput) (fuel : Nat) (atom : source.AromaticCanonicalAtom) :
    source.DeclarativeAromaticCanonicalOccurrenceAtAtom fuel atom
      (source.aromaticCanonicalExecutableRootOccurrence fuel atom).1 := by
  show source.DeclarativeAromaticCanonicalOccurrenceSubtree atom [] (fuel + 1)
    (OfficialCIPNode.root atom)
    (source.aromaticCanonicalExecutableRootOccurrence fuel atom).1
  exact DeclarativeAromaticCanonicalOccurrenceSubtree.subtreeRoot [] (fuel + 1)
    (OfficialCIPNode.root atom)

/-! ## Address characterization of the root occurrence -/

/-- Private restatement of the address-prefix invariant of a bounded declarative subtree.
`AuthoritativeSemanticMancudeOccurrenceRerootFrame` already publishes the same statement for its
own consumers, so this module keeps its copy private instead of shadowing it. -/
private theorem aromaticCanonicalOccurrenceSubtree_addressPrefix
    (source : AuthoritativeChemicalInput)
    {root : source.AromaticCanonicalAtom} {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode source.AromaticCanonicalAtom}
    {occurrence : source.AromaticCanonicalOccurrenceFrame}
    (derived : source.DeclarativeAromaticCanonicalOccurrenceSubtree
      root path fuel node occurrence) :
    path <+: occurrence.address := by
  induction derived with
  | subtreeRoot => exact ⟨[], by simp⟩
  | @subtreeDescendant path fuel node child slot occurrence
      childAtSlot descendant inductionHypothesis =>
      exact (List.prefix_append path [slot]).trans inductionHypothesis

/-- Private restatement of the address characterization of a subtree root frame: a derivation that
has not advanced its address is its root constructor. -/
private theorem aromaticCanonicalOccurrenceSubtree_eq_root_of_address_eq
    (source : AuthoritativeChemicalInput)
    {root : source.AromaticCanonicalAtom} {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode source.AromaticCanonicalAtom}
    {occurrence : source.AromaticCanonicalOccurrenceFrame}
    (derived : source.DeclarativeAromaticCanonicalOccurrenceSubtree
      root path fuel node occurrence)
    (address : occurrence.address = path) :
    occurrence =
      { root := root, address := path, node := node, remaining := fuel } := by
  cases derived with
  | subtreeRoot => rfl
  | @subtreeDescendant _ _ _ child slot descendant childAtSlot below =>
      have addressPrefix :=
        aromaticCanonicalOccurrenceSubtree_addressPrefix source below
      have lengthBound := addressPrefix.length_le
      rw [address] at lengthBound
      simp at lengthBound

/-- The plain root occurrence is the unique carrier member with a prescribed source root and the
empty relative address.  Both the official cursor and the remaining expansion budget are forced by
the reachability relation, so no case distinction on the atom is needed. -/
theorem aromaticCanonicalExecutableRootOccurrence_unique
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (atom : source.AromaticCanonicalAtom)
    (occurrence : source.AromaticCanonicalOccurrence fuel)
    (rootEq : occurrence.1.root = atom)
    (addressNil : occurrence.1.address = []) :
    occurrence = source.aromaticCanonicalExecutableRootOccurrence fuel atom := by
  refine Subtype.ext ?_
  have derived :=
    (source.mem_aromaticCanonicalOccurrences_iff fuel occurrence.1).mp occurrence.2
  have frameIdentity :=
    aromaticCanonicalOccurrenceSubtree_eq_root_of_address_eq source derived addressNil
  rw [frameIdentity, rootEq]
  rfl

/-! ## Plain final occurrence of a perceived center -/

/-- Plain final occurrence of a perceived source-canonical tetrahedral center: the root occurrence
at the center's source atom index `center.1`. -/
def aromaticCanonicalExecutableFinalOccurrence
    (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    source.AromaticCanonicalOccurrence fuel :=
  source.aromaticCanonicalExecutableRootOccurrence fuel center.1

@[simp] theorem aromaticCanonicalExecutableFinalOccurrence_root
    (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    (source.aromaticCanonicalExecutableFinalOccurrence fuel center).1.root = center.1 := rfl

@[simp] theorem aromaticCanonicalExecutableFinalOccurrence_address
    (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    (source.aromaticCanonicalExecutableFinalOccurrence fuel center).1.address = [] := rfl

@[simp] theorem aromaticCanonicalExecutableFinalOccurrence_node
    (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    (source.aromaticCanonicalExecutableFinalOccurrence fuel center).1.node =
      OfficialCIPNode.root center.1 := rfl

@[simp] theorem aromaticCanonicalExecutableFinalOccurrence_remaining
    (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    (source.aromaticCanonicalExecutableFinalOccurrence fuel center).1.remaining = fuel + 1 := rfl

/-- The plain final occurrence is exactly the final occurrence of
`AuthoritativeSemanticMancudeOccurrenceFixedPoint`.  `Subtype.ext` reduces the comparison to the
underlying frames, which are the same literal and therefore `rfl`; the two membership witnesses are
identified by proof irrelevance. -/
theorem aromaticCanonicalExecutableFinalOccurrence_eq
    (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    source.aromaticCanonicalExecutableFinalOccurrence fuel center =
      source.aromaticCanonicalFinalOccurrence fuel center :=
  Subtype.ext rfl

/-! ## Dependencies of the executable final occurrence -/

/-- Every permitted dependency of the executable final occurrence is a strictly deeper occurrence
below the same center: it has the center as its root and its relative address is nonempty.  The
final occurrence therefore depends on deeper occurrences; it is the top of the source-canonical
dependency order, not a leaf of it. -/
theorem aromaticCanonicalDepthDependency_executableFinalOccurrence_address_pos
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    {center : source.AromaticCanonicalTetrahedralCenter}
    {dependency : source.AromaticCanonicalOccurrence fuel}
    (below : source.AromaticCanonicalDepthDependency dependency
      (source.aromaticCanonicalExecutableFinalOccurrence fuel center)) :
    dependency.1.root = center.1 ∧ 0 < dependency.1.address.length := by
  refine ⟨below.1.trans
    (source.aromaticCanonicalExecutableFinalOccurrence_root fuel center), ?_⟩
  have addressNil := source.aromaticCanonicalExecutableFinalOccurrence_address fuel center
  have lengthBound := below.2
  rw [addressNil] at lengthBound
  simpa using lengthBound

/-- A dependency read while evaluating the executable final occurrence always has strictly smaller
remaining expansion depth than the full budget `fuel + 1`; the causal measure of the fixed point
therefore separates every dependency from the final occurrence. -/
theorem aromaticCanonicalDepthDependency_executableFinalOccurrence_remaining_lt
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    {center : source.AromaticCanonicalTetrahedralCenter}
    {dependency : source.AromaticCanonicalOccurrence fuel}
    (below : source.AromaticCanonicalDepthDependency dependency
      (source.aromaticCanonicalExecutableFinalOccurrence fuel center)) :
    dependency.1.remaining < fuel + 1 := by
  have positive :=
    (source.aromaticCanonicalDepthDependency_executableFinalOccurrence_address_pos
      below).2
  have grade := source.aromaticCanonicalOccurrence_depthGrade dependency
  omega

/-! ## Plain occurrence system -/

/-- The source-canonical aromatic occurrence system written with the plain final occurrence.  It has
the same descriptor projection, the same independently supplied declarative derivation relation and
the same dependency-restricted executable rule as `aromaticCanonicalOccurrenceSystem`, but the
final occurrence above. -/
def aromaticCanonicalExecutableOccurrenceSystem
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics fuel) :
    OccurrenceSystem source.AromaticCanonicalTetrahedralCenter
      (source.AromaticCanonicalOccurrence fuel) AromaticCanonicalAuxiliaryLabel where
  finalOccurrence := source.aromaticCanonicalExecutableFinalOccurrence fuel
  descriptorOf := aromaticCanonicalAuxiliaryDescriptor
  DeclarativeDerivation := semantics.DeclarativeDerivation
  executableStep := source.aromaticCanonicalExecutableStep semantics.executableRule

/-- The plain occurrence system is *the same occurrence system* as the original.  Three of the four
fields are definitionally the original ones; the fourth is the plain final occurrence, which is
equal to the original by `Subtype.ext`. -/
theorem aromaticCanonicalExecutableOccurrenceSystem_eq
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics fuel) :
    source.aromaticCanonicalExecutableOccurrenceSystem semantics =
      source.aromaticCanonicalOccurrenceSystem semantics := by
  have finalOccurrence_eq :
      source.aromaticCanonicalExecutableFinalOccurrence fuel =
        source.aromaticCanonicalFinalOccurrence fuel :=
    funext fun center =>
      source.aromaticCanonicalExecutableFinalOccurrence_eq fuel center
  unfold aromaticCanonicalExecutableOccurrenceSystem aromaticCanonicalOccurrenceSystem
  rw [finalOccurrence_eq]

/-! ## Consequences for the plain occurrence system -/

/-- Any independently justified source-canonical chemical semantics has exactly one complete
occurrence model of the plain system; the system is the one of
`AuthoritativeSemanticMancudeOccurrenceFixedPoint`, so the model is the same. -/
theorem existsUnique_aromaticCanonicalExecutableCIPModel
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics fuel) :
    ∃! state,
      (source.aromaticCanonicalExecutableOccurrenceSystem semantics).CIPModel state := by
  rw [source.aromaticCanonicalExecutableOccurrenceSystem_eq semantics]
  exact source.existsUnique_aromaticCanonicalCIPModel semantics

/-- The generic causal closure decodes to the unique source-canonical occurrence model of the plain
system. -/
theorem aromaticCanonicalExecutableSchedulerClosure_cipModel
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics fuel) :
    (source.aromaticCanonicalExecutableOccurrenceSystem semantics).CIPModel
      (DeclarativeCIP.OccurrenceScheduler.decode
        (source.aromaticCanonicalExecutableOccurrenceSystem semantics)
        (@source.AromaticCanonicalDepthDependency fuel)
        (DeclarativeCIP.OccurrenceScheduler.closure
          (source.aromaticCanonicalExecutableOccurrenceSystem semantics)
          (@source.AromaticCanonicalDepthDependency fuel))) := by
  rw [source.aromaticCanonicalExecutableOccurrenceSystem_eq semantics]
  exact source.aromaticCanonicalSchedulerClosure_cipModel semantics

end AuthoritativeChemicalInput

end TetraStereo.OneCenter
