/-
  Raw/localized oxido path invariant.

  ## Purpose

  `RawLocalizedChildCopyTransport` and `RawLocalizedChildNodeTransport` state the raw/localized
  child transport under the explicit per-node hypothesis `NoOxidoRootEdgeHistory mol node`.  That
  predicate is

  ```
  ∀ current center, node.history = [current, center] →
    ¬ BlueBookP93.TrigonalPyramidal.OxidoRootEdge mol center current
  ```

  and therefore only constrains nodes whose stored history is exactly a two-element path.  Two
  facts make a naive "prove it at the root and induct" argument wrong:

  * a root marker with one-element history (`history = [atom]`) satisfies the predicate
    *vacuously*, while
  * its actual first child has history `[u, atom]` and can activate the P/S oxido exception
    exactly on the actual first edge `(atom, u)`.

  This module does three things.

  1. It characterizes `NoOxidoRootEdgeHistory` exactly: vacuous unless the history has length two,
     and at length two equivalent to the negation of the production `OxidoRootEdge` on the actual
     edge, equivalently to the production detector returning `false`.
  2. It isolates the minimal rooted gate — the detector does not fire on the *actually emitted*
     first-shell child copies — and proves that this gate is hereditary along the actual canonical
     child relation: every node reachable from a one-element-history root satisfies
     `NoOxidoRootEdgeHistory`.  The gate is shown to be equivalent to the per-first-child
     hypothesis, and to hold structurally whenever the original root is not P or S (in particular
     for ordinary carbon roots).
  3. It applies the existing corrected `List.Forall₂` + `List.Perm` child endpoint of
     `RawLocalizedChildNodeTransport` to every reachable node, deriving the atom bound structurally
     from reachability and well-formedness instead of assuming it per node.  The resulting step
     theorem is re-applicable: every actual official child is related to an actual canonical child
     that is again reachable and again satisfies the stored exclusion.

  ## Explicit limits

  No claim is made that the rooted gate holds for P/S roots; the P/S oxido root case is exactly
  the excluded case, and `OxidoRootExpansionDiagnostic` witnesses that it can genuinely fire.
  The structural corollaries therefore carry the explicit hypotheses that the root element is not
  `P` and not `S` (with a carbon specialization).

  Every public theorem is guarded by `assert_kernel_only`.
-/

import TetraStereo.OneCenter.RawLocalizedChildNodeTransport

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace RawLocalizedOxidoPathInvariant

open TetraStereo.OneCenter.RawLocalizedChildNodeTransport

/-! ## 1. Exact structure of the stored exclusion -/

/-- A stored exclusion is vacuous unless the node history is a two-element path. -/
theorem noOxidoRootEdgeHistory_of_length_ne_two
    (mol : RawMolecule) {node : RawMolecule.CanonicalBranchNode}
    (hlen : node.history.length ≠ 2) :
    NoOxidoRootEdgeHistory mol node := by
  intro current center hhistory
  exact absurd (by rw [hhistory]; rfl) hlen

/-- A one-element history (an original root marker) satisfies the exclusion vacuously. -/
theorem noOxidoRootEdgeHistory_of_length_one
    (mol : RawMolecule) {node : RawMolecule.CanonicalBranchNode}
    (hlen : node.history.length = 1) :
    NoOxidoRootEdgeHistory mol node :=
  noOxidoRootEdgeHistory_of_length_ne_two mol (by rw [hlen]; decide)

/-- A root marker with history `[atom]` satisfies the stored exclusion vacuously. -/
theorem noOxidoRootEdgeHistory_of_history_singleton
    (mol : RawMolecule) {node : RawMolecule.CanonicalBranchNode} {atom : ℕ}
    (hhistory : node.history = [atom]) :
    NoOxidoRootEdgeHistory mol node :=
  noOxidoRootEdgeHistory_of_length_one mol (by rw [hhistory]; rfl)

/-- **Exact first-edge condition.**  For a node whose history is the actual two-element path
`[ligand, center]` (a first child of the root `center`), the stored exclusion holds exactly when
the production P/S oxido detector does not fire on the actual edge `(center, ligand)`. -/
theorem noOxidoRootEdgeHistory_iff_not_oxidoRootEdge
    (mol : RawMolecule) {node : RawMolecule.CanonicalBranchNode} {ligand center : ℕ}
    (hhistory : node.history = [ligand, center]) :
    NoOxidoRootEdgeHistory mol node ↔
      ¬ BlueBookP93.TrigonalPyramidal.OxidoRootEdge mol center ligand := by
  constructor
  · intro hno
    exact hno ligand center hhistory
  · intro hno current center' hcurrent
    have hlist : [current, center'] = [ligand, center] := by
      rw [← hcurrent, hhistory]
    cases hlist
    exact hno

/-- Detector form of the exact first-edge condition. -/
theorem noOxidoRootEdgeHistory_iff_detector_eq_false
    (mol : RawMolecule) {node : RawMolecule.CanonicalBranchNode} {ligand center : ℕ}
    (hhistory : node.history = [ligand, center]) :
    NoOxidoRootEdgeHistory mol node ↔
      mol.isTrigonalPyramidalOxidoRootEdge center ligand = false := by
  rw [noOxidoRootEdgeHistory_iff_not_oxidoRootEdge mol hhistory]
  constructor
  · intro hno
    cases hdet : mol.isTrigonalPyramidalOxidoRootEdge center ligand with
    | false => rfl
    | true =>
        exact absurd
          ((BlueBookP93.TrigonalPyramidal.isTrigonalPyramidalOxidoRootEdge_eq_true_iff
            mol center ligand).mp hdet) hno
  · intro hfalse hedge
    have htrue :=
      (BlueBookP93.TrigonalPyramidal.isTrigonalPyramidalOxidoRootEdge_eq_true_iff
        mol center ligand).mpr hedge
    rw [htrue] at hfalse
    exact absurd hfalse (by decide)

/-- The production first-edge root convention `RawMolecule.canonicalRoot center atom`, whose
history is `[atom, center]`, satisfies the stored exclusion exactly when the actual edge
`(center, atom)` is not a P/S oxido root edge. -/
theorem noOxidoRootEdgeHistory_canonicalRoot_iff
    (mol : RawMolecule) (center atom : ℕ) :
    NoOxidoRootEdgeHistory mol (RawMolecule.canonicalRoot center atom) ↔
      ¬ BlueBookP93.TrigonalPyramidal.OxidoRootEdge mol center atom := by
  apply noOxidoRootEdgeHistory_iff_not_oxidoRootEdge
  rfl

/-! ## 2. The minimal rooted first-shell gate -/

/-- Atom-level rooted gate: the production P/S oxido detector does not fire at the root atom on
any ligand.  This is a sufficient condition; the copy-level predicate below is the actual minimum
needed by the expansion. -/
def NoOxidoRootEdgeAtRoot (mol : RawMolecule) (root : ℕ) : Prop :=
  ∀ ligand : ℕ, ¬ BlueBookP93.TrigonalPyramidal.OxidoRootEdge mol root ligand

/-- **Minimal rooted gate.**  The detector does not fire on any child copy that the canonical
expansion actually emits from the root marker.  Only emitted first-shell copies are constrained. -/
def NoOxidoRootEdgeAtRootCopies (mol : RawMolecule)
    (root : RawMolecule.CanonicalBranchNode) : Prop :=
  ∀ copy : ℕ × ℕ, copy ∈ mol.canonicalChildCopies root →
    ¬ BlueBookP93.TrigonalPyramidal.OxidoRootEdge mol root.atom copy.1

/-- The atom-level gate implies the minimal copy-level gate. -/
theorem noOxidoRootEdgeAtRootCopies_of_atRoot
    {mol : RawMolecule} {root : RawMolecule.CanonicalBranchNode}
    (gate : NoOxidoRootEdgeAtRoot mol root.atom) :
    NoOxidoRootEdgeAtRootCopies mol root :=
  fun copy _ => gate copy.1

/-- Structural satisfaction: if the root atom is not phosphorus and not sulfur, the production
detector can never fire at it.  This is a statement about the ordinary (non-P-93.2) path; no
conclusion is drawn for P/S roots. -/
theorem noOxidoRootEdgeAtRoot_of_element_ne_P_ne_S
    (mol : RawMolecule) (root : ℕ) (spec : AtomSpec)
    (observed : mol.atomAt? root = some spec)
    (notP : spec.element ≠ .P) (notS : spec.element ≠ .S) :
    NoOxidoRootEdgeAtRoot mol root := by
  intro ligand hedge
  obtain ⟨centerSpec, oxygenSpec, hcenter, _hoxygen, hPS, _hoxide, _horder⟩ := hedge
  rw [observed] at hcenter
  cases hcenter
  rcases hPS with hP | hS
  · exact notP hP
  · exact notS hS

/-- Specialization to an ordinary carbon root. -/
theorem noOxidoRootEdgeAtRoot_of_element_eq_carbon
    (mol : RawMolecule) (root : ℕ) (spec : AtomSpec)
    (observed : mol.atomAt? root = some spec) (carbon : spec.element = .C) :
    NoOxidoRootEdgeAtRoot mol root := by
  refine noOxidoRootEdgeAtRoot_of_element_ne_P_ne_S mol root spec observed ?_ ?_
  · rw [carbon]; decide
  · rw [carbon]; decide

/-- Under a non-P/S root, the production first-edge root convention satisfies the stored
exclusion structurally. -/
theorem noOxidoRootEdgeHistory_canonicalRoot_of_centerElement_ne_P_ne_S
    (mol : RawMolecule) (center atom : ℕ) (spec : AtomSpec)
    (observed : mol.atomAt? center = some spec)
    (notP : spec.element ≠ .P) (notS : spec.element ≠ .S) :
    NoOxidoRootEdgeHistory mol (RawMolecule.canonicalRoot center atom) :=
  (noOxidoRootEdgeHistory_canonicalRoot_iff mol center atom).mpr
    (noOxidoRootEdgeAtRoot_of_element_ne_P_ne_S mol center spec observed notP notS atom)

/-- Carbon specialization of the preceding theorem. -/
theorem noOxidoRootEdgeHistory_canonicalRoot_of_centerElement_eq_carbon
    (mol : RawMolecule) (center atom : ℕ) (spec : AtomSpec)
    (observed : mol.atomAt? center = some spec) (carbon : spec.element = .C) :
    NoOxidoRootEdgeHistory mol (RawMolecule.canonicalRoot center atom) :=
  (noOxidoRootEdgeHistory_canonicalRoot_iff mol center atom).mpr
    (noOxidoRootEdgeAtRoot_of_element_eq_carbon mol center spec observed carbon atom)

/-! ## 3. Child construction facts -/

@[simp] theorem canonicalChildOfCopy_atom
    (node : RawMolecule.CanonicalBranchNode) (copy : ℕ × ℕ) :
    (Rule1bRepresentedAtomObservation.canonicalChildOfCopy node copy).atom = copy.1 := rfl

@[simp] theorem canonicalChildOfCopy_parent
    (node : RawMolecule.CanonicalBranchNode) (copy : ℕ × ℕ) :
    (Rule1bRepresentedAtomObservation.canonicalChildOfCopy node copy).parent = node.atom := rfl

@[simp] theorem canonicalChildOfCopy_history
    (node : RawMolecule.CanonicalBranchNode) (copy : ℕ × ℕ) :
    (Rule1bRepresentedAtomObservation.canonicalChildOfCopy node copy).history =
      copy.1 :: node.history := rfl

/-- An actual canonical child is the canonical constructor applied to an actual emitted copy. -/
theorem mem_canonicalChildren_iff_exists
    {mol : RawMolecule} {node child : RawMolecule.CanonicalBranchNode}
    (hmem : child ∈ mol.canonicalChildren node) :
    ∃ copy ∈ mol.canonicalChildCopies node,
      child = Rule1bRepresentedAtomObservation.canonicalChildOfCopy node copy := by
  rw [Rule1bRepresentedAtomObservation.canonicalChildren_eq_map_canonicalChildOfCopy] at hmem
  by_cases hleaf : node.forcedLeaf = true
  · rw [if_pos hleaf] at hmem
    simp at hmem
  · rw [if_neg hleaf] at hmem
    rw [List.mem_map] at hmem
    obtain ⟨copy, hcopy, hchild⟩ := hmem
    exact ⟨copy, hcopy, hchild.symm⟩

/-- Members of the emitted child-copy list are members of the seed enumeration: erasing one
parent copy cannot introduce a copy. -/
theorem mem_canonicalSeedCopies_of_mem_childCopies
    (mol : RawMolecule) {node : RawMolecule.CanonicalBranchNode} {copy : ℕ × ℕ}
    (hmem : copy ∈ mol.canonicalChildCopies node) :
    copy ∈ mol.canonicalSeedCopies node := by
  have hmem' :
      copy ∈ RawMolecule.eraseCanonicalParentCopy node.parent (mol.canonicalSeedCopies node) := by
    rwa [← RawMolecule.canonicalChildCopies_eq_erase_seed]
  rw [RawMolecule.eraseCanonicalParentCopy_eq_erase] at hmem'
  exact List.mem_of_mem_erase hmem'

/-- **The actual first edge.**  A child produced from a one-element-history root satisfies the
stored exclusion exactly when the detector does not fire on the actual first edge. -/
theorem noOxidoRootEdgeHistory_canonicalChildOfCopy_iff
    (mol : RawMolecule) {root : RawMolecule.CanonicalBranchNode}
    (rootHist : root.history = [root.atom]) (copy : ℕ × ℕ) :
    NoOxidoRootEdgeHistory mol
        (Rule1bRepresentedAtomObservation.canonicalChildOfCopy root copy) ↔
      ¬ BlueBookP93.TrigonalPyramidal.OxidoRootEdge mol root.atom copy.1 := by
  apply noOxidoRootEdgeHistory_iff_not_oxidoRootEdge mol
  simp [rootHist]

/-- **Descendants of a first edge.**  Every child of a node of history length at least two has
history length at least three, so no two-element witness exists and the exclusion is vacuous. -/
theorem noOxidoRootEdgeHistory_canonicalChildOfCopy_of_two_le
    (mol : RawMolecule) {node : RawMolecule.CanonicalBranchNode}
    (hlen : 2 ≤ node.history.length) (copy : ℕ × ℕ) :
    NoOxidoRootEdgeHistory mol
      (Rule1bRepresentedAtomObservation.canonicalChildOfCopy node copy) := by
  apply noOxidoRootEdgeHistory_of_length_ne_two
  intro h
  have hlen' :
      (Rule1bRepresentedAtomObservation.canonicalChildOfCopy node copy).history.length =
        node.history.length + 1 := by
    simp
  rw [hlen'] at h
  have h1 : node.history.length = 1 := Nat.succ.inj h
  rw [h1] at hlen
  exact absurd hlen (by decide)

/-! ### Exactness of the minimal gate on the actual canonical children -/

/-- The minimal first-shell gate is exactly the conjunction of the stored exclusions on the
actual canonical children.  The non-forced-leaf hypothesis is what makes every emitted copy an
actual child; a forced leaf expands to no children at all. -/
theorem noOxidoRootEdgeAtRootCopies_iff_children
    (mol : RawMolecule) {root : RawMolecule.CanonicalBranchNode}
    (rootHist : root.history = [root.atom]) (notForced : root.forcedLeaf = false) :
    NoOxidoRootEdgeAtRootCopies mol root ↔
      ∀ child ∈ mol.canonicalChildren root, NoOxidoRootEdgeHistory mol child := by
  constructor
  · intro gate child hmem
    obtain ⟨copy, hcopy, hchild⟩ := mem_canonicalChildren_iff_exists hmem
    rw [hchild]
    exact
      (noOxidoRootEdgeHistory_canonicalChildOfCopy_iff mol rootHist copy).mpr
        (gate copy hcopy)
  · intro hchildren copy hcopy
    have hmem : Rule1bRepresentedAtomObservation.canonicalChildOfCopy root copy ∈
        mol.canonicalChildren root := by
      rw [Rule1bRepresentedAtomObservation.canonicalChildren_eq_map_canonicalChildOfCopy,
        if_neg (by rw [notForced]; decide : ¬ root.forcedLeaf = true)]
      exact List.mem_map.mpr ⟨copy, hcopy, rfl⟩
    exact
      (noOxidoRootEdgeHistory_canonicalChildOfCopy_iff mol rootHist copy).mp
        (hchildren _ hmem)

/-! ## 4. Reachability and hereditary propagation -/

/-- Actual reachability from a root through the canonical child relation. -/
inductive ReachableCanonical (mol : RawMolecule) (root : RawMolecule.CanonicalBranchNode) :
    RawMolecule.CanonicalBranchNode → Prop where
  | refl : ReachableCanonical mol root root
  | child (node child : RawMolecule.CanonicalBranchNode)
      (reach : ReachableCanonical mol root node)
      (member : child ∈ mol.canonicalChildren node) :
      ReachableCanonical mol root child

/-- Every reachable node has nonempty history. -/
theorem reachable_history_pos
    (mol : RawMolecule) (root : RawMolecule.CanonicalBranchNode)
    (rootHist : root.history = [root.atom]) :
    ∀ node, ReachableCanonical mol root node → 0 < node.history.length := by
  intro node reach
  induction reach with
  | refl => rw [rootHist]; simp
  | child parent childNode _hreach hmem _ih =>
      obtain ⟨copy, _hcopy, hchild⟩ := mem_canonicalChildren_iff_exists hmem
      rw [hchild]
      simp

/-- Every reachable non-root node has history length at least two. -/
theorem reachable_length_ge_two_of_ne_root
    (mol : RawMolecule) (root : RawMolecule.CanonicalBranchNode)
    (rootHist : root.history = [root.atom]) :
    ∀ node, ReachableCanonical mol root node → node ≠ root → 2 ≤ node.history.length := by
  intro node reach
  induction reach with
  | refl => intro hne; exact absurd rfl hne
  | child parent childNode hreach hmem _ih =>
      intro _hne
      have hpos := reachable_history_pos mol root rootHist parent hreach
      obtain ⟨copy, _hcopy, hchild⟩ := mem_canonicalChildren_iff_exists hmem
      rw [hchild]
      have hlen' :
          (Rule1bRepresentedAtomObservation.canonicalChildOfCopy parent copy).history.length =
            parent.history.length + 1 := by
        simp
      rw [hlen']
      exact Nat.succ_le_succ (Nat.succ_le_of_lt hpos)

/-- **Hereditary exclusion from the minimal first-shell gate.**  If the root marker has
one-element history and the detector does not fire on any actually emitted first-shell copy, then
every node reachable from it satisfies `NoOxidoRootEdgeHistory`.

The root itself is vacuous; first children are discharged by the gate on the actual first edge;
all deeper nodes have history length at least three and are vacuous. -/
theorem reachable_noOxidoRootEdgeHistory_of_firstShellGate
    (mol : RawMolecule) (root : RawMolecule.CanonicalBranchNode)
    (rootHist : root.history = [root.atom])
    (gate : NoOxidoRootEdgeAtRootCopies mol root) :
    ∀ node, ReachableCanonical mol root node → NoOxidoRootEdgeHistory mol node := by
  intro node reach
  induction reach with
  | refl => exact noOxidoRootEdgeHistory_of_length_one mol (by rw [rootHist]; rfl)
  | child parent childNode hreach hmem _ih =>
      by_cases hroot : parent = root
      · subst hroot
        obtain ⟨copy, hcopy, hchild⟩ := mem_canonicalChildren_iff_exists hmem
        rw [hchild]
        exact
          (noOxidoRootEdgeHistory_canonicalChildOfCopy_iff mol rootHist copy).mpr
            (gate copy hcopy)
      · have hlen := reachable_length_ge_two_of_ne_root mol root rootHist parent hreach hroot
        obtain ⟨copy, _hcopy, hchild⟩ := mem_canonicalChildren_iff_exists hmem
        rw [hchild]
        exact noOxidoRootEdgeHistory_canonicalChildOfCopy_of_two_le mol hlen copy

/-- Hereditary exclusion from the atom-level rooted gate. -/
theorem reachable_noOxidoRootEdgeHistory
    (mol : RawMolecule) (root : RawMolecule.CanonicalBranchNode)
    (rootHist : root.history = [root.atom])
    (gate : NoOxidoRootEdgeAtRoot mol root.atom) :
    ∀ node, ReachableCanonical mol root node → NoOxidoRootEdgeHistory mol node :=
  reachable_noOxidoRootEdgeHistory_of_firstShellGate mol root rootHist
    (noOxidoRootEdgeAtRootCopies_of_atRoot gate)

/-- Hereditary exclusion for the production one-element-history root marker
`canonicalSelfParentRoot`. -/
theorem reachable_noOxidoRootEdgeHistory_of_selfParentRoot
    (mol : RawMolecule) (atom : ℕ) (gate : NoOxidoRootEdgeAtRoot mol atom) :
    ∀ node, ReachableCanonical mol (canonicalSelfParentRoot atom) node →
      NoOxidoRootEdgeHistory mol node :=
  reachable_noOxidoRootEdgeHistory mol (canonicalSelfParentRoot atom) rfl gate

/-- Hereditary exclusion for an ordinary carbon original root.  The rooted gate is discharged
structurally from the root atom's element. -/
theorem reachable_noOxidoRootEdgeHistory_of_selfParentCarbonRoot
    (mol : RawMolecule) (atom : ℕ) (spec : AtomSpec)
    (observed : mol.atomAt? atom = some spec) (carbon : spec.element = .C) :
    ∀ node, ReachableCanonical mol (canonicalSelfParentRoot atom) node →
      NoOxidoRootEdgeHistory mol node :=
  reachable_noOxidoRootEdgeHistory_of_selfParentRoot mol atom
    (noOxidoRootEdgeAtRoot_of_element_eq_carbon mol atom spec observed carbon)

/-! ## 5. Structural atom bounds for reachable nodes -/

/-- Every reachable node's atom is a parsed atom index, derived from reachability, the raw seed
characterization and well-formedness.  This removes the per-node `atomBound` hypothesis from the
recursive transport step. -/
theorem reachable_atom_lt
    (mol : RawMolecule) (root : RawMolecule.CanonicalBranchNode)
    (_rootHist : root.history = [root.atom])
    (rootBound : root.atom < mol.atomCount)
    (wellFormed : mol.WellFormed) :
    ∀ node, ReachableCanonical mol root node → node.atom < mol.atomCount := by
  intro node reach
  induction reach with
  | refl => exact rootBound
  | child parent _childNode _hreach hmem _ih =>
      obtain ⟨copy, hcopy, hchild⟩ := mem_canonicalChildren_iff_exists hmem
      rw [hchild]
      have hseed := mem_canonicalSeedCopies_of_mem_childCopies mol hcopy
      have hpositive :=
        (RawMolecule.mem_canonicalSeedCopies_iff mol parent wellFormed copy.1 copy.2).mp hseed
      have hbound := (RawMolecule.bondOrder_pos_endpoint_lt mol wellFormed hpositive.1).2
      simpa [Rule1bRepresentedAtomObservation.canonicalChildOfCopy] using hbound

/-! ## 6. Recursive child transport under the gate -/

/-- Pointwise membership extraction from an aligned `List.Forall₂` list: a member on the left is
related to some member on the right. -/
theorem exists_mem_of_forall₂_left {α β : Type*} {R : α → β → Prop}
    {l₁ : List α} {l₂ : List β} (h : List.Forall₂ R l₁ l₂) {x : α}
    (hx : x ∈ l₁) :
    ∃ y ∈ l₂, R x y := by
  obtain ⟨⟨i, hi⟩, hget⟩ := List.get_of_mem hx
  have hy : i < l₂.length := by
    rw [← h.length_eq]
    exact hi
  refine ⟨l₂.get ⟨i, hy⟩, List.get_mem _ _, ?_⟩
  rw [← hget]
  exact h.get hi hy

/-- **Recursive transport step.**  At every node reachable from a one-element-history root under
the minimal first-shell gate, the existing corrected `List.Forall₂` + `List.Perm` endpoint applies:
the actual executable official children are pointwise `NodeCorresponds`-related to an aligned
canonical list which permutes the actual canonical child list.

The stored exclusion is supplied by heredity rather than assumed per node, and the atom bound is
derived from reachability and well-formedness. -/
theorem reachableCIPChildren_forall₂_canonicalChildren
    (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (root : RawMolecule.CanonicalBranchNode)
    (rootHist : root.history = [root.atom])
    (rootBound : root.atom < mol.atomCount)
    (gate : NoOxidoRootEdgeAtRootCopies mol root)
    (node : RawMolecule.CanonicalBranchNode) (onode : OfficialCIPNode input.Atom)
    (reach : ReachableCanonical mol root node)
    (hcorr : NodeCorresponds (fun atom : input.Atom => atom.val) onode node) :
    ∃ alignedCanonical : List RawMolecule.CanonicalBranchNode,
      List.Forall₂ (NodeCorresponds (fun atom : input.Atom => atom.val))
        (input.executableOfficialCIPChildren onode) alignedCanonical ∧
      List.Perm alignedCanonical (mol.canonicalChildren node) := by
  have hno : NoOxidoRootEdgeHistory mol node :=
    reachable_noOxidoRootEdgeHistory_of_firstShellGate mol root rootHist gate node reach
  have hbound : node.atom < mol.atomCount :=
    reachable_atom_lt mol root rootHist rootBound wellFormed node reach
  have hcurrent : onode.current? =
      some (localizedIndexOf mol input agreement ⟨node.atom, hbound⟩) := by
    obtain ⟨atom, hatom⟩ := NodeCorresponds.exists_current hcorr
    have hval : atom.val = node.atom := by
      have hmap := hcorr.current
      rw [hatom] at hmap
      simpa using hmap
    rw [hatom]
    congr 1
    exact Fin.ext (by simpa [localizedIndexOf] using hval)
  have countExact := RawMolecule.toSemanticMolecule?_atomCount mol
    input.certified.input.molecule agreement.1
  cases hparent : onode.parent? with
  | none =>
      exact
        productionRootCIPChildren_forall₂_canonicalChildren mol input agreement wellFormed
          unique supported node onode hbound hcurrent hparent hno hcorr
  | some p =>
      have hpval : p.val = node.parent := by
        have hmap := hcorr.parent
        rw [hparent] at hmap
        simp only [Option.map_some] at hmap
        by_cases hself : node.parent = node.atom
        · rw [if_pos hself] at hmap
          cases hmap
        · rw [if_neg hself] at hmap
          exact Option.some.inj hmap
      have hparentBound : node.parent < mol.atomCount := by
        rw [← hpval, ← countExact]
        exact p.isLt
      have hparentObserved : onode.parent? =
          some (localizedIndexOf mol input agreement ⟨node.parent, hparentBound⟩) := by
        rw [hparent]
        congr 1
        exact Fin.ext (by simpa [localizedIndexOf] using hpval)
      exact
        productionCIPChildren_forall₂_canonicalChildren mol input agreement wellFormed
          unique supported node onode hbound hparentBound hcurrent hparentObserved hno hcorr

/-- Every actual official child corresponds to an actual canonical child of the same reachable
node.  No list equality is asserted; the correspondence is extracted from the `Forall₂` alignment
and the canonical `Perm`. -/
theorem reachableCIPChildren_official_mem_corresponds
    (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (root : RawMolecule.CanonicalBranchNode)
    (rootHist : root.history = [root.atom])
    (rootBound : root.atom < mol.atomCount)
    (gate : NoOxidoRootEdgeAtRootCopies mol root)
    (node : RawMolecule.CanonicalBranchNode) (onode : OfficialCIPNode input.Atom)
    (reach : ReachableCanonical mol root node)
    (hcorr : NodeCorresponds (fun atom : input.Atom => atom.val) onode node)
    {child : OfficialCIPNode input.Atom}
    (hmem : child ∈ input.executableOfficialCIPChildren onode) :
    ∃ canonicalChild ∈ mol.canonicalChildren node,
      NodeCorresponds (fun atom : input.Atom => atom.val) child canonicalChild := by
  obtain ⟨aligned, haligned, hperm⟩ :=
    reachableCIPChildren_forall₂_canonicalChildren mol input agreement wellFormed unique
      supported root rootHist rootBound gate node onode reach hcorr
  obtain ⟨canonicalChild, hmemAligned, hcorrChild⟩ :=
    exists_mem_of_forall₂_left haligned hmem
  exact ⟨canonicalChild, hperm.mem_iff.mp hmemAligned, hcorrChild⟩

/-- **Preservation of the recursive invariant.**  Every actual official child at a reachable node
is related to an actual canonical child which is itself reachable from the root and itself
satisfies the stored exclusion.  Hence the heredity theorem and the transport step can be applied
again at every descended node. -/
theorem reachableChild_pathInvariant
    (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (root : RawMolecule.CanonicalBranchNode)
    (rootHist : root.history = [root.atom])
    (rootBound : root.atom < mol.atomCount)
    (gate : NoOxidoRootEdgeAtRootCopies mol root)
    (node : RawMolecule.CanonicalBranchNode) (onode : OfficialCIPNode input.Atom)
    (reach : ReachableCanonical mol root node)
    (hcorr : NodeCorresponds (fun atom : input.Atom => atom.val) onode node)
    {child : OfficialCIPNode input.Atom}
    (hmem : child ∈ input.executableOfficialCIPChildren onode) :
    ∃ canonicalChild ∈ mol.canonicalChildren node,
      NodeCorresponds (fun atom : input.Atom => atom.val) child canonicalChild ∧
        ReachableCanonical mol root canonicalChild ∧
          NoOxidoRootEdgeHistory mol canonicalChild := by
  obtain ⟨canonicalChild, hmemCanonical, hcorrChild⟩ :=
    reachableCIPChildren_official_mem_corresponds mol input agreement wellFormed unique
      supported root rootHist rootBound gate node onode reach hcorr hmem
  have hreachChild : ReachableCanonical mol root canonicalChild :=
    ReachableCanonical.child node canonicalChild reach hmemCanonical
  exact ⟨canonicalChild, hmemCanonical, hcorrChild, hreachChild,
    reachable_noOxidoRootEdgeHistory_of_firstShellGate mol root rootHist gate canonicalChild
      hreachChild⟩

end RawLocalizedOxidoPathInvariant
end OneCenter
end TetraStereo

/-! ## Kernel-authority guards -/

assert_kernel_only
  TetraStereo.OneCenter.RawLocalizedOxidoPathInvariant.noOxidoRootEdgeHistory_of_length_ne_two
assert_kernel_only
  TetraStereo.OneCenter.RawLocalizedOxidoPathInvariant.noOxidoRootEdgeHistory_of_length_one
assert_kernel_only
  TetraStereo.OneCenter.RawLocalizedOxidoPathInvariant.noOxidoRootEdgeHistory_of_history_singleton
assert_kernel_only
  TetraStereo.OneCenter.RawLocalizedOxidoPathInvariant.noOxidoRootEdgeHistory_iff_not_oxidoRootEdge
assert_kernel_only
  TetraStereo.OneCenter.RawLocalizedOxidoPathInvariant.noOxidoRootEdgeHistory_iff_detector_eq_false
assert_kernel_only
  TetraStereo.OneCenter.RawLocalizedOxidoPathInvariant.noOxidoRootEdgeHistory_canonicalRoot_iff
assert_kernel_only
  TetraStereo.OneCenter.RawLocalizedOxidoPathInvariant.noOxidoRootEdgeAtRootCopies_of_atRoot
assert_kernel_only
  TetraStereo.OneCenter.RawLocalizedOxidoPathInvariant.noOxidoRootEdgeAtRoot_of_element_ne_P_ne_S
assert_kernel_only
  TetraStereo.OneCenter.RawLocalizedOxidoPathInvariant.noOxidoRootEdgeAtRoot_of_element_eq_carbon
assert_kernel_only
  TetraStereo.OneCenter.RawLocalizedOxidoPathInvariant.noOxidoRootEdgeHistory_canonicalRoot_of_centerElement_ne_P_ne_S
assert_kernel_only
  TetraStereo.OneCenter.RawLocalizedOxidoPathInvariant.noOxidoRootEdgeHistory_canonicalRoot_of_centerElement_eq_carbon
assert_kernel_only
  TetraStereo.OneCenter.RawLocalizedOxidoPathInvariant.noOxidoRootEdgeAtRootCopies_iff_children
assert_kernel_only
  TetraStereo.OneCenter.RawLocalizedOxidoPathInvariant.canonicalChildOfCopy_atom
assert_kernel_only
  TetraStereo.OneCenter.RawLocalizedOxidoPathInvariant.canonicalChildOfCopy_parent
assert_kernel_only
  TetraStereo.OneCenter.RawLocalizedOxidoPathInvariant.canonicalChildOfCopy_history
assert_kernel_only
  TetraStereo.OneCenter.RawLocalizedOxidoPathInvariant.mem_canonicalChildren_iff_exists
assert_kernel_only
  TetraStereo.OneCenter.RawLocalizedOxidoPathInvariant.mem_canonicalSeedCopies_of_mem_childCopies
assert_kernel_only
  TetraStereo.OneCenter.RawLocalizedOxidoPathInvariant.noOxidoRootEdgeHistory_canonicalChildOfCopy_iff
assert_kernel_only
  TetraStereo.OneCenter.RawLocalizedOxidoPathInvariant.noOxidoRootEdgeHistory_canonicalChildOfCopy_of_two_le
assert_kernel_only
  TetraStereo.OneCenter.RawLocalizedOxidoPathInvariant.reachable_history_pos
assert_kernel_only
  TetraStereo.OneCenter.RawLocalizedOxidoPathInvariant.reachable_length_ge_two_of_ne_root
assert_kernel_only
  TetraStereo.OneCenter.RawLocalizedOxidoPathInvariant.reachable_noOxidoRootEdgeHistory_of_firstShellGate
assert_kernel_only
  TetraStereo.OneCenter.RawLocalizedOxidoPathInvariant.reachable_noOxidoRootEdgeHistory
assert_kernel_only
  TetraStereo.OneCenter.RawLocalizedOxidoPathInvariant.reachable_noOxidoRootEdgeHistory_of_selfParentRoot
assert_kernel_only
  TetraStereo.OneCenter.RawLocalizedOxidoPathInvariant.reachable_noOxidoRootEdgeHistory_of_selfParentCarbonRoot
assert_kernel_only
  TetraStereo.OneCenter.RawLocalizedOxidoPathInvariant.reachable_atom_lt
assert_kernel_only
  TetraStereo.OneCenter.RawLocalizedOxidoPathInvariant.exists_mem_of_forall₂_left
assert_kernel_only
  TetraStereo.OneCenter.RawLocalizedOxidoPathInvariant.reachableCIPChildren_forall₂_canonicalChildren
assert_kernel_only
  TetraStereo.OneCenter.RawLocalizedOxidoPathInvariant.reachableCIPChildren_official_mem_corresponds
assert_kernel_only
  TetraStereo.OneCenter.RawLocalizedOxidoPathInvariant.reachableChild_pathInvariant
