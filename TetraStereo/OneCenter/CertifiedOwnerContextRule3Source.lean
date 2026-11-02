/-
# Certified owner-context Rule-3 source reader

This module repairs the trust weakness of `TetraStereo.OneCenter.OwnerContextRule3Source`.
That reader accepts a caller-supplied `ownerHistory : List ℕ` and only checks that some
suffix of it, prefixed by one predecessor atom, is a bonded path.  Three concrete defects
follow (each reproduced below on the old reader with `decide`):

* `owner = [99]` together with a malformed predecessor (empty history) is accepted and the
  out-of-range atom `99` is returned as the Rule-3 entry;
* the prefix `[99, 4, 2, 1, 3, 0]` is accepted because `ownerPredecessorAtom?` recurses over
  suffixes and never validates the skipped prefix;
* the bonded repeat history `[4, 2, 5, 2, 1, 3, 0]` is accepted on the up-then-down fixture,
  yielding the bonded entry `5`, which equals the far endpoint of the double bond.

The old file is not modified.  This module rebuilds the context from data that the caller
cannot fabricate:

* `owner` is an actual `CanonicalCenterTreeNode` generated from the stereogenic root and has
  real provenance (`CertifiedOwnerContext.ownerGenerated`, `ownerReal`);
* the path from the owner to the current cursor is an actual sequence of
  `CanonicalRerootCursor.children` steps (`RerootWalk`);
* `previous` and `current` are the last two actual cursor steps, so both have a genuine
  `previous?` predecessor and the coherent history relation
  `child.history = child.atom :: parent.history` for every downward step;
* the entry is the atom of `beforePrevious`, the actual cursor just before the `near`
  endpoint, not an arbitrary list element; its occurrence is real
  (`CertifiedOwnerContext.beforePreviousReal`);
* `CertifiedSource` consists of exactly the old reader's five source guards (both endpoints
  real, both non-centre, incoming edge of order two); coherence is not an extra premise;
* the reader refuses (`none`) any context whose entry equals the far endpoint, and returns
  `some none` for a coherent non-source context (non-real endpoint, centre-adjacent endpoint,
  or single bond), preserving the old three-way operational shape.

Generic results (the proof core) establish, for every certified context:

* `certifiedEntryCoherent_of_current_real`: if the far occurrence is real, then the entry
  occurrence differs from the far atom.  This is a theorem about the two actual cursor steps,
  proved by a four-case upward/downward analysis; hence the five source guards alone already
  guarantee a genuine entry, and `certifiedCoherent?_of_source` shows the runtime guard
  passes on every actual source;
* `certifiedEntry_near_bonded`: the entry atom is joined to the near endpoint by a written
  bond (`0 < bondOrder entry near`), because the last step is an actual canonical step;
* `certifiedEntry_ne_near`: the entry and near atoms are distinct real occurrences;
* `certifiedSourceUnit?_unit_double`: the returned near/far pair is the required double bond;
* `certifiedSourceUnit?_unit_entry_ne_far`: the returned entry is distinct from the far
  endpoint (the old `bondedrepeat` defect cannot be returned);
* `certifiedSourceUnit?_unit_entry_lt`: the returned entry is an in-range atom, so the old
  `[99]` defect cannot be returned;
* `certifiedEntry_eq_drop_two_of_downward` and
  `certifiedSourceUnit?_eq_historicalReader_of_downward`: whenever the last two steps are
  both downward canonical steps, the certified entry is exactly the historical entry
  `(current.history.drop 2).head?` and the certified reader agrees with the historical
  reader.  This is the preserved directional behaviour: the owner-side override is invisible
  on inputs where the canonical history already records the entry.

The two fixtures are the actual generated traversals of the old module:

* original (upward): `0 - 3 - 1 = 2 - 4`, reroot `4 → 2 → 1`, certified unit
  `near = 2, far = 1, entry = 4`;
* turn (up-then-down): `0 - 3 - 1 - 2`, owner `4` on `2`, double `2 = 5`, reroot
  `4 → 2 → 5`, certified unit `near = 2, far = 5, entry = 4` even though the cursor is
  directed and the historical reader reports entry `1`.

No production file is modified.  Scope: this is a certified *reader* and its proof core.
Supplying such a certificate from a production traversal (and integrating it into callers) is
left to the integrating layer; the reader itself makes no claim about uncertified inputs
beyond returning `none`.
-/

import TetraStereo.OneCenter.OwnerContextRule3Source
import TetraStereo.OneCenter.CanonicalGeneratedProfileAdmission
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.CertifiedOwnerContextRule3Source

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.OccurrencePreRule4b
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.OneCenter.CanonicalGeneratedComparisonProfile
open TetraStereo.OneCenter.CanonicalGeneratedProfileAdmission
open TetraStereo.OneCenter.OwnerContextRule3Source

/-! ## Actual zipper reachability -/

/-- Reachability by finitely many actual production cursor steps.  A `step` extends a walk by
one member of `CanonicalRerootCursor.children`, i.e. one genuine reroot neighbour that is not the
remembered incoming node. -/
inductive RerootWalk (mol : RawMolecule) (start : CanonicalRerootCursor) :
    CanonicalRerootCursor → Prop where
  | refl : RerootWalk mol start start
  | step {middle last : CanonicalRerootCursor} :
      RerootWalk mol start middle →
      last ∈ middle.children mol →
      RerootWalk mol start last

/-- A certified owner-centre Rule-3 context.

Everything except the owner and the three trailing cursors is a proof field, so the structure
cannot be built for a fabricated owner history.  `ownerWalk` is the actual reroot walk that
starts at the real owner occurrence and ends at `beforePrevious`; `previousStep` and
`currentStep` extend it by the last two cursor steps.  `beforePreviousReal` records that the
entry occurrence itself is real (a proven field, not a caller-supplied list atom); it is
needed for the sibling-uniqueness case of `certifiedEntryCoherent_of_current_real`. -/
structure CertifiedOwnerContext (mol : RawMolecule) (root : ℕ) where
  owner : RawMolecule.CanonicalBranchNode
  ownerGenerated : CanonicalCenterTreeNode mol root owner
  ownerReal : owner.provenance = RawMolecule.CanonicalNodeProvenance.realAtom
  beforePrevious : CanonicalRerootCursor
  beforePreviousReal : beforePrevious.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom
  previous : CanonicalRerootCursor
  current : CanonicalRerootCursor
  ownerWalk : RerootWalk mol { node := owner, previous? := none } beforePrevious
  previousStep : previous ∈ beforePrevious.children mol
  currentStep : current ∈ previous.children mol

/-! ## Read conditions -/

/-- The coherence condition that replaces the old unvalidated owner list: the entry occurrence
is genuinely distinct from the far endpoint.  Its failure is an unsupported read (outer `none`),
which is exactly the `entry = far` defect of the old reader. -/
def CertifiedEntryCoherent {mol : RawMolecule} {root : ℕ}
    (ctx : CertifiedOwnerContext mol root) : Prop :=
  ctx.beforePrevious.node.atom ≠ ctx.current.node.atom

/-- The complete certified source condition: exactly the old reader's five source guards (both
endpoints real, both non-centre, incoming edge of order two), but obtained from the general
certified context rather than from a caller-supplied atom list.

Coherence is deliberately *not* a premise here.  It is derived from the real far occurrence by
`certifiedEntryCoherent_of_current_real`, so a context satisfying these five guards can never
return an entry equal to the far endpoint. -/
def CertifiedSource (mol : RawMolecule) (center : ℕ) {root : ℕ}
    (ctx : CertifiedOwnerContext mol root) : Prop :=
  ctx.current.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom ∧
    ctx.previous.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom ∧
      ctx.current.node.atom ≠ center ∧
        ctx.previous.node.atom ≠ center ∧
          mol.bondOrder ctx.previous.node.atom ctx.current.node.atom = 2

instance certifiedEntryCoherentDecidable {mol : RawMolecule} {root : ℕ}
    (ctx : CertifiedOwnerContext mol root) : Decidable (CertifiedEntryCoherent ctx) := by
  unfold CertifiedEntryCoherent
  infer_instance

instance certifiedSourceDecidable (mol : RawMolecule) (center : ℕ) {root : ℕ}
    (ctx : CertifiedOwnerContext mol root) : Decidable (CertifiedSource mol center ctx) := by
  unfold CertifiedSource
  infer_instance

/-- Executable coherence decision. -/
def certifiedCoherent? {mol : RawMolecule} {root : ℕ}
    (ctx : CertifiedOwnerContext mol root) : Bool :=
  decide (CertifiedEntryCoherent ctx)

/-- Executable source decision. -/
def certifiedSource? (mol : RawMolecule) (center : ℕ) {root : ℕ}
    (ctx : CertifiedOwnerContext mol root) : Bool :=
  decide (CertifiedSource mol center ctx)

/-- The certified Rule-3 source reader.

The unit is returned only when the full certified source condition holds.  A coherent but
non-source context is the determinate `some none`, mirroring the old reader's classification.
An incoherent context -- in particular the `entry = far` repeat defect -- is the outer `none`:
the reader refuses to report a source unit with a non-genuine entry. -/
def certifiedSourceUnit? (mol : RawMolecule) (center : ℕ) {root : ℕ}
    (ctx : CertifiedOwnerContext mol root) :
    Option (Option ChemistryNormalizationResult.Rule3SourceUnit) :=
  if certifiedSource? mol center ctx then
    some (some { near := ctx.previous.node.atom, far := ctx.current.node.atom,
                 entry? := some ctx.beforePrevious.node.atom })
  else if certifiedCoherent? ctx then
    some none
  else
    none

/-- Entry-relative Rule-3 geometry wrapper.  It consumes exactly the unit read by
`certifiedSourceUnit?`; no entry is supplied or assumed on the path from the certificate to the
geometry. -/
def certifiedEntryGeometry? (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (center : ℕ) {root : ℕ} (ctx : CertifiedOwnerContext mol root) :
    Option OfficialRule3Geometry :=
  match certifiedSourceUnit? mol center ctx with
  | some (some unit) =>
      match unit.entry? with
      | some entry =>
          ChemistryNormalizationResult.rule3EntryGeometry? result mol unit.near unit.far entry
      | none => none
  | _ => none

/-! ## Generic cursor-step facts -/

/-- A member of `children` is a genuine uncut neighbour and stores that neighbour as its node
and the current node as its predecessor. -/
theorem mem_children_spec {mol : RawMolecule} {parent child : CanonicalRerootCursor}
    (member : child ∈ parent.children mol) :
    ∃ neighbor,
      neighbor ∈ ({ node := parent.node } : CanonicalRerootCursor).neighbors mol ∧
        child = { node := neighbor, previous? := some parent.node } := by
  unfold CanonicalRerootCursor.children at member
  by_cases leaf : parent.node.forcedLeaf
  · simp [leaf] at member
  · simp only [leaf, Bool.false_eq_true, ↓reduceIte, List.mem_filterMap] at member
    rcases member with ⟨neighbor, neighborMember, selected⟩
    cases hprevious : parent.previous? with
    | none =>
        rw [hprevious] at selected
        exact ⟨neighbor, neighborMember, (Option.some.inj selected).symm⟩
    | some previous =>
        rw [hprevious] at selected
        dsimp only at selected
        by_cases same : neighbor == previous
        · rw [if_pos same] at selected
          simp at selected
        · rw [if_neg same] at selected
          exact ⟨neighbor, neighborMember, (Option.some.inj selected).symm⟩

/-- The node of a child cursor is a neighbour of the parent node. -/
theorem mem_children_neighbor {mol : RawMolecule} {parent child : CanonicalRerootCursor}
    (member : child ∈ parent.children mol) :
    child.node ∈ ({ node := parent.node } : CanonicalRerootCursor).neighbors mol := by
  rcases mem_children_spec member with ⟨neighbor, neighborMember, childEq⟩
  rw [childEq]
  exact neighborMember

/-- Every child cursor remembers the parent node as its predecessor: there is no malformed
`previous?` in a genuinely stepped context. -/
theorem mem_children_previous? {mol : RawMolecule} {parent child : CanonicalRerootCursor}
    (member : child ∈ parent.children mol) :
    child.previous? = some parent.node := by
  rcases mem_children_spec member with ⟨neighbor, _neighborMember, childEq⟩
  rw [childEq]

/-- A canonical child stores its source atom as its parent. -/
theorem canonicalChildren_parent (mol : RawMolecule)
    {parent child : RawMolecule.CanonicalBranchNode}
    (member : child ∈ mol.canonicalChildren parent) :
    child.parent = parent.atom := by
  unfold RawMolecule.canonicalChildren at member
  by_cases leaf : parent.forcedLeaf
  · simp [leaf] at member
  · simp only [leaf, Bool.false_eq_true, ↓reduceIte, List.mem_map] at member
    obtain ⟨copy, _copyMember, rfl⟩ := member
    rfl

/-- A canonical child is joined to its parent by a written bond of positive order. -/
theorem canonicalChildren_bondOrder_pos (mol : RawMolecule)
    {parent child : RawMolecule.CanonicalBranchNode}
    (head : parent.history.head? = some parent.atom)
    (member : child ∈ mol.canonicalChildren parent) :
    0 < mol.bondOrder parent.atom child.atom := by
  unfold RawMolecule.canonicalChildren at member
  by_cases leaf : parent.forcedLeaf
  · simp [leaf] at member
  · simp only [leaf, Bool.false_eq_true, ↓reduceIte, List.mem_map] at member
    obtain ⟨copy, copyMember, rfl⟩ := member
    rcases mol.canonicalChildCopies_source parent copy copyMember with
      ⟨bond, _bondMember, _endpoints, copyIndex⟩
    have positive : 0 < mol.canonicalBondOrder parent copy.1 :=
      Nat.lt_of_le_of_lt (Nat.zero_le copy.2) copyIndex
    exact mol.canonicalBondOrder_pos_imp_bondOrder_pos parent copy.1 head positive

/-- A canonical child atom differs from its source atom: positive bond order excludes the
reflexive source-target pair, whose order is zero. -/
theorem canonicalChildren_atom_ne_parent (mol : RawMolecule)
    {parent child : RawMolecule.CanonicalBranchNode}
    (head : parent.history.head? = some parent.atom)
    (member : child ∈ mol.canonicalChildren parent) :
    child.atom ≠ parent.atom := by
  intro equal
  have positive := canonicalChildren_bondOrder_pos mol head member
  rw [equal, mol.bondOrder_self] at positive
  exact Nat.lt_irrefl 0 positive

/-- Every atom generated from a bounded real root is an in-range atom index. -/
theorem generated_node_atom_lt (mol : RawMolecule) {root : ℕ} (well : mol.WellFormed)
    (rootBound : root < mol.atomCount) {node : RawMolecule.CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode mol root node) :
    node.atom < mol.atomCount := by
  induction generated with
  | root => simpa [canonicalCenterRoot] using rootBound
  | @child parent child _parentGenerated member _ih =>
      exact child_atom_lt_atomCount well member

/-- Every child of a generated node is generated. -/
theorem mem_children_node_generated {mol : RawMolecule} {root : ℕ}
    {cursor child : CanonicalRerootCursor}
    (generated : CanonicalCenterTreeNode mol root cursor.node)
    (member : child ∈ cursor.children mol) :
    CanonicalCenterTreeNode mol root child.node := by
  have neighborMember :
      child.node ∈ ({ node := cursor.node } : CanonicalRerootCursor).neighbors mol :=
    mem_children_neighbor member
  rcases CanonicalCenterTreeNode.neighbor_cases generated neighborMember with
    parentCase | childCase
  · exact parentCase.1
  · exact CanonicalCenterTreeNode.child generated childCase

/-- Every node reached by an actual walk from a generated start is generated. -/
theorem rerootWalk_generated {mol : RawMolecule} {root : ℕ} {start : CanonicalRerootCursor} :
    ∀ {finish : CanonicalRerootCursor}, RerootWalk mol start finish →
      CanonicalCenterTreeNode mol root start.node →
        CanonicalCenterTreeNode mol root finish.node
  | _, RerootWalk.refl, generated => generated
  | _, RerootWalk.step walk member, generated =>
      mem_children_node_generated (rerootWalk_generated walk generated) member

/-! ## Certified context facts -/

/-- The cursor just before the near endpoint is generated from the root. -/
theorem certified_beforePrevious_generated {mol : RawMolecule} {root : ℕ}
    (ctx : CertifiedOwnerContext mol root) :
    CanonicalCenterTreeNode mol root ctx.beforePrevious.node :=
  rerootWalk_generated ctx.ownerWalk ctx.ownerGenerated

/-- The near cursor's node is generated from the root. -/
theorem certified_previous_generated {mol : RawMolecule} {root : ℕ}
    (ctx : CertifiedOwnerContext mol root) :
    CanonicalCenterTreeNode mol root ctx.previous.node :=
  mem_children_node_generated (certified_beforePrevious_generated ctx) ctx.previousStep

/-- The far cursor's node is generated from the root. -/
theorem certified_current_generated {mol : RawMolecule} {root : ℕ}
    (ctx : CertifiedOwnerContext mol root) :
    CanonicalCenterTreeNode mol root ctx.current.node :=
  mem_children_node_generated (certified_previous_generated ctx) ctx.currentStep

/-- The owner occurrence is an in-range atom index. -/
theorem certified_owner_atom_lt {mol : RawMolecule} {root : ℕ}
    (well : mol.WellFormed) (rootBound : root < mol.atomCount)
    (ctx : CertifiedOwnerContext mol root) :
    ctx.owner.atom < mol.atomCount :=
  generated_node_atom_lt mol well rootBound ctx.ownerGenerated

/-- The entry-side cursor node is an in-range atom index. -/
theorem certified_beforePrevious_atom_lt {mol : RawMolecule} {root : ℕ}
    (well : mol.WellFormed) (rootBound : root < mol.atomCount)
    (ctx : CertifiedOwnerContext mol root) :
    ctx.beforePrevious.node.atom < mol.atomCount :=
  generated_node_atom_lt mol well rootBound (certified_beforePrevious_generated ctx)

/-- The near cursor node is an in-range atom index. -/
theorem certified_previous_atom_lt {mol : RawMolecule} {root : ℕ}
    (well : mol.WellFormed) (rootBound : root < mol.atomCount)
    (ctx : CertifiedOwnerContext mol root) :
    ctx.previous.node.atom < mol.atomCount :=
  generated_node_atom_lt mol well rootBound (certified_previous_generated ctx)

/-- The far cursor node is an in-range atom index. -/
theorem certified_current_atom_lt {mol : RawMolecule} {root : ℕ}
    (well : mol.WellFormed) (rootBound : root < mol.atomCount)
    (ctx : CertifiedOwnerContext mol root) :
    ctx.current.node.atom < mol.atomCount :=
  generated_node_atom_lt mol well rootBound (certified_current_generated ctx)

/-- The entry atom and the near atom are genuinely bonded: the last walk step is an actual
canonical child step or its reverse, and both cases carry a written bond. -/
theorem certifiedEntry_near_bonded {mol : RawMolecule} {root : ℕ}
    (ctx : CertifiedOwnerContext mol root) :
    0 < mol.bondOrder ctx.beforePrevious.node.atom ctx.previous.node.atom := by
  have beforeGenerated := certified_beforePrevious_generated ctx
  have neighborMember :
      ctx.previous.node ∈
        ({ node := ctx.beforePrevious.node } : CanonicalRerootCursor).neighbors mol :=
    mem_children_neighbor ctx.previousStep
  rcases CanonicalCenterTreeNode.neighbor_cases beforeGenerated neighborMember with
    parentCase | childCase
  · have positive :
        0 < mol.bondOrder ctx.previous.node.atom ctx.beforePrevious.node.atom :=
      canonicalChildren_bondOrder_pos mol
        (CanonicalCenterTreeNode.history_head parentCase.1) parentCase.2
    rw [RawMolecule.bondOrder_symm] at positive
    exact positive
  · exact canonicalChildren_bondOrder_pos mol
      (CanonicalCenterTreeNode.history_head beforeGenerated) childCase

/-- The entry atom and the near atom are distinct: a canonical child atom differs from its
source atom, in whichever direction the last actual step runs. -/
theorem certifiedEntry_ne_near {mol : RawMolecule} {root : ℕ}
    (ctx : CertifiedOwnerContext mol root) :
    ctx.beforePrevious.node.atom ≠ ctx.previous.node.atom := by
  have beforeGenerated := certified_beforePrevious_generated ctx
  have neighborMember :
      ctx.previous.node ∈
        ({ node := ctx.beforePrevious.node } : CanonicalRerootCursor).neighbors mol :=
    mem_children_neighbor ctx.previousStep
  rcases CanonicalCenterTreeNode.neighbor_cases beforeGenerated neighborMember with
    parentCase | childCase
  · exact canonicalChildren_atom_ne_parent mol
      (CanonicalCenterTreeNode.history_head parentCase.1) parentCase.2
  · exact fun equal =>
      canonicalChildren_atom_ne_parent mol
        (CanonicalCenterTreeNode.history_head beforeGenerated) childCase equal.symm

/-- **The coherence guarantee is a theorem of the actual history, not a checked premise.**

If the far occurrence is real, the entry occurrence cannot be the far atom.  Let `B`, `P`, `C`
be the before-previous, previous and current nodes.  The two actual cursor steps give
`P.previous? = some B` and an uncut neighbour `C` of `P` with `C ≠ B` (the remembered
incoming neighbour is filtered out).  Each step is either upward (the previous occurrence is a
canonical child) or downward.  The four cases are excluded as follows:

* down/down: `B` occurs in `P.history` (it heads `B.history`), while the real child `C` is
  fresh in that history;
* up/up: the real child `B` is fresh in `P.history`, while `C` occurs in it (it heads
  `C.history` and `P.history = P.atom :: C.history`);
* down/up: exact parent recovery gives `canonicalOriginalParent? P = some B` and also
  `= some C`, hence `B = C`, contradicting the cut;
* up/down: `B` and `C` are real siblings of `P`, so equal atoms force equal atom, parent,
  history and provenance, hence `B = C`, again contradicting the cut.

The hypothesis `currentReal` is essential: a ring duplicate `C` may repeat `B.atom`. -/
theorem certifiedEntryCoherent_of_current_real {mol : RawMolecule} {root : ℕ}
    (ctx : CertifiedOwnerContext mol root)
    (currentReal : ctx.current.node.provenance =
      RawMolecule.CanonicalNodeProvenance.realAtom) :
    CertifiedEntryCoherent ctx := by
  intro equal
  -- The remembered incoming edge of `previous` is exactly `beforePrevious`, so the actual
  -- `current` step is a step of the cursor whose predecessor is `beforePrevious`.
  have previousEq := mem_children_previous? ctx.previousStep
  have member' : ctx.current ∈
      ({ node := ctx.previous.node, previous? := some ctx.beforePrevious.node } :
        CanonicalRerootCursor).children mol := by
    simpa [CanonicalRerootCursor.children, previousEq] using ctx.currentStep
  obtain ⟨neighbor, _neighborMember, different, childEq⟩ :=
    mem_cursor_children_of_previous member'
  -- `current` is not the before-previous occurrence: its remembered predecessor is the
  -- previous node, and the selected neighbour differs from `beforePrevious`.
  have cutNe : ctx.current.node ≠ ctx.beforePrevious.node := by
    intro same
    have neighborIs : neighbor = ctx.current.node :=
      (congrArg CanonicalRerootCursor.node childEq).symm
    exact different (neighborIs.trans same)
  have beforeGenerated := certified_beforePrevious_generated ctx
  rcases CanonicalCenterTreeNode.neighbor_cases beforeGenerated
      (mem_children_neighbor ctx.previousStep) with step1Up | step1Down
  · -- `previous` is the parent; `beforePrevious` is its real child.
    rcases CanonicalCenterTreeNode.neighbor_cases (certified_previous_generated ctx)
        (mem_children_neighbor ctx.currentStep) with step2Up | step2Down
    · -- up/up: `B.atom` is fresh in `P.history`, while `C.atom` lies in it.
      have fresh := real_child_not_mem_history step1Up.2 ctx.beforePreviousReal
      have present : ctx.current.node.atom ∈ ctx.previous.node.history := by
        rw [mol.canonicalChildren_history ctx.current.node ctx.previous.node step2Up.2]
        exact List.mem_cons_of_mem _
          (List.mem_of_head? (CanonicalCenterTreeNode.history_head step2Up.1))
      exact fresh (equal ▸ present)
    · -- up/down: real siblings of `P` with equal atoms are the same occurrence.
      have beforeParent := canonicalChildren_parent mol step1Up.2
      have currentParent := canonicalChildren_parent mol step2Down
      have beforeHistory :=
        mol.canonicalChildren_history ctx.previous.node ctx.beforePrevious.node step1Up.2
      have currentHistory :=
        mol.canonicalChildren_history ctx.previous.node ctx.current.node step2Down
      have recordsEq : ctx.beforePrevious.node = ctx.current.node := by
        have atomEq : ctx.beforePrevious.node.atom = ctx.current.node.atom := equal
        have parentEq : ctx.beforePrevious.node.parent = ctx.current.node.parent :=
          beforeParent.trans currentParent.symm
        have historyEq : ctx.beforePrevious.node.history = ctx.current.node.history := by
          rw [beforeHistory, currentHistory, atomEq]
        have provEq : ctx.beforePrevious.node.provenance =
            ctx.current.node.provenance :=
          ctx.beforePreviousReal.trans currentReal.symm
        change RawMolecule.CanonicalBranchNode.mk
            ctx.beforePrevious.node.atom ctx.beforePrevious.node.parent
            ctx.beforePrevious.node.history ctx.beforePrevious.node.provenance =
          RawMolecule.CanonicalBranchNode.mk
            ctx.current.node.atom ctx.current.node.parent
            ctx.current.node.history ctx.current.node.provenance
        rw [atomEq, parentEq, historyEq, provEq]
      exact cutNe recordsEq.symm
  · -- `beforePrevious` is the parent; `previous` is its child.
    rcases CanonicalCenterTreeNode.neighbor_cases (certified_previous_generated ctx)
        (mem_children_neighbor ctx.currentStep) with step2Up | step2Down
    · -- down/up: exact parent recovery forces `B = C`.
      have recoverBefore :=
        canonicalOriginalParent?_eq_some_of_child beforeGenerated step1Down
      have recoverCurrent :=
        canonicalOriginalParent?_eq_some_of_child step2Up.1 step2Up.2
      have recordsEq : ctx.beforePrevious.node = ctx.current.node := by
        rw [recoverBefore] at recoverCurrent
        exact Option.some.inj recoverCurrent
      exact cutNe recordsEq.symm
    · -- down/down: `B.atom` occurs in `P.history`; the real child `C` is fresh in it.
      have fresh := real_child_not_mem_history step2Down currentReal
      have present : ctx.beforePrevious.node.atom ∈ ctx.previous.node.history := by
        rw [mol.canonicalChildren_history ctx.beforePrevious.node ctx.previous.node step1Down]
        exact List.mem_cons_of_mem _
          (List.mem_of_head? (CanonicalCenterTreeNode.history_head beforeGenerated))
      exact fresh (equal ▸ present)

/-! ## Reuse of the generated-profile admission results -/


theorem certifiedOwner_pathOK (mol : RawMolecule) (root : ℕ) (well : mol.WellFormed)
    (rootBound : root < mol.atomCount) (ctx : CertifiedOwnerContext mol root) :
    pathOK? mol root ctx.owner = true :=
  generated_pathOK mol root well rootBound ctx.ownerGenerated


theorem certifiedOwner_history_nodup (mol : RawMolecule) (root : ℕ) (well : mol.WellFormed)
    (rootBound : root < mol.atomCount) (ctx : CertifiedOwnerContext mol root) :
    ctx.owner.history.Nodup :=
  (CanonicalCenterTreeNode.real_history rootBound ctx.ownerGenerated well ctx.ownerReal).1


theorem certifiedOwner_history_atoms_lt (mol : RawMolecule) (root : ℕ) (well : mol.WellFormed)
    (rootBound : root < mol.atomCount) (ctx : CertifiedOwnerContext mol root) :
    ∀ atom, atom ∈ ctx.owner.history → atom < mol.atomCount :=
  (CanonicalCenterTreeNode.real_history rootBound ctx.ownerGenerated well ctx.ownerReal).2

/-! ## Reader laws -/

theorem certifiedCoherent?_eq_true_iff {mol : RawMolecule} {root : ℕ}
    (ctx : CertifiedOwnerContext mol root) :
    certifiedCoherent? ctx = true ↔ CertifiedEntryCoherent ctx := by
  unfold certifiedCoherent?
  exact decide_eq_true_iff

theorem certifiedSource?_eq_true_iff {mol : RawMolecule} {center : ℕ} {root : ℕ}
    (ctx : CertifiedOwnerContext mol root) :
    certifiedSource? mol center ctx = true ↔ CertifiedSource mol center ctx := by
  unfold certifiedSource?
  exact decide_eq_true_iff

/-- A full certified source context reads the owner-side unit. -/
theorem certifiedSourceUnit?_some_some_of_source {mol : RawMolecule} {center : ℕ} {root : ℕ}
    {ctx : CertifiedOwnerContext mol root} (source : CertifiedSource mol center ctx) :
    certifiedSourceUnit? mol center ctx =
      some (some { near := ctx.previous.node.atom, far := ctx.current.node.atom,
                   entry? := some ctx.beforePrevious.node.atom }) := by
  have hsrc : certifiedSource? mol center ctx = true :=
    (certifiedSource?_eq_true_iff ctx).mpr source
  unfold certifiedSourceUnit?
  split
  · rfl
  · rename_i hnot
    exact absurd hsrc hnot

/-- A coherent but non-source certified context is the determinate `some none`. -/
theorem certifiedSourceUnit?_some_none_of_coherent_not_source {mol : RawMolecule}
    {center : ℕ} {root : ℕ} {ctx : CertifiedOwnerContext mol root}
    (coherent : CertifiedEntryCoherent ctx) (notSource : ¬ CertifiedSource mol center ctx) :
    certifiedSourceUnit? mol center ctx = some none := by
  unfold certifiedSourceUnit?
  split
  · rename_i sourceTrue
    exact absurd ((certifiedSource?_eq_true_iff ctx).mp sourceTrue) notSource
  · split
    · rfl
    · rename_i coherentFalse
      exact absurd ((certifiedCoherent?_eq_true_iff ctx).mpr coherent) coherentFalse

/-- An incoherent certified context (in particular `entry = far`) is refused with the outer
`none`. -/
theorem certifiedSourceUnit?_none_of_not_coherent {mol : RawMolecule} {center : ℕ}
    {root : ℕ} {ctx : CertifiedOwnerContext mol root}
    (notCoherent : ¬ CertifiedEntryCoherent ctx) :
    certifiedSourceUnit? mol center ctx = none := by
  unfold certifiedSourceUnit?
  split
  · rename_i sourceTrue
    have source := (certifiedSource?_eq_true_iff ctx).mp sourceTrue
    exact absurd
      (certifiedEntryCoherent_of_current_real ctx source.1) notCoherent
  · split
    · rename_i coherentTrue
      exact absurd ((certifiedCoherent?_eq_true_iff ctx).mp coherentTrue) notCoherent
    · rfl

/-- The old `bondedrepeat` shape -- an entry equal to the far endpoint -- is refused.  The
source branch is impossible: whenever the five source guards hold, the real far occurrence
makes the entry coherent by `certifiedEntryCoherent_of_current_real`. -/
theorem certifiedSourceUnit?_none_of_entry_eq_far {mol : RawMolecule} {center : ℕ}
    {root : ℕ} {ctx : CertifiedOwnerContext mol root}
    (equal : ctx.beforePrevious.node.atom = ctx.current.node.atom) :
    certifiedSourceUnit? mol center ctx = none := by
  unfold certifiedSourceUnit?
  split
  · rename_i sourceTrue
    have source := (certifiedSource?_eq_true_iff ctx).mp sourceTrue
    exact absurd equal
      (certifiedEntryCoherent_of_current_real ctx source.1)
  · split
    · rename_i coherentTrue
      exact absurd ((certifiedCoherent?_eq_true_iff ctx).mp coherentTrue)
        (fun coherent => coherent equal)
    · rfl

/-- A coherent context with a non-double incoming edge is a supported non-source. -/
theorem certifiedSourceUnit?_some_none_of_no_double {mol : RawMolecule} {center : ℕ}
    {root : ℕ} {ctx : CertifiedOwnerContext mol root}
    (coherent : CertifiedEntryCoherent ctx)
    (noDouble : mol.bondOrder ctx.previous.node.atom ctx.current.node.atom ≠ 2) :
    certifiedSourceUnit? mol center ctx = some none :=
  certifiedSourceUnit?_some_none_of_coherent_not_source coherent
    (fun source => noDouble source.2.2.2.2)

/-! ### Projections of the certified source condition -/

theorem certifiedSource_current_real {mol : RawMolecule} {center : ℕ} {root : ℕ}
    {ctx : CertifiedOwnerContext mol root} (source : CertifiedSource mol center ctx) :
    ctx.current.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom :=
  source.1

theorem certifiedSource_previous_real {mol : RawMolecule} {center : ℕ} {root : ℕ}
    {ctx : CertifiedOwnerContext mol root} (source : CertifiedSource mol center ctx) :
    ctx.previous.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom :=
  source.2.1

theorem certifiedSource_far_ne_center {mol : RawMolecule} {center : ℕ} {root : ℕ}
    {ctx : CertifiedOwnerContext mol root} (source : CertifiedSource mol center ctx) :
    ctx.current.node.atom ≠ center :=
  source.2.2.1

theorem certifiedSource_near_ne_center {mol : RawMolecule} {center : ℕ} {root : ℕ}
    {ctx : CertifiedOwnerContext mol root} (source : CertifiedSource mol center ctx) :
    ctx.previous.node.atom ≠ center :=
  source.2.2.2.1

theorem certifiedSource_double {mol : RawMolecule} {center : ℕ} {root : ℕ}
    {ctx : CertifiedOwnerContext mol root} (source : CertifiedSource mol center ctx) :
    mol.bondOrder ctx.previous.node.atom ctx.current.node.atom = 2 :=
  source.2.2.2.2

/-- Every certified source context is coherent, derived from the real far occurrence. -/
theorem certifiedSource_entry_coherent {mol : RawMolecule} {center : ℕ} {root : ℕ}
    {ctx : CertifiedOwnerContext mol root} (source : CertifiedSource mol center ctx) :
    CertifiedEntryCoherent ctx :=
  certifiedEntryCoherent_of_current_real ctx (certifiedSource_current_real source)

/-- The runtime coherence guard passes on every actual source context.  It is a derived
consequence of the five source guards, not an additional premise. -/
theorem certifiedCoherent?_of_source {mol : RawMolecule} {center : ℕ} {root : ℕ}
    {ctx : CertifiedOwnerContext mol root} (source : CertifiedSource mol center ctx) :
    certifiedCoherent? ctx = true :=
  (certifiedCoherent?_eq_true_iff ctx).mpr (certifiedSource_entry_coherent source)

/-- Source totality without a coherence premise: the five old source guards alone produce the
owner-side unit, and the runtime coherence guard necessarily passes on the same data. -/
theorem certifiedSourceUnit?_of_source {mol : RawMolecule} {center : ℕ} {root : ℕ}
    {ctx : CertifiedOwnerContext mol root} (source : CertifiedSource mol center ctx) :
    certifiedSourceUnit? mol center ctx =
        some (some { near := ctx.previous.node.atom, far := ctx.current.node.atom,
                     entry? := some ctx.beforePrevious.node.atom }) ∧
      certifiedCoherent? ctx = true :=
  ⟨certifiedSourceUnit?_some_some_of_source source, certifiedCoherent?_of_source source⟩

/-- Any successful certified read is a certified source context. -/
theorem certifiedSource_of_some_some {mol : RawMolecule} {center : ℕ} {root : ℕ}
    (ctx : CertifiedOwnerContext mol root)
    {unit : ChemistryNormalizationResult.Rule3SourceUnit}
    (read : certifiedSourceUnit? mol center ctx = some (some unit)) :
    CertifiedSource mol center ctx := by
  unfold certifiedSourceUnit? at read
  split at read
  · rename_i sourceTrue
    exact (certifiedSource?_eq_true_iff ctx).mp sourceTrue
  · split at read <;> simp at read

/-- The near endpoint of a successful certified read is the near cursor atom. -/
theorem certifiedSourceUnit?_unit_near {mol : RawMolecule} {center : ℕ} {root : ℕ}
    (ctx : CertifiedOwnerContext mol root)
    {unit : ChemistryNormalizationResult.Rule3SourceUnit}
    (read : certifiedSourceUnit? mol center ctx = some (some unit)) :
    unit.near = ctx.previous.node.atom := by
  unfold certifiedSourceUnit? at read
  split at read
  · have unitEq :
        ({ near := ctx.previous.node.atom, far := ctx.current.node.atom,
           entry? := some ctx.beforePrevious.node.atom } :
          ChemistryNormalizationResult.Rule3SourceUnit) = unit :=
      Option.some.inj (Option.some.inj read)
    rw [← unitEq]
  · split at read <;> simp at read

/-- The far endpoint of a successful certified read is the far cursor atom. -/
theorem certifiedSourceUnit?_unit_far {mol : RawMolecule} {center : ℕ} {root : ℕ}
    (ctx : CertifiedOwnerContext mol root)
    {unit : ChemistryNormalizationResult.Rule3SourceUnit}
    (read : certifiedSourceUnit? mol center ctx = some (some unit)) :
    unit.far = ctx.current.node.atom := by
  unfold certifiedSourceUnit? at read
  split at read
  · have unitEq :
        ({ near := ctx.previous.node.atom, far := ctx.current.node.atom,
           entry? := some ctx.beforePrevious.node.atom } :
          ChemistryNormalizationResult.Rule3SourceUnit) = unit :=
      Option.some.inj (Option.some.inj read)
    rw [← unitEq]
  · split at read <;> simp at read

/-- The entry of a successful certified read is the atom of the actual cursor just before the
near endpoint: the owner-side breadcrumb, not a caller-supplied list element. -/
theorem certifiedSourceUnit?_unit_entry {mol : RawMolecule} {center : ℕ} {root : ℕ}
    (ctx : CertifiedOwnerContext mol root)
    {unit : ChemistryNormalizationResult.Rule3SourceUnit}
    (read : certifiedSourceUnit? mol center ctx = some (some unit)) :
    unit.entry? = some ctx.beforePrevious.node.atom := by
  unfold certifiedSourceUnit? at read
  split at read
  · have unitEq :
        ({ near := ctx.previous.node.atom, far := ctx.current.node.atom,
           entry? := some ctx.beforePrevious.node.atom } :
          ChemistryNormalizationResult.Rule3SourceUnit) = unit :=
      Option.some.inj (Option.some.inj read)
    rw [← unitEq]
  · split at read <;> simp at read

/-- The returned near/far pair is joined by the required double bond. -/
theorem certifiedSourceUnit?_unit_double {mol : RawMolecule} {center : ℕ} {root : ℕ}
    (ctx : CertifiedOwnerContext mol root)
    {unit : ChemistryNormalizationResult.Rule3SourceUnit}
    (read : certifiedSourceUnit? mol center ctx = some (some unit)) :
    mol.bondOrder unit.near unit.far = 2 := by
  have source := certifiedSource_of_some_some ctx read
  rw [certifiedSourceUnit?_unit_near ctx read, certifiedSourceUnit?_unit_far ctx read]
  exact certifiedSource_double source

/-- The returned entry is distinct from the far endpoint.  This is the exact `bondedrepeat`
defect of the old reader, now impossible on a successful certified read. -/
theorem certifiedSourceUnit?_unit_entry_ne_far {mol : RawMolecule} {center : ℕ} {root : ℕ}
    (ctx : CertifiedOwnerContext mol root)
    {unit : ChemistryNormalizationResult.Rule3SourceUnit}
    (read : certifiedSourceUnit? mol center ctx = some (some unit)) :
    ∀ entry, unit.entry? = some entry → entry ≠ unit.far := by
  intro entry entryEq
  have source := certifiedSource_of_some_some ctx read
  have coherent := certifiedSource_entry_coherent source
  have entryIs : entry = ctx.beforePrevious.node.atom := by
    rw [certifiedSourceUnit?_unit_entry ctx read] at entryEq
    exact (Option.some.inj entryEq).symm
  have farIs := certifiedSourceUnit?_unit_far ctx read
  rw [entryIs, farIs]
  exact coherent

/-- The returned entry is joined to the near endpoint by a written bond: the entry-near
adjacency is a consequence of the actual walk, not of the entry's history position. -/
theorem certifiedSourceUnit?_unit_entry_near_bonded {mol : RawMolecule} {center : ℕ} {root : ℕ}
    (ctx : CertifiedOwnerContext mol root)
    {unit : ChemistryNormalizationResult.Rule3SourceUnit}
    (read : certifiedSourceUnit? mol center ctx = some (some unit)) :
    ∀ entry, unit.entry? = some entry → 0 < mol.bondOrder entry unit.near := by
  intro entry entryEq
  have entryIs : entry = ctx.beforePrevious.node.atom := by
    rw [certifiedSourceUnit?_unit_entry ctx read] at entryEq
    exact (Option.some.inj entryEq).symm
  have nearIs := certifiedSourceUnit?_unit_near ctx read
  rw [entryIs, nearIs]
  exact certifiedEntry_near_bonded ctx

/-- The returned near atom is in range. -/
theorem certifiedSourceUnit?_unit_near_lt {mol : RawMolecule} {center : ℕ} {root : ℕ}
    (well : mol.WellFormed) (rootBound : root < mol.atomCount)
    (ctx : CertifiedOwnerContext mol root)
    {unit : ChemistryNormalizationResult.Rule3SourceUnit}
    (read : certifiedSourceUnit? mol center ctx = some (some unit)) :
    unit.near < mol.atomCount := by
  rw [certifiedSourceUnit?_unit_near ctx read]
  exact certified_previous_atom_lt well rootBound ctx

/-- The returned far atom is in range. -/
theorem certifiedSourceUnit?_unit_far_lt {mol : RawMolecule} {center : ℕ} {root : ℕ}
    (well : mol.WellFormed) (rootBound : root < mol.atomCount)
    (ctx : CertifiedOwnerContext mol root)
    {unit : ChemistryNormalizationResult.Rule3SourceUnit}
    (read : certifiedSourceUnit? mol center ctx = some (some unit)) :
    unit.far < mol.atomCount := by
  rw [certifiedSourceUnit?_unit_far ctx read]
  exact certified_current_atom_lt well rootBound ctx

/-- Every returned entry is an in-range atom: the old `[99]` owner cannot be surfaced. -/
theorem certifiedSourceUnit?_unit_entry_lt {mol : RawMolecule} {center : ℕ} {root : ℕ}
    (well : mol.WellFormed) (rootBound : root < mol.atomCount)
    (ctx : CertifiedOwnerContext mol root)
    {unit : ChemistryNormalizationResult.Rule3SourceUnit}
    (read : certifiedSourceUnit? mol center ctx = some (some unit)) :
    ∀ entry, unit.entry? = some entry → entry < mol.atomCount := by
  intro entry entryEq
  have entryIs : entry = ctx.beforePrevious.node.atom := by
    rw [certifiedSourceUnit?_unit_entry ctx read] at entryEq
    exact (Option.some.inj entryEq).symm
  rw [entryIs]
  exact certified_beforePrevious_atom_lt well rootBound ctx

/-! ## Directional behaviour on genuinely downward steps -/

/-- With two consecutive downward canonical steps, the historical entry
`(current.history.drop 2).head?` is exactly the certified entry `beforePrevious.atom`. -/
theorem certifiedEntry_eq_drop_two_of_downward {mol : RawMolecule} {root : ℕ}
    (ctx : CertifiedOwnerContext mol root)
    (previousStep : ctx.previous.node ∈ mol.canonicalChildren ctx.beforePrevious.node)
    (currentStep : ctx.current.node ∈ mol.canonicalChildren ctx.previous.node) :
    (ctx.current.node.history.drop 2).head? = some ctx.beforePrevious.node.atom := by
  rw [mol.canonicalChildren_history ctx.previous.node ctx.current.node currentStep,
    mol.canonicalChildren_history ctx.beforePrevious.node ctx.previous.node previousStep]
  simp [CanonicalCenterTreeNode.history_head (certified_beforePrevious_generated ctx)]

/-- With a downward last step the current cursor is directed in the historical sense. -/
theorem certifiedCurrent_directed_of_downward {mol : RawMolecule} {root : ℕ}
    (ctx : CertifiedOwnerContext mol root)
    (currentStep : ctx.current.node ∈ mol.canonicalChildren ctx.previous.node) :
    IsDirectedSourceCursor ctx.current := by
  refine ⟨ctx.previous.node, mem_children_previous? ctx.currentStep, ?_, ?_⟩
  · exact (canonicalChildren_parent mol currentStep).symm
  · rw [mol.canonicalChildren_history ctx.previous.node ctx.current.node currentStep]
    simp

/-- With two consecutive downward steps, a real current occurrence cannot revisit the entry
atom: the current atom is fresh in the previous history, while the entry atom is in it. -/
theorem certifiedEntry_ne_far_of_double_downward {mol : RawMolecule} {root : ℕ}
    (ctx : CertifiedOwnerContext mol root)
    (previousStep : ctx.previous.node ∈ mol.canonicalChildren ctx.beforePrevious.node)
    (currentStep : ctx.current.node ∈ mol.canonicalChildren ctx.previous.node)
    (real : ctx.current.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom) :
    ctx.beforePrevious.node.atom ≠ ctx.current.node.atom := by
  intro equal
  have notMem : ctx.current.node.atom ∉ ctx.previous.node.history :=
    real_child_not_mem_history currentStep real
  have atomMem : ctx.beforePrevious.node.atom ∈ ctx.previous.node.history := by
    rw [mol.canonicalChildren_history ctx.beforePrevious.node ctx.previous.node previousStep]
    exact List.mem_cons_of_mem _
      (List.mem_of_head? (CanonicalCenterTreeNode.history_head
        (certified_beforePrevious_generated ctx)))
  exact notMem (equal ▸ atomMem)

/-- On a genuinely downward two-step context the certified reader agrees with the production
cursor reader: the owner-side breadcrumb coincides with the predecessor's history entry. -/
theorem certifiedSourceUnit?_eq_cursorReader_of_downward {mol : RawMolecule} {center : ℕ}
    {root : ℕ} (ctx : CertifiedOwnerContext mol root)
    (previousStep : ctx.previous.node ∈ mol.canonicalChildren ctx.beforePrevious.node)
    (currentStep : ctx.current.node ∈ mol.canonicalChildren ctx.previous.node)
    (real : ctx.current.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (currentNe : ctx.current.node.atom ≠ center)
    (previousNe : ctx.previous.node.atom ≠ center)
    (double : mol.bondOrder ctx.previous.node.atom ctx.current.node.atom = 2) :
    certifiedSourceUnit? mol center ctx =
      some (cursorRule3SourceUnitOfNode? mol center ctx.current) := by
  have entryEq : (ctx.previous.node.history.drop 1).head? =
      some ctx.beforePrevious.node.atom := by
    rw [mol.canonicalChildren_history ctx.beforePrevious.node ctx.previous.node previousStep]
    simp [CanonicalCenterTreeNode.history_head (certified_beforePrevious_generated ctx)]
  have previousEq : ctx.current.previous? = some ctx.previous.node :=
    mem_children_previous? ctx.currentStep
  have cond : (ctx.current.node.provenance ==
        RawMolecule.CanonicalNodeProvenance.realAtom &&
        ctx.current.node.atom != center && ctx.previous.node.atom != center &&
        mol.bondOrder ctx.previous.node.atom ctx.current.node.atom == 2) = true := by
    simp [real, currentNe, previousNe, double]
  have cursorEq : cursorRule3SourceUnitOfNode? mol center ctx.current =
      some { near := ctx.previous.node.atom, far := ctx.current.node.atom,
             entry? := some ctx.beforePrevious.node.atom } := by
    simp only [cursorRule3SourceUnitOfNode?, previousEq]
    rw [if_pos cond, entryEq]
  have previousReal : ctx.previous.node.provenance =
      RawMolecule.CanonicalNodeProvenance.realAtom :=
    real_of_child_mem currentStep
  have source : CertifiedSource mol center ctx :=
    ⟨real, previousReal, currentNe, previousNe, double⟩
  have read := certifiedSourceUnit?_some_some_of_source source
  rw [read, cursorEq]

/-- On a genuinely downward two-step context the certified reader agrees with the historical
node reader as well (through the production directed-cursor bridge). -/
theorem certifiedSourceUnit?_eq_historicalReader_of_downward {mol : RawMolecule} {center : ℕ}
    {root : ℕ} (ctx : CertifiedOwnerContext mol root)
    (previousStep : ctx.previous.node ∈ mol.canonicalChildren ctx.beforePrevious.node)
    (currentStep : ctx.current.node ∈ mol.canonicalChildren ctx.previous.node)
    (real : ctx.current.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (currentNe : ctx.current.node.atom ≠ center)
    (previousNe : ctx.previous.node.atom ≠ center)
    (double : mol.bondOrder ctx.previous.node.atom ctx.current.node.atom = 2) :
    certifiedSourceUnit? mol center ctx =
      some (ChemistryNormalizationResult.rule3SourceUnitOfNode? mol center ctx.current.node) := by
  rw [certifiedSourceUnit?_eq_cursorReader_of_downward ctx previousStep currentStep real
    currentNe previousNe double]
  rw [cursorRule3SourceUnitOfNode?_eq_rule3SourceUnitOfNode?_of_directed
    (certifiedCurrent_directed_of_downward ctx currentStep)]

/-- Faithfulness of the geometry wrapper: it consumes exactly the unit read from the
certificate, at the read `near`, `far` and entry. -/
theorem certifiedEntryGeometry?_eq_of_reader_some
    {result : ChemistryNormalizationResult} {mol : RawMolecule} {center : ℕ} {root : ℕ}
    {ctx : CertifiedOwnerContext mol root}
    {unit : ChemistryNormalizationResult.Rule3SourceUnit}
    (read : certifiedSourceUnit? mol center ctx = some (some unit)) :
    certifiedEntryGeometry? result mol center ctx =
      match unit.entry? with
      | some entry =>
          ChemistryNormalizationResult.rule3EntryGeometry? result mol unit.near unit.far entry
      | none => none := by
  unfold certifiedEntryGeometry?
  rw [read]

/-! ## Fixtures: the actual upward and up-then-down traversals -/

/-- The shared atom-3 occurrence on the path from root `0`. -/
def fixtureNode3 : RawMolecule.CanonicalBranchNode :=
  { atom := 3, parent := 0, history := [3, 0],
    provenance := RawMolecule.CanonicalNodeProvenance.realAtom }

/-! ### Original fixture (`0 - 3 - 1 = 2 - 4`, reroot `4 → 2 → 1`) -/

theorem original_root3_step :
    fixtureNode3 ∈ ownerContextMolecule.canonicalChildren (canonicalCenterRoot 0) := by
  decide

theorem original_31_step :
    ownerContextNearNode ∈ ownerContextMolecule.canonicalChildren fixtureNode3 := by
  decide

theorem original_12_step :
    ownerContextFarNode ∈ ownerContextMolecule.canonicalChildren ownerContextNearNode := by
  decide

theorem original_24_step :
    ownerContextOwnerOccurrence ∈
      ownerContextMolecule.canonicalChildren ownerContextFarNode := by
  decide

theorem originalNode3_generated :
    CanonicalCenterTreeNode ownerContextMolecule 0 fixtureNode3 :=
  CanonicalCenterTreeNode.child CanonicalCenterTreeNode.root original_root3_step

theorem originalNearNode_generated :
    CanonicalCenterTreeNode ownerContextMolecule 0 ownerContextNearNode :=
  CanonicalCenterTreeNode.child originalNode3_generated original_31_step

theorem originalFarNode_generated :
    CanonicalCenterTreeNode ownerContextMolecule 0 ownerContextFarNode :=
  CanonicalCenterTreeNode.child originalNearNode_generated original_12_step

theorem originalOwner_generated :
    CanonicalCenterTreeNode ownerContextMolecule 0 ownerContextOwnerOccurrence :=
  CanonicalCenterTreeNode.child originalFarNode_generated original_24_step

/-- The owner cursor at the real owner occurrence, with no remembered predecessor. -/
def originalOwnerCursor : CanonicalRerootCursor :=
  { node := ownerContextOwnerOccurrence, previous? := none }

/-- The certified context of the original upward traversal.  The walk is the reflexive walk at
the owner occurrence; the two trailing steps are the actual generated cursor steps from the old
fixture (reused, not reproved by assumption). -/
def originalCertifiedContext : CertifiedOwnerContext ownerContextMolecule 0 :=
  { owner := ownerContextOwnerOccurrence
    ownerGenerated := originalOwner_generated
    ownerReal := rfl
    beforePrevious := originalOwnerCursor
    beforePreviousReal := rfl
    previous := ownerContextMidCursor
    current := ownerContextUpwardCursor
    ownerWalk := RerootWalk.refl
    previousStep := ownerContext_midCursor_generated
    currentStep := ownerContext_upwardCursor_generated }

theorem ownerContextMolecule_atomCount : ownerContextMolecule.atomCount = 5 := by
  decide

theorem ownerContextMolecule_wellFormed : ownerContextMolecule.WellFormed :=
  (wellFormed_iff_all_bondEndpointsOK ownerContextMolecule).mpr (by decide)

theorem ownerContextMolecule_rootBound : (0 : ℕ) < ownerContextMolecule.atomCount := by
  decide

theorem originalCertified_source :
    CertifiedSource ownerContextMolecule 0 originalCertifiedContext :=
  ⟨rfl, rfl, by decide, by decide, by decide⟩

/-- The certified original read: `near = 2`, `far = 1`, entry = owner-side atom `4`. -/
theorem originalCertified_read :
    certifiedSourceUnit? ownerContextMolecule 0 originalCertifiedContext =
      some (some { near := 2, far := 1, entry? := some 4 }) :=
  certifiedSourceUnit?_some_some_of_source originalCertified_source

/-- The certified original read coincides with the old owner-context reader on this actual
certified input: existing operational behaviour is preserved where the old reader was right. -/
theorem originalCertified_matches_ownerContextReader :
    certifiedSourceUnit? ownerContextMolecule 0 originalCertifiedContext =
      ownerContextRule3SourceUnitOfNode? ownerContextMolecule 0 ownerContext := by
  rw [originalCertified_read, ownerContext_reader_reads_correct_entry]

/-- The production cursor reader would report the historical entry `1`. -/
theorem originalCertified_cursorReader_reads_historical_entry :
    cursorRule3SourceUnitOfNode? ownerContextMolecule 0 ownerContextUpwardCursor =
      some { near := 2, far := 1, entry? := some 1 } := by
  decide

/-- The certified reader returns the owner-side entry, not the historical one. -/
theorem originalCertified_reader_differs_from_cursorReader :
    certifiedSourceUnit? ownerContextMolecule 0 originalCertifiedContext ≠
      some (cursorRule3SourceUnitOfNode? ownerContextMolecule 0 ownerContextUpwardCursor) := by
  rw [originalCertified_read, originalCertified_cursorReader_reads_historical_entry]
  decide

/-- The original first step (owner `4` to near `2`) is upward: atom `4` has no canonical
children, so the step goes to the recorded canonical parent. -/
theorem original_firstStep_upward :
    ownerContextFarNode ∉ ownerContextMolecule.canonicalChildren ownerContextOwnerOccurrence := by
  decide

/-- The original second step (`2` to `1`) is upward: atom `1` is the recorded canonical parent
of `2`, not one of `2`'s canonical children (the only atom-1 child is the multiple-bond
duplicate with a different history). -/
theorem original_secondStep_upward :
    ownerContextNearNode ∉ ownerContextMolecule.canonicalChildren ownerContextFarNode := by
  decide

/-- The old cursor is not downward-directed: the whole original traversal is upward. -/
theorem originalCertified_cursor_not_directed :
    isDirectedSourceCursor ownerContextUpwardCursor = false :=
  ownerContext_not_directed

/-- The returned original entry `4` is distinct from the far endpoint `1`. -/
theorem originalCertified_returned_entry_ne_far (entry : ℕ)
    (entryEq : ({ near := 2, far := 1, entry? := some 4 } :
      ChemistryNormalizationResult.Rule3SourceUnit).entry? = some entry) :
    entry ≠ 1 := by
  have h := certifiedSourceUnit?_unit_entry_ne_far originalCertifiedContext
    originalCertified_read entry entryEq
  simpa using h

/-- No successful original certified read can surface the old out-of-range owner `99`. -/
theorem originalCertified_no_entry_99 (entry : ℕ)
    (entryEq : ({ near := 2, far := 1, entry? := some 4 } :
      ChemistryNormalizationResult.Rule3SourceUnit).entry? = some entry) :
    entry ≠ 99 := by
  have bound := certifiedSourceUnit?_unit_entry_lt ownerContextMolecule_wellFormed
    ownerContextMolecule_rootBound originalCertifiedContext originalCertified_read entry entryEq
  rw [ownerContextMolecule_atomCount] at bound
  intro equal
  subst entry
  exact absurd bound (by decide)

/-- The returned original near/far pair is the required double bond. -/
theorem originalCertified_near_far_double :
    ownerContextMolecule.bondOrder 2 1 = 2 :=
  certifiedSourceUnit?_unit_double originalCertifiedContext originalCertified_read

/-- The returned original entry `4` is bonded to the near endpoint `2`. -/
theorem originalCertified_entry_near_bonded :
    0 < ownerContextMolecule.bondOrder 4 2 :=
  certifiedEntry_near_bonded originalCertifiedContext

/-! ### Turn fixture (`0 - 3 - 1 - 2`, owner `4` on `2`, double `2 = 5`) -/

theorem turn_root3_step :
    fixtureNode3 ∈ turnContextMolecule.canonicalChildren (canonicalCenterRoot 0) := by
  decide

theorem turn_31_step :
    ownerContextNearNode ∈ turnContextMolecule.canonicalChildren fixtureNode3 := by
  decide

theorem turn_12_step :
    turnContextNearNode ∈ turnContextMolecule.canonicalChildren ownerContextNearNode := by
  decide

theorem turn_24_step :
    turnContextOwnerOccurrence ∈ turnContextMolecule.canonicalChildren turnContextNearNode := by
  decide

theorem turn_25_step :
    turnContextFarNode ∈ turnContextMolecule.canonicalChildren turnContextNearNode := by
  decide

theorem turnNode3_generated :
    CanonicalCenterTreeNode turnContextMolecule 0 fixtureNode3 :=
  CanonicalCenterTreeNode.child CanonicalCenterTreeNode.root turn_root3_step

theorem turnNode1_generated :
    CanonicalCenterTreeNode turnContextMolecule 0 ownerContextNearNode :=
  CanonicalCenterTreeNode.child turnNode3_generated turn_31_step

theorem turnNearNode_generated :
    CanonicalCenterTreeNode turnContextMolecule 0 turnContextNearNode :=
  CanonicalCenterTreeNode.child turnNode1_generated turn_12_step

theorem turnOwner_generated :
    CanonicalCenterTreeNode turnContextMolecule 0 turnContextOwnerOccurrence :=
  CanonicalCenterTreeNode.child turnNearNode_generated turn_24_step

theorem turnFarNode_generated :
    CanonicalCenterTreeNode turnContextMolecule 0 turnContextFarNode :=
  CanonicalCenterTreeNode.child turnNearNode_generated turn_25_step

/-- The turn owner cursor. -/
def turnOwnerCursor : CanonicalRerootCursor :=
  { node := turnContextOwnerOccurrence, previous? := none }

/-- The certified context of the up-then-down traversal. -/
def turnCertifiedContext : CertifiedOwnerContext turnContextMolecule 0 :=
  { owner := turnContextOwnerOccurrence
    ownerGenerated := turnOwner_generated
    ownerReal := rfl
    beforePrevious := turnOwnerCursor
    beforePreviousReal := rfl
    previous := turnContextMidCursor
    current := turnContextCursor
    ownerWalk := RerootWalk.refl
    previousStep := turnContext_midCursor_generated
    currentStep := turnContext_cursor_generated }

theorem turnContextMolecule_atomCount : turnContextMolecule.atomCount = 6 := by
  decide

theorem turnContextMolecule_wellFormed : turnContextMolecule.WellFormed :=
  (wellFormed_iff_all_bondEndpointsOK turnContextMolecule).mpr (by decide)

theorem turnContextMolecule_rootBound : (0 : ℕ) < turnContextMolecule.atomCount := by
  decide

theorem turnCertified_source :
    CertifiedSource turnContextMolecule 0 turnCertifiedContext :=
  ⟨rfl, rfl, by decide, by decide, by decide⟩

/-- The certified turn read: `near = 2`, `far = 5`, entry = owner-side atom `4`, despite the
up-then-down direction. -/
theorem turnCertified_read :
    certifiedSourceUnit? turnContextMolecule 0 turnCertifiedContext =
      some (some { near := 2, far := 5, entry? := some 4 }) :=
  certifiedSourceUnit?_some_some_of_source turnCertified_source

/-- The certified turn read coincides with the old owner-context reader on this actual certified
input. -/
theorem turnCertified_matches_ownerContextReader :
    certifiedSourceUnit? turnContextMolecule 0 turnCertifiedContext =
      ownerContextRule3SourceUnitOfNode? turnContextMolecule 0 turnContext := by
  rw [turnCertified_read, turnContext_reader_reads_correct_entry]

/-- The historical node reader on the turn far node reports the wrong entry `1`, which is the
entry the direction dispatch would have used. -/
theorem turnCertified_historicalReader_reads_wrong_entry :
    ChemistryNormalizationResult.rule3SourceUnitOfNode? turnContextMolecule 0
      turnContextFarNode = some { near := 2, far := 5, entry? := some 1 } :=
  turnContext_historicalReader_reads_wrong_entry

/-- The production cursor reader on the turn cursor also reports the historical entry `1`. -/
theorem turnCertified_cursorReader_reads_historical_entry :
    cursorRule3SourceUnitOfNode? turnContextMolecule 0 turnContextCursor =
      some { near := 2, far := 5, entry? := some 1 } := by
  decide

/-- The certified turn reader overrides the directed branch: the returned entry is `4`, while
the directed cursor reader returns `1`. -/
theorem turnCertified_reader_differs_from_cursorReader :
    certifiedSourceUnit? turnContextMolecule 0 turnCertifiedContext ≠
      some (cursorRule3SourceUnitOfNode? turnContextMolecule 0 turnContextCursor) := by
  rw [turnCertified_read, turnCertified_cursorReader_reads_historical_entry]
  decide

/-- The turn cursor itself is downward-directed (`previous.atom = node.parent` and the histories
agree), so the direction dispatch cannot distinguish it from a harmless downward cursor. -/
theorem turnCertified_cursor_directed :
    isDirectedSourceCursor turnContextCursor = true :=
  turnContext_directed

/-- The certified turn cursor is historically directed, yet its coherent owner-side entry is
required. -/
theorem turnCertified_current_directed :
    IsDirectedSourceCursor turnContextCursor :=
  certifiedCurrent_directed_of_downward turnCertifiedContext turn_25_step

/-- The turn first step is upward: the owner occurrence `4` is a leaf. -/
theorem turn_firstStep_upward :
    turnContextNearNode ∉ turnContextMolecule.canonicalChildren turnContextOwnerOccurrence := by
  decide

/-- The turn second step is downward. -/
theorem turn_secondStep_downward :
    turnContextFarNode ∈ turnContextMolecule.canonicalChildren turnContextNearNode :=
  turn_25_step

/-- The returned turn entry `4` is distinct from the far endpoint `5`. -/
theorem turnCertified_returned_entry_ne_far (entry : ℕ)
    (entryEq : ({ near := 2, far := 5, entry? := some 4 } :
      ChemistryNormalizationResult.Rule3SourceUnit).entry? = some entry) :
    entry ≠ 5 := by
  have h := certifiedSourceUnit?_unit_entry_ne_far turnCertifiedContext
    turnCertified_read entry entryEq
  simpa using h

/-- No successful turn certified read can surface the old out-of-range owner `99`. -/
theorem turnCertified_no_entry_99 (entry : ℕ)
    (entryEq : ({ near := 2, far := 5, entry? := some 4 } :
      ChemistryNormalizationResult.Rule3SourceUnit).entry? = some entry) :
    entry ≠ 99 := by
  have bound := certifiedSourceUnit?_unit_entry_lt turnContextMolecule_wellFormed
    turnContextMolecule_rootBound turnCertifiedContext turnCertified_read entry entryEq
  rw [turnContextMolecule_atomCount] at bound
  intro equal
  subst entry
  exact absurd bound (by decide)

/-- The returned turn near/far pair is the required double bond. -/
theorem turnCertified_near_far_double :
    turnContextMolecule.bondOrder 2 5 = 2 :=
  certifiedSourceUnit?_unit_double turnCertifiedContext turnCertified_read

/-- The returned turn entry `4` is bonded to the near endpoint `2`. -/
theorem turnCertified_entry_near_bonded :
    0 < turnContextMolecule.bondOrder 4 2 :=
  certifiedEntry_near_bonded turnCertifiedContext










/-- Defect 1: the singleton owner list `[99]` together with a malformed predecessor (empty
history) is accepted, returning the out-of-range entry `99`. -/
theorem oldReader_accepts_singleton_owner_99 :
    ownerContextRule3SourceUnitOfNode? ownerContextMolecule 0
      { ownerHistory := [99],
        cursor :=
          { node := ownerContextNearNode,
            previous? := some
              { atom := 2, parent := 1, history := [],
                provenance := RawMolecule.CanonicalNodeProvenance.realAtom } } } =
      some (some { near := 2, far := 1, entry? := some 99 }) := by
  decide

/-- Defect 2: the prefix `[99, 4, 2, 1, 3, 0]` is skipped by the suffix search, and the reader
returns the entry `4` as if the invalid prefix did not exist. -/
theorem oldReader_skips_invalid_prefix :
    ownerContextRule3SourceUnitOfNode? ownerContextMolecule 0
      { ownerHistory := [99, 4, 2, 1, 3, 0], cursor := ownerContextUpwardCursor } =
      some (some { near := 2, far := 1, entry? := some 4 }) := by
  decide

/-- Defect 3: the bonded repeat history `[4, 2, 5, 2, 1, 3, 0]` is accepted on the turn fixture
and returns entry `5`, which is exactly the far endpoint of the double bond. -/
theorem oldReader_accepts_bonded_repeat_entry_far :
    ownerContextRule3SourceUnitOfNode? turnContextMolecule 0
      { ownerHistory := [4, 2, 5, 2, 1, 3, 0], cursor := turnContextCursor } =
      some (some { near := 2, far := 5, entry? := some 5 }) := by
  decide

/-- The old reader's defect-2 result is exactly the genuine owner-side entry `4`: the problem is
that the invalid prefix is not rejected, not that the atom is wrong.  The certified reader
rejects only contexts that are actually incoherent; it never needs to search a list. -/
theorem oldReader_prefix_result_is_owner_entry :
    ownerContextRule3SourceUnitOfNode? ownerContextMolecule 0
      { ownerHistory := [99, 4, 2, 1, 3, 0], cursor := ownerContextUpwardCursor } =
      some (some { near := 2, far := 1, entry? := some 4 }) :=
  oldReader_skips_invalid_prefix

/-! ## Kernel-authority guards -/

assert_kernel_only RerootWalk
assert_kernel_only CertifiedOwnerContext
assert_kernel_only CertifiedEntryCoherent
assert_kernel_only CertifiedSource
assert_kernel_only certifiedEntryCoherentDecidable
assert_kernel_only certifiedSourceDecidable
assert_kernel_only certifiedCoherent?
assert_kernel_only certifiedSource?
assert_kernel_only certifiedSourceUnit?
assert_kernel_only certifiedEntryGeometry?
assert_kernel_only mem_children_spec
assert_kernel_only mem_children_neighbor
assert_kernel_only mem_children_previous?
assert_kernel_only canonicalChildren_parent
assert_kernel_only canonicalChildren_bondOrder_pos
assert_kernel_only generated_node_atom_lt
assert_kernel_only mem_children_node_generated
assert_kernel_only rerootWalk_generated
assert_kernel_only certified_beforePrevious_generated
assert_kernel_only certified_previous_generated
assert_kernel_only certified_current_generated
assert_kernel_only certified_owner_atom_lt
assert_kernel_only certified_beforePrevious_atom_lt
assert_kernel_only certified_previous_atom_lt
assert_kernel_only certified_current_atom_lt
assert_kernel_only canonicalChildren_atom_ne_parent
assert_kernel_only certifiedEntry_near_bonded
assert_kernel_only certifiedEntry_ne_near
assert_kernel_only certifiedEntryCoherent_of_current_real
assert_kernel_only certifiedOwner_pathOK
assert_kernel_only certifiedOwner_history_nodup
assert_kernel_only certifiedOwner_history_atoms_lt
assert_kernel_only certifiedCoherent?_eq_true_iff
assert_kernel_only certifiedSource?_eq_true_iff
assert_kernel_only certifiedSourceUnit?_some_some_of_source
assert_kernel_only certifiedSourceUnit?_some_none_of_coherent_not_source
assert_kernel_only certifiedSourceUnit?_none_of_not_coherent
assert_kernel_only certifiedSourceUnit?_none_of_entry_eq_far
assert_kernel_only certifiedSourceUnit?_some_none_of_no_double
assert_kernel_only certifiedSource_entry_coherent
assert_kernel_only certifiedCoherent?_of_source
assert_kernel_only certifiedSourceUnit?_of_source
assert_kernel_only certifiedSource_current_real
assert_kernel_only certifiedSource_previous_real
assert_kernel_only certifiedSource_far_ne_center
assert_kernel_only certifiedSource_near_ne_center
assert_kernel_only certifiedSource_double
assert_kernel_only certifiedSource_of_some_some
assert_kernel_only certifiedSourceUnit?_unit_near
assert_kernel_only certifiedSourceUnit?_unit_far
assert_kernel_only certifiedSourceUnit?_unit_entry
assert_kernel_only certifiedSourceUnit?_unit_double
assert_kernel_only certifiedSourceUnit?_unit_entry_ne_far
assert_kernel_only certifiedSourceUnit?_unit_entry_near_bonded
assert_kernel_only certifiedSourceUnit?_unit_near_lt
assert_kernel_only certifiedSourceUnit?_unit_far_lt
assert_kernel_only certifiedSourceUnit?_unit_entry_lt
assert_kernel_only certifiedEntry_eq_drop_two_of_downward
assert_kernel_only certifiedCurrent_directed_of_downward
assert_kernel_only certifiedEntry_ne_far_of_double_downward
assert_kernel_only certifiedSourceUnit?_eq_cursorReader_of_downward
assert_kernel_only certifiedSourceUnit?_eq_historicalReader_of_downward
assert_kernel_only certifiedEntryGeometry?_eq_of_reader_some
assert_kernel_only original_root3_step
assert_kernel_only original_31_step
assert_kernel_only original_12_step
assert_kernel_only original_24_step
assert_kernel_only originalNode3_generated
assert_kernel_only originalNearNode_generated
assert_kernel_only originalFarNode_generated
assert_kernel_only originalOwner_generated
assert_kernel_only ownerContextMolecule_atomCount
assert_kernel_only ownerContextMolecule_wellFormed
assert_kernel_only ownerContextMolecule_rootBound
assert_kernel_only originalCertified_source
assert_kernel_only originalCertified_read
assert_kernel_only originalCertified_matches_ownerContextReader
assert_kernel_only originalCertified_cursorReader_reads_historical_entry
assert_kernel_only originalCertified_reader_differs_from_cursorReader
assert_kernel_only original_firstStep_upward
assert_kernel_only original_secondStep_upward
assert_kernel_only originalCertified_cursor_not_directed
assert_kernel_only originalCertified_returned_entry_ne_far
assert_kernel_only originalCertified_no_entry_99
assert_kernel_only originalCertified_near_far_double
assert_kernel_only originalCertified_entry_near_bonded
assert_kernel_only turn_root3_step
assert_kernel_only turn_31_step
assert_kernel_only turn_12_step
assert_kernel_only turn_24_step
assert_kernel_only turn_25_step
assert_kernel_only turnNode3_generated
assert_kernel_only turnNode1_generated
assert_kernel_only turnNearNode_generated
assert_kernel_only turnOwner_generated
assert_kernel_only turnFarNode_generated
assert_kernel_only turnContextMolecule_atomCount
assert_kernel_only turnContextMolecule_wellFormed
assert_kernel_only turnContextMolecule_rootBound
assert_kernel_only turnCertified_source
assert_kernel_only turnCertified_read
assert_kernel_only turnCertified_matches_ownerContextReader
assert_kernel_only turnCertified_historicalReader_reads_wrong_entry
assert_kernel_only turnCertified_cursorReader_reads_historical_entry
assert_kernel_only turnCertified_reader_differs_from_cursorReader
assert_kernel_only turnCertified_cursor_directed
assert_kernel_only turnCertified_current_directed
assert_kernel_only turn_firstStep_upward
assert_kernel_only turn_secondStep_downward
assert_kernel_only turnCertified_returned_entry_ne_far
assert_kernel_only turnCertified_no_entry_99
assert_kernel_only turnCertified_near_far_double
assert_kernel_only turnCertified_entry_near_bonded
assert_kernel_only oldReader_accepts_singleton_owner_99
assert_kernel_only oldReader_skips_invalid_prefix
assert_kernel_only oldReader_accepts_bonded_repeat_entry_far
assert_kernel_only oldReader_prefix_result_is_owner_entry

end TetraStereo.OneCenter.CertifiedOwnerContextRule3Source
