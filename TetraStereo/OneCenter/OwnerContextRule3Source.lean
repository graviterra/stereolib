


















































import TetraStereo.OneCenter.OccurrencePreRule4bComparator
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.OwnerContextRule3Source

open TetraStereo.OneCenter
open TetraStereo.OneCenter.OccurrencePreRule4b

/-! ## Owner-centre context -/

/-- The owner-centre context that makes an upward Rule-3 source read well-defined.

`ownerHistory` is the canonical history of the owning occurrence: it starts at the owning atom and
ends at the stereogenic-unit root.  `cursor` is the actual zipper cursor after rerooting.  Together
they record the atom through which the traversal arrived at the cursor's predecessor -- the piece
of information the predecessor's own history does not contain. -/
structure Rule3OwnerContext where
  ownerHistory : List ℕ
  cursor : CanonicalRerootCursor
  deriving DecidableEq, Repr

/-! ## Validated owner path -/

/-- A list of atom indices is a real bonded path when every consecutive pair names distinct
in-bounds atoms joined by a written bond.  This is what distinguishes a genuine owner-centre
history from an arbitrary list such as `[99, 2, 1, 3, 0]`. -/
def validOwnerPath (mol : RawMolecule) : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest =>
      a < mol.atoms.length && b < mol.atoms.length &&
        mol.bondOrder a b > 0 && validOwnerPath mol (b :: rest)

/-- The owner-side predecessor of `previous` on `ownerHistory`: the atom immediately before
`previous.atom` when `previous.history` is a suffix of `ownerHistory`, and `none` otherwise.

This is the traversal breadcrumb.  It supports deep traversals, not only the two-step prefix
`previous.history = ownerHistory.drop 1`, because it recurses along the owner history until the
stored history matches a suffix. -/
def ownerPredecessorAtom? (ownerHistory : List ℕ)
    (previous : RawMolecule.CanonicalBranchNode) : Option ℕ :=
  match ownerHistory with
  | [] => none
  | owner :: rest =>
      if previous.history == rest then some owner
      else ownerPredecessorAtom? rest previous

/-! ## Owner-context source reader -/

/-- The source-bound Rule-3 unit of one cursor under an owner-centre context.

The entry is derived uniformly from the validated owner-to-current path: when the stored
predecessor lies on the owner history (`ownerPredecessorAtom?` returns the atom immediately before
it), the unit is read with `near = previous.atom`, `far = cursor.node.atom` and that entry, after
checking that the owner path is a real bonded path and that the incoming edge is the required
double bond between two real non-centre atoms.

Direction is only a fallback: when the predecessor is *not* on the owner path, a downward-directed
cursor is read historically (agreeing with the production directed-only observer), and any other
cursor is unsupported. -/
def ownerContextRule3SourceUnitOfNode? (mol : RawMolecule) (center : ℕ)
    (ctx : Rule3OwnerContext) :
    Option (Option ChemistryNormalizationResult.Rule3SourceUnit) :=
  match ctx.cursor.previous? with
  | none => some none
  | some previous =>
      match ownerPredecessorAtom? ctx.ownerHistory previous with
      | some owner =>
          if validOwnerPath mol (owner :: previous.history) then
            if ctx.cursor.node.provenance == RawMolecule.CanonicalNodeProvenance.realAtom &&
                previous.provenance == RawMolecule.CanonicalNodeProvenance.realAtom &&
                ctx.cursor.node.atom != center && previous.atom != center &&
                mol.bondOrder previous.atom ctx.cursor.node.atom == 2 then
              some (some { near := previous.atom, far := ctx.cursor.node.atom,
                           entry? := some owner })
            else some none
          else none
      | none =>
          if isDirectedSourceCursor ctx.cursor then
            some (ChemistryNormalizationResult.rule3SourceUnitOfNode? mol center ctx.cursor.node)
          else none

/-! ## Reader laws -/

/-- A valid owner-aligned context extracts the correct entry: `near = previous.atom`,
`far = cursor.node.atom`, and the entry is the owner-side predecessor of `previous`, uniformly
whether or not the cursor edge faces up or down. -/
theorem ownerContextRule3SourceUnitOfNode?_some_of_ownerAligned
    {mol : RawMolecule} {center : ℕ} {ctx : Rule3OwnerContext}
    {previous : RawMolecule.CanonicalBranchNode} {owner : ℕ}
    (hPrev : ctx.cursor.previous? = some previous)
    (hPred : ownerPredecessorAtom? ctx.ownerHistory previous = some owner)
    (hValid : validOwnerPath mol (owner :: previous.history) = true)
    (hReal : ctx.cursor.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (hPrevReal : previous.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (hNodeNe : ctx.cursor.node.atom ≠ center)
    (hPrevNe : previous.atom ≠ center)
    (hDouble : mol.bondOrder previous.atom ctx.cursor.node.atom = 2) :
    ownerContextRule3SourceUnitOfNode? mol center ctx =
      some (some { near := previous.atom, far := ctx.cursor.node.atom, entry? := some owner }) := by
  simp [ownerContextRule3SourceUnitOfNode?, hPrev, hPred, hValid, hReal, hPrevReal, hNodeNe,
    hPrevNe, hDouble]

/-- A supported but non-source cursor is the determinate `some none`: owner-aligned with a real
path, but the incoming edge is not the required double bond. -/
theorem ownerContextRule3SourceUnitOfNode?_some_none_of_ownerAligned_no_double
    {mol : RawMolecule} {center : ℕ} {ctx : Rule3OwnerContext}
    {previous : RawMolecule.CanonicalBranchNode} {owner : ℕ}
    (hPrev : ctx.cursor.previous? = some previous)
    (hPred : ownerPredecessorAtom? ctx.ownerHistory previous = some owner)
    (hValid : validOwnerPath mol (owner :: previous.history) = true)
    (hNoDouble : mol.bondOrder previous.atom ctx.cursor.node.atom ≠ 2) :
    ownerContextRule3SourceUnitOfNode? mol center ctx = some none := by
  have hNoDoubleBool : (mol.bondOrder previous.atom ctx.cursor.node.atom == 2) = false :=
    beq_false_of_ne hNoDouble
  simp [ownerContextRule3SourceUnitOfNode?, hPrev, hPred, hValid, hNoDoubleBool]

/-- An owner-aligned cursor whose owner path is not a real bonded path is rejected with the outer
`none`: an arbitrary owner history must not fabricate an entry. -/
theorem ownerContextRule3SourceUnitOfNode?_none_of_invalid_owner_path
    {mol : RawMolecule} {center : ℕ} {ctx : Rule3OwnerContext}
    {previous : RawMolecule.CanonicalBranchNode} {owner : ℕ}
    (hPrev : ctx.cursor.previous? = some previous)
    (hPred : ownerPredecessorAtom? ctx.ownerHistory previous = some owner)
    (hInvalid : validOwnerPath mol (owner :: previous.history) = false) :
    ownerContextRule3SourceUnitOfNode? mol center ctx = none := by
  simp [ownerContextRule3SourceUnitOfNode?, hPrev, hPred, hInvalid]

/-- A cursor whose predecessor is not on the owner path and that is not downward-directed is
unsupported (outer `none`). -/
theorem ownerContextRule3SourceUnitOfNode?_none_of_not_ownerAligned_not_directed
    {mol : RawMolecule} {center : ℕ} {ctx : Rule3OwnerContext}
    {previous : RawMolecule.CanonicalBranchNode}
    (hPrev : ctx.cursor.previous? = some previous)
    (hPred : ownerPredecessorAtom? ctx.ownerHistory previous = none)
    (hNotDirected : isDirectedSourceCursor ctx.cursor = false) :
    ownerContextRule3SourceUnitOfNode? mol center ctx = none := by
  simp [ownerContextRule3SourceUnitOfNode?, hPrev, hPred, hNotDirected]

/-- A root cursor (no incoming edge) is a determinate non-source. -/
theorem ownerContextRule3SourceUnitOfNode?_some_none_of_no_previous
    {mol : RawMolecule} {center : ℕ} {ctx : Rule3OwnerContext}
    (hNoPrev : ctx.cursor.previous? = none) :
    ownerContextRule3SourceUnitOfNode? mol center ctx = some none := by
  simp [ownerContextRule3SourceUnitOfNode?, hNoPrev]

/-- On a downward-directed cursor whose predecessor is not on the owner path, the reader agrees
with the historical reader (and hence with the production directed-only observer). -/
theorem ownerContextRule3SourceUnitOfNode?_eq_some_of_directed
    {mol : RawMolecule} {center : ℕ} {ctx : Rule3OwnerContext}
    {previous : RawMolecule.CanonicalBranchNode}
    (hPrev : ctx.cursor.previous? = some previous)
    (hPred : ownerPredecessorAtom? ctx.ownerHistory previous = none)
    (directed : IsDirectedSourceCursor ctx.cursor) :
    ownerContextRule3SourceUnitOfNode? mol center ctx =
      some (ChemistryNormalizationResult.rule3SourceUnitOfNode? mol center ctx.cursor.node) := by
  have hDir : isDirectedSourceCursor ctx.cursor = true :=
    (isDirectedSourceCursor_eq_true_iff ctx.cursor).mpr directed
  simp [ownerContextRule3SourceUnitOfNode?, hPrev, hPred, hDir]

/-- The same directed agreement expressed against the production cursor reader. -/
theorem ownerContextRule3SourceUnitOfNode?_eq_some_cursorReader_of_directed
    {mol : RawMolecule} {center : ℕ} {ctx : Rule3OwnerContext}
    {previous : RawMolecule.CanonicalBranchNode}
    (hPrev : ctx.cursor.previous? = some previous)
    (hPred : ownerPredecessorAtom? ctx.ownerHistory previous = none)
    (directed : IsDirectedSourceCursor ctx.cursor) :
    ownerContextRule3SourceUnitOfNode? mol center ctx =
      some (cursorRule3SourceUnitOfNode? mol center ctx.cursor) := by
  simp [ownerContextRule3SourceUnitOfNode?_eq_some_of_directed hPrev hPred directed,
    cursorRule3SourceUnitOfNode?_eq_rule3SourceUnitOfNode?_of_directed directed]

/-! ## Entry-relative geometry orientation -/

/-- Entry-relative Rule-3 geometry of the unit read from an owner context: the *read* entry (never
an assumed one) is handed to `rule3EntryGeometry?` together with the read `near`/`far` endpoints. -/
def ownerContextRule3EntryGeometry? (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (center : ℕ) (ctx : Rule3OwnerContext) : Option OfficialRule3Geometry :=
  match ownerContextRule3SourceUnitOfNode? mol center ctx with
  | some (some unit) =>
      match unit.entry? with
      | some entry =>
          ChemistryNormalizationResult.rule3EntryGeometry? result mol unit.near unit.far entry
      | none => none
  | _ => none

/-- Faithfulness of the geometry wrapper: it consumes exactly the unit read from the context, and
relates the geometry to `rule3EntryGeometry?` at the *read* `near`, `far` and entry -- no entry is
assumed anywhere on the path from the reader to the geometry. -/
theorem ownerContextRule3EntryGeometry?_eq_of_reader_some
    {result : ChemistryNormalizationResult} {mol : RawMolecule} {center : ℕ}
    {ctx : Rule3OwnerContext} {unit : ChemistryNormalizationResult.Rule3SourceUnit}
    (hReader : ownerContextRule3SourceUnitOfNode? mol center ctx = some (some unit)) :
    ownerContextRule3EntryGeometry? result mol center ctx =
      match unit.entry? with
      | some entry => ChemistryNormalizationResult.rule3EntryGeometry? result mol unit.near unit.far
          entry
      | none => none := by
  simp [ownerContextRule3EntryGeometry?, hReader]






/-! ### Original counterexample: `0 - 3 - 1 = 2 - 4`, reroot `4 → 2 → 1` -/

/-- Molecule: five carbons; bonds `0-3` single, `3-1` single, `1=2` double, `2-4` single. -/
def ownerContextMolecule : RawMolecule :=
  { atoms := [AtomSpec.aliphatic Element.C, AtomSpec.aliphatic Element.C,
              AtomSpec.aliphatic Element.C, AtomSpec.aliphatic Element.C,
              AtomSpec.aliphatic Element.C],
    bonds := [{ source := 0, target := 3, kind := ParsedBondKind.single },
              { source := 3, target := 1, kind := ParsedBondKind.single },
              { source := 1, target := 2, kind := ParsedBondKind.double },
              { source := 2, target := 4, kind := ParsedBondKind.single }] }

/-- The owner-centre occurrence history: starts at atom `4`, ends at root `0`. -/
def ownerContextOwnerHistory : List ℕ := [4, 2, 1, 3, 0]

/-- The owner-centre occurrence node (atom `4`). -/
def ownerContextOwnerOccurrence : RawMolecule.CanonicalBranchNode :=
  { atom := 4, parent := 2, history := [4, 2, 1, 3, 0],
    provenance := RawMolecule.CanonicalNodeProvenance.realAtom }

/-- The near node (atom `1`): the double-bond end toward the root. -/
def ownerContextNearNode : RawMolecule.CanonicalBranchNode :=
  { atom := 1, parent := 3, history := [1, 3, 0],
    provenance := RawMolecule.CanonicalNodeProvenance.realAtom }

/-- The far node (atom `2`): the double-bond end toward the owner occurrence. -/
def ownerContextFarNode : RawMolecule.CanonicalBranchNode :=
  { atom := 2, parent := 1, history := [2, 1, 3, 0],
    provenance := RawMolecule.CanonicalNodeProvenance.realAtom }

/-- The intermediate cursor produced by the first reroot step `4 → 2`. -/
def ownerContextMidCursor : CanonicalRerootCursor :=
  { node := ownerContextFarNode, previous? := some ownerContextOwnerOccurrence }

/-- The final cursor produced by the second reroot step `2 → 1`: node `1`, predecessor `2`. -/
def ownerContextUpwardCursor : CanonicalRerootCursor :=
  { node := ownerContextNearNode, previous? := some ownerContextFarNode }

/-- The full owner context: owner history `[4, 2, 1, 3, 0]` plus the generated upward cursor. -/
def ownerContext : Rule3OwnerContext :=
  { ownerHistory := ownerContextOwnerHistory, cursor := ownerContextUpwardCursor }

/-! ### Turn counterexample: tree `0 - 3 - 1 - 2`, owner `4` on `2`, double `2 = 5` -/

/-- Molecule: six carbons; bonds `0-3`, `3-1`, `1-2`, `2-4` single and `2=5` double. -/
def turnContextMolecule : RawMolecule :=
  { atoms := [AtomSpec.aliphatic Element.C, AtomSpec.aliphatic Element.C,
              AtomSpec.aliphatic Element.C, AtomSpec.aliphatic Element.C,
              AtomSpec.aliphatic Element.C, AtomSpec.aliphatic Element.C],
    bonds := [{ source := 0, target := 3, kind := ParsedBondKind.single },
              { source := 3, target := 1, kind := ParsedBondKind.single },
              { source := 1, target := 2, kind := ParsedBondKind.single },
              { source := 2, target := 4, kind := ParsedBondKind.single },
              { source := 2, target := 5, kind := ParsedBondKind.double }] }

/-- The owner-centre occurrence node (atom `4`), same history as the original example. -/
def turnContextOwnerOccurrence : RawMolecule.CanonicalBranchNode :=
  { atom := 4, parent := 2, history := [4, 2, 1, 3, 0],
    provenance := RawMolecule.CanonicalNodeProvenance.realAtom }

/-- The near node (atom `2`): the double-bond end through which the walk entered. -/
def turnContextNearNode : RawMolecule.CanonicalBranchNode :=
  { atom := 2, parent := 1, history := [2, 1, 3, 0],
    provenance := RawMolecule.CanonicalNodeProvenance.realAtom }

/-- The far node (atom `5`): the double-bond partner reached after the turn. -/
def turnContextFarNode : RawMolecule.CanonicalBranchNode :=
  { atom := 5, parent := 2, history := [5, 2, 1, 3, 0],
    provenance := RawMolecule.CanonicalNodeProvenance.realAtom }

/-- The intermediate cursor produced by the first reroot step `4 → 2`. -/
def turnContextMidCursor : CanonicalRerootCursor :=
  { node := turnContextNearNode, previous? := some turnContextOwnerOccurrence }

/-- The final cursor produced by the second reroot step `2 → 5`: node `5`, predecessor `2`. -/
def turnContextCursor : CanonicalRerootCursor :=
  { node := turnContextFarNode, previous? := some turnContextNearNode }

/-- The full owner context for the turn example. -/
def turnContext : Rule3OwnerContext :=
  { ownerHistory := ownerContextOwnerHistory, cursor := turnContextCursor }

/-! ### Fixture facts (all kernel-reducible `decide` proofs) -/

/-- The original fixture's molecular path is real. -/
theorem ownerContextMolecule_bondOrders :
    ownerContextMolecule.bondOrder 0 3 = 1 ∧
    ownerContextMolecule.bondOrder 3 1 = 1 ∧
    ownerContextMolecule.bondOrder 1 2 = 2 ∧
    ownerContextMolecule.bondOrder 2 4 = 1 ∧
    ownerContextMolecule.bondOrder 2 1 = 2 := by
  decide

/-- The turn fixture's molecular path is real, including the double bond `2 = 5`. -/
theorem turnContextMolecule_bondOrders :
    turnContextMolecule.bondOrder 0 3 = 1 ∧
    turnContextMolecule.bondOrder 3 1 = 1 ∧
    turnContextMolecule.bondOrder 1 2 = 1 ∧
    turnContextMolecule.bondOrder 2 4 = 1 ∧
    turnContextMolecule.bondOrder 2 5 = 2 ∧
    turnContextMolecule.bondOrder 5 2 = 2 := by
  decide

/-- The owner history facts used by the reader: head is `4`, tail is the far node's history. -/
theorem ownerContext_ownerHistory_facts :
    ownerContextOwnerHistory.head? = some 4 ∧
    ownerContextOwnerHistory.drop 1 = [2, 1, 3, 0] := by
  decide

/-- The near node is the actual recovered original parent of the far node. -/
theorem ownerContext_farNode_originalParent :
    canonicalOriginalParent? ownerContextFarNode = some ownerContextNearNode := by
  decide

/-- First reroot step `4 → 2` is actually generated by the zipper. -/
theorem ownerContext_midCursor_generated :
    ownerContextMidCursor ∈
      ({ node := ownerContextOwnerOccurrence } : CanonicalRerootCursor).children
        ownerContextMolecule := by
  decide

/-- Second reroot step `2 → 1` is actually generated by the zipper. -/
theorem ownerContext_upwardCursor_generated :
    ownerContextUpwardCursor ∈ ownerContextMidCursor.children ownerContextMolecule := by
  decide

/-- The whole two-step traversal `4 → 2 → 1` is generated. -/
theorem ownerContext_upwardCursor_actually_generated :
    ∃ mid : CanonicalRerootCursor,
      mid ∈ ({ node := ownerContextOwnerOccurrence } : CanonicalRerootCursor).children
        ownerContextMolecule ∧
      ownerContextUpwardCursor ∈ mid.children ownerContextMolecule := by
  refine ⟨ownerContextMidCursor, ownerContext_midCursor_generated,
    ownerContext_upwardCursor_generated⟩

/-- First reroot step of the turn example `4 → 2` is actually generated by the zipper. -/
theorem turnContext_midCursor_generated :
    turnContextMidCursor ∈
      ({ node := turnContextOwnerOccurrence } : CanonicalRerootCursor).children
        turnContextMolecule := by
  decide

/-- Second reroot step of the turn example `2 → 5` is actually generated by the zipper. -/
theorem turnContext_cursor_generated :
    turnContextCursor ∈ turnContextMidCursor.children turnContextMolecule := by
  decide

/-- The whole turn traversal `4 → 2 → 5` is generated. -/
theorem turnContext_cursor_actually_generated :
    ∃ mid : CanonicalRerootCursor,
      mid ∈ ({ node := turnContextOwnerOccurrence } : CanonicalRerootCursor).children
        turnContextMolecule ∧
      turnContextCursor ∈ mid.children turnContextMolecule := by
  refine ⟨turnContextMidCursor, turnContext_midCursor_generated,
    turnContext_cursor_generated⟩

/-- The original generated cursor is not downward-directed. -/
theorem ownerContext_not_directed :
    isDirectedSourceCursor ownerContextUpwardCursor = false := by
  decide

/-- The turn generated cursor *is* downward-directed, yet the entry must still come from the owner
side -- this is exactly the up-then-down defect that a direction dispatch would misread. -/
theorem turnContext_directed :
    isDirectedSourceCursor turnContextCursor = true := by
  decide

/-- The owner-side predecessor of the original far node is the owning occurrence `4`. -/
theorem ownerContext_aligned :
    ownerPredecessorAtom? ownerContextOwnerHistory ownerContextFarNode = some 4 := by
  decide

/-- The owner-side predecessor of the turn near node is the owning occurrence `4`. -/
theorem turnContext_aligned :
    ownerPredecessorAtom? ownerContextOwnerHistory turnContextNearNode = some 4 := by
  decide

/-- The original owner history is a real bonded path. -/
theorem ownerContext_valid_path :
    validOwnerPath ownerContextMolecule [4, 2, 1, 3, 0] = true := by
  decide

/-- The turn owner history is a real bonded path. -/
theorem turnContext_valid_path :
    validOwnerPath turnContextMolecule [4, 2, 1, 3, 0] = true := by
  decide



theorem ownerContext_historicalPreviousReader_reads_wrong_entry :
    ChemistryNormalizationResult.rule3SourceUnitOfNode? ownerContextMolecule 0
      ownerContextFarNode =
      some { near := 1, far := 2, entry? := some 3 } := by
  decide

/-- The historical reader on the turn far node reports the historical grandparent `1`, which is the
wrong entry: the walk entered through the owner `4`, not through the parent `1`. -/
theorem turnContext_historicalReader_reads_wrong_entry :
    ChemistryNormalizationResult.rule3SourceUnitOfNode? turnContextMolecule 0
      turnContextFarNode =
      some { near := 2, far := 5, entry? := some 1 } := by
  decide

/-- The repaired owner-context reader reads the correct original unit: `near = 2`, `far = 1`, entry
is the owning occurrence `4`. -/
theorem ownerContext_reader_reads_correct_entry :
    ownerContextRule3SourceUnitOfNode? ownerContextMolecule 0 ownerContext =
      some (some { near := 2, far := 1, entry? := some 4 }) := by
  decide

/-- The repaired owner-context reader reads the correct turn unit: `near = 2`, `far = 5`, entry is
the owning occurrence `4`, despite the cursor being downward-directed. -/
theorem turnContext_reader_reads_correct_entry :
    ownerContextRule3SourceUnitOfNode? turnContextMolecule 0 turnContext =
      some (some { near := 2, far := 5, entry? := some 4 }) := by
  decide


theorem ownerContext_oldProposal_differs_from_correct :
    ChemistryNormalizationResult.rule3SourceUnitOfNode? ownerContextMolecule 0
      ownerContextFarNode ≠ some { near := 2, far := 1, entry? := some 4 } := by
  decide

/-- The repaired turn reader and the historical reader return different results: the direction
dispatch would have let the directed branch win and produce the wrong entry `1`. -/
theorem turnContext_reader_differs_from_historical :
    ownerContextRule3SourceUnitOfNode? turnContextMolecule 0 turnContext ≠
      some (ChemistryNormalizationResult.rule3SourceUnitOfNode? turnContextMolecule 0
        turnContextFarNode) := by
  decide

/-- An arbitrary owner history `[99, 2, 1, 3, 0]` is rejected (outer `none`) rather than surfacing
the nonexistent atom `99` as an entry. -/
theorem ownerContext_arbitrary_owner_history_rejected :
    ownerContextRule3SourceUnitOfNode? ownerContextMolecule 0
      { ownerHistory := [99, 2, 1, 3, 0], cursor := ownerContextUpwardCursor } = none := by
  decide

/-! ## Kernel trust checks -/

assert_kernel_only ownerContextRule3SourceUnitOfNode?_some_of_ownerAligned
assert_kernel_only ownerContextRule3SourceUnitOfNode?_some_none_of_ownerAligned_no_double
assert_kernel_only ownerContextRule3SourceUnitOfNode?_none_of_invalid_owner_path
assert_kernel_only ownerContextRule3SourceUnitOfNode?_none_of_not_ownerAligned_not_directed
assert_kernel_only ownerContextRule3SourceUnitOfNode?_some_none_of_no_previous
assert_kernel_only ownerContextRule3SourceUnitOfNode?_eq_some_of_directed
assert_kernel_only ownerContextRule3SourceUnitOfNode?_eq_some_cursorReader_of_directed
assert_kernel_only ownerContextRule3EntryGeometry?_eq_of_reader_some
assert_kernel_only ownerContextMolecule_bondOrders
assert_kernel_only turnContextMolecule_bondOrders
assert_kernel_only ownerContext_ownerHistory_facts
assert_kernel_only ownerContext_farNode_originalParent
assert_kernel_only ownerContext_midCursor_generated
assert_kernel_only ownerContext_upwardCursor_generated
assert_kernel_only ownerContext_upwardCursor_actually_generated
assert_kernel_only turnContext_midCursor_generated
assert_kernel_only turnContext_cursor_generated
assert_kernel_only turnContext_cursor_actually_generated
assert_kernel_only ownerContext_not_directed
assert_kernel_only turnContext_directed
assert_kernel_only ownerContext_aligned
assert_kernel_only turnContext_aligned
assert_kernel_only ownerContext_valid_path
assert_kernel_only turnContext_valid_path
assert_kernel_only ownerContext_historicalPreviousReader_reads_wrong_entry
assert_kernel_only turnContext_historicalReader_reads_wrong_entry
assert_kernel_only ownerContext_reader_reads_correct_entry
assert_kernel_only turnContext_reader_reads_correct_entry
assert_kernel_only ownerContext_oldProposal_differs_from_correct
assert_kernel_only turnContext_reader_differs_from_historical
assert_kernel_only ownerContext_arbitrary_owner_history_rejected

end TetraStereo.OneCenter.OwnerContextRule3Source
