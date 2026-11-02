import TetraStereo.OneCenter.LocalizedCumulativeTreeTableReconstruction
import TetraStereo.OneCenter.LocalizedRule4bSparseLabelDecoding
import TetraStereo.OneCenter.LocalizedRealizedTreeCutEmbedding
import TetraStereo.OneCenter.LocalizedRerootCompoundRule45Key
import TetraStereo.OneCenter.LocalizedCumulativeConstitutionalCoherence
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput
open LocalizedCumulativeDecoratedTree

























































variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}

/-! ## The mirror bit determined by the two own Rule-4b references -/

/-- The mirror bit of one comparison of the two own Rule-4b references.  It is `true` exactly when
the references differ, i.e. when the decoded label table must be uppercase-reflected. -/
def referenceMirror (leftReference rightReference : RS) : Bool :=
  decide (leftReference ≠ rightReference)

@[simp] theorem referenceMirror_eq_true_iff {leftReference rightReference : RS} :
    referenceMirror leftReference rightReference = true ↔ leftReference ≠ rightReference := by
  simp [referenceMirror]

@[simp] theorem referenceMirror_eq_false_iff {leftReference rightReference : RS} :
    referenceMirror leftReference rightReference = false ↔ leftReference = rightReference := by
  simp [referenceMirror]

/-- Mirror an optional auxiliary label at a Boolean flag: reflect uppercase descriptors at `true`
and leave the label untouched at `false`. -/
def labelMirror (mirror : Bool) (label : Option LocalizedAuxiliaryLabel) :
    Option LocalizedAuxiliaryLabel :=
  if mirror then reflectUppercaseOptionalLabel label else label

@[simp] theorem labelMirror_false :
    labelMirror false = id := by
  funext label
  simp [labelMirror]

@[simp] theorem labelMirror_true :
    labelMirror true = reflectUppercaseOptionalLabel := by
  funext label
  simp [labelMirror]

/-- Mirroring an optional label twice at the same flag returns the original label. -/
theorem labelMirror_involutive (mirror : Bool) (label : Option LocalizedAuxiliaryLabel) :
    labelMirror mirror (labelMirror mirror label) = label := by
  cases mirror with
  | false => rfl
  | true => exact reflectUppercaseOptionalLabel_involutive label

/-- The mirror flag is either the identity action or the uppercase reflection. -/
theorem labelMirror_eq_if (mirror : Bool) (label : Option LocalizedAuxiliaryLabel) :
    labelMirror mirror label =
      if mirror then reflectUppercaseOptionalLabel label else label := rfl

/-! ## Entrywise payload maps of ranked label tables -/

/-- Entrywise payload map of a ranked optional-label table.  Addresses and sphere structure are
retained exactly; only the observation payload is transformed. -/
def mapLabelTable (f : Option LocalizedAuxiliaryLabel → Option LocalizedAuxiliaryLabel)
    (layers : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))) :
    List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))) :=
  layers.map (List.map fun entry => (entry.1, f entry.2))

/-- The identity payload map leaves a table untouched. -/
@[simp] theorem mapLabelTable_id
    (layers : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))) :
    mapLabelTable id layers = layers := by
  unfold mapLabelTable
  have entryIdentity :
      (fun entry : OfficialSparseEntry (Option LocalizedAuxiliaryLabel) =>
        (entry.1, id entry.2)) = id := by
    funext entry
    rcases entry with ⟨address, label⟩
    rfl
  have mapIdentity :
      (List.map id :
        List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)) →
          List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))) = id := by
    funext layer
    exact List.map_id layer
  rw [entryIdentity, mapIdentity]
  exact List.map_id layers

/-- The uppercase-reflecting payload map is the existing ranked-label reflection. -/
theorem mapLabelTable_reflectUppercase
    (layers : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))) :
    mapLabelTable reflectUppercaseOptionalLabel layers =
      reflectUppercaseRankedLabels layers := rfl

/-- The payload map is the identity when the flag is `false`. -/
theorem mapLabelTable_labelMirror_false
    (layers : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))) :
    mapLabelTable (labelMirror false) layers = layers := by
  exact mapLabelTable_id layers

/-- The payload map is the uppercase reflection when the flag is `true`. -/
theorem mapLabelTable_labelMirror_true
    (layers : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))) :
    mapLabelTable (labelMirror true) layers = reflectUppercaseRankedLabels layers := by
  exact mapLabelTable_reflectUppercase layers

/-- The payload map commutes with dropping the root sphere. -/
theorem mapLabelTable_tail
    (f : Option LocalizedAuxiliaryLabel → Option LocalizedAuxiliaryLabel)
    (layers : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))) :
    (mapLabelTable f layers).tail = mapLabelTable f layers.tail := by
  cases layers with
  | nil => rfl
  | cons layer rest => rfl

/-- Reading a mapped table at one depth reads the original sphere and maps its payload. -/
theorem mapLabelTable_getD
    (f : Option LocalizedAuxiliaryLabel → Option LocalizedAuxiliaryLabel)
    (layers : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))))
    (depth : Nat) :
    (mapLabelTable f layers).getD depth [] =
      (layers.getD depth []).map (fun entry => (entry.1, f entry.2)) := by
  unfold mapLabelTable
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases depthLookup : layers[depth]? with
  | none => rfl
  | some layer => rfl

/-- A mapped table at the root sphere is the mapped root observation. -/
theorem mapLabelTable_getD_zero
    (f : Option LocalizedAuxiliaryLabel → Option LocalizedAuxiliaryLabel)
    (layers : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))))
    (label : Option LocalizedAuxiliaryLabel)
    (root : layers.getD 0 [] = [([], label)]) :
    (mapLabelTable f layers).getD 0 [] = [([], f label)] := by
  rw [mapLabelTable_getD, root]
  rfl

/-- Two payload maps compose. -/
theorem mapLabelTable_mapLabelTable
    (f g : Option LocalizedAuxiliaryLabel → Option LocalizedAuxiliaryLabel)
    (layers : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))) :
    mapLabelTable f (mapLabelTable g layers) =
      mapLabelTable (fun label => f (g label)) layers := by
  unfold mapLabelTable
  induction layers with
  | nil => rfl
  | cons layer rest inductionHypothesis =>
      rw [List.map_cons, List.map_cons, List.map_cons, inductionHypothesis]
      rw [List.map_map]
      congr 1

/-! ## The payload map commutes with the sparse child reconstruction -/

/-- Selecting the entries addressed at one slot commutes with the entrywise payload map. -/
theorem entriesAtSlot_mapLabelTable
    (f : Option LocalizedAuxiliaryLabel → Option LocalizedAuxiliaryLabel)
    (slot : Nat) (layer : List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))) :
    SparseAddress.entriesAtSlot slot
        (layer.map (fun entry => (entry.1, f entry.2))) =
      (SparseAddress.entriesAtSlot slot layer).map
        (fun entry => (entry.1, f entry.2)) := by
  unfold SparseAddress.entriesAtSlot
  simp only [List.filter_map]
  have predicateEq :
      ((fun entry : OfficialSparseEntry (Option LocalizedAuxiliaryLabel) =>
          entry.1.head? == some slot) ∘
        (fun entry => (entry.1, f entry.2))) =
      (fun entry : OfficialSparseEntry (Option LocalizedAuxiliaryLabel) =>
        entry.1.head? == some slot) := by
    funext entry
    rfl
  rw [predicateEq]

/-- Dropping the leading address slot commutes with the entrywise payload map. -/
theorem dropAddressHeadLayer_mapLabelTable
    (f : Option LocalizedAuxiliaryLabel → Option LocalizedAuxiliaryLabel)
    (layer : List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))) :
    SparseAddress.dropAddressHeadLayer
        (layer.map (fun entry => (entry.1, f entry.2))) =
      (SparseAddress.dropAddressHeadLayer layer).map
        (fun entry => (entry.1, f entry.2)) := by
  unfold SparseAddress.dropAddressHeadLayer SparseAddress.dropAddressHead
  simp only [List.map_map]
  have compositionEq :
      ((fun entry : OfficialSparseEntry (Option LocalizedAuxiliaryLabel) =>
          (entry.1.tail, entry.2)) ∘ (fun entry => (entry.1, f entry.2))) =
      ((fun entry => (entry.1, f entry.2)) ∘
        (fun entry : OfficialSparseEntry (Option LocalizedAuxiliaryLabel) =>
          (entry.1.tail, entry.2))) := by
    funext entry
    rfl
  rw [compositionEq]

/-- The executable nonemptiness test is unchanged by the entrywise payload map. -/
theorem nonemptySphere_mapLabelTable
    (f : Option LocalizedAuxiliaryLabel → Option LocalizedAuxiliaryLabel)
    (sphere : List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))) :
    SparseAddress.nonemptySphere
        (sphere.map (fun entry => (entry.1, f entry.2))) =
      SparseAddress.nonemptySphere sphere := by
  unfold SparseAddress.nonemptySphere
  cases sphere with
  | nil => rfl
  | cons head tail => rfl

/-- Trimming the trailing empty spheres commutes with the entrywise payload map. -/
theorem takeWhile_mapLabelTable
    (f : Option LocalizedAuxiliaryLabel → Option LocalizedAuxiliaryLabel) :
    ∀ layers : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))),
      (layers.map (List.map fun entry => (entry.1, f entry.2))).takeWhile
          SparseAddress.nonemptySphere =
        (layers.takeWhile SparseAddress.nonemptySphere).map
          (List.map fun entry => (entry.1, f entry.2))
  | [] => rfl
  | sphere :: rest => by
      by_cases occupied : SparseAddress.nonemptySphere sphere = true
      · have mappedOccupied :
            SparseAddress.nonemptySphere
                (sphere.map (fun entry => (entry.1, f entry.2))) = true := by
          rw [nonemptySphere_mapLabelTable, occupied]
        simp only [List.map_cons, List.takeWhile_cons, if_pos occupied,
          if_pos mappedOccupied, takeWhile_mapLabelTable f rest]
      · have mappedEmpty :
            ¬ SparseAddress.nonemptySphere
                (sphere.map (fun entry => (entry.1, f entry.2))) = true := by
          rw [nonemptySphere_mapLabelTable]
          exact occupied
        simp only [List.map_cons, List.takeWhile_cons, if_neg occupied,
          if_neg mappedEmpty]
        rfl

/-- The sparse normalized child reconstruction commutes with the entrywise payload map. -/
theorem normalizedChildTable_mapLabelTable
    (f : Option LocalizedAuxiliaryLabel → Option LocalizedAuxiliaryLabel)
    (slot : Nat)
    (table : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))) :
    SparseAddress.normalizedChildTable slot
        (table.map (List.map fun entry => (entry.1, f entry.2))) =
      (SparseAddress.normalizedChildTable slot table).map
        (List.map fun entry => (entry.1, f entry.2)) := by
  unfold SparseAddress.normalizedChildTable
  rw [List.map_map]
  have step :
      (fun sphere => SparseAddress.dropAddressHeadLayer
          (SparseAddress.entriesAtSlot slot sphere)) ∘
          (List.map fun entry => (entry.1, f entry.2)) =
        (List.map fun entry => (entry.1, f entry.2)) ∘
          (fun sphere => SparseAddress.dropAddressHeadLayer
            (SparseAddress.entriesAtSlot slot sphere)) := by
    funext sphere
    simp only [Function.comp_apply]
    rw [entriesAtSlot_mapLabelTable, dropAddressHeadLayer_mapLabelTable]
  rw [step, ← List.map_map]
  exact takeWhile_mapLabelTable f
    (table.map fun sphere =>
      SparseAddress.dropAddressHeadLayer (SparseAddress.entriesAtSlot slot sphere))

/-! ## The exact label relation decoded by an actual Rule-4b tie -/

/-- Restate the decoded label relation of `LocalizedRule4bSparseLabelDecoding` at the Boolean
mirror flag `referenceMirror`. -/
theorem labels_eq_mapLabelTable_of_referenceMirror
    {leftReference rightReference : RS}
    {leftLabels rightLabels : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))}
    (decoded : rightLabels = if leftReference = rightReference then leftLabels
      else reflectUppercaseRankedLabels leftLabels) :
    rightLabels =
      mapLabelTable (labelMirror (referenceMirror leftReference rightReference)) leftLabels := by
  by_cases same : leftReference = rightReference
  · subst rightReference
    rw [decoded, if_pos rfl]
    simp [referenceMirror]
  · have different : referenceMirror leftReference rightReference = true := by
      simp [referenceMirror, same]
    rw [decoded, if_neg same, different]
    exact (mapLabelTable_labelMirror_true leftLabels).symm






abbrev compatibilitySubtreeAt? (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    List Nat → Option (LocalizedCumulativeDecoratedTree input carrierFuel) :=
  subtreeAt? (input := input) (carrierFuel := carrierFuel) tree

@[simp] theorem compatibilitySubtreeAt?_nil
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    compatibilitySubtreeAt? tree [] = some tree := subtreeAt?_nil tree

@[simp] theorem compatibilitySubtreeAt?_cons
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) (slot : Nat) (rest : List Nat) :
    compatibilitySubtreeAt? tree (slot :: rest) =
      (tree.children[slot]?).bind (fun child => compatibilitySubtreeAt? child rest) :=
  subtreeAt?_cons tree slot rest


theorem compatibilitySubtreeAt?_cons_eq_some_iff
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {slot : Nat} {rest : List Nat}
    {node : LocalizedCumulativeDecoratedTree input carrierFuel} :
    compatibilitySubtreeAt? tree (slot :: rest) = some node ↔
      ∃ child, tree.children[slot]? = some child ∧
        compatibilitySubtreeAt? child rest = some node :=
  subtreeAt?_cons_eq_some_iff

/-! ## Transport of a whole-table label relation to every actual position -/













theorem labelTable_transport_at_subtree
    (f : Option LocalizedAuxiliaryLabel → Option LocalizedAuxiliaryLabel)
    {tL tR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (labels : tR.labelTable = mapLabelTable f tL.labelTable)
    {path : List Nat}
    {nodeL nodeR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (leftLookup : compatibilitySubtreeAt? tL path = some nodeL)
    (rightLookup : compatibilitySubtreeAt? tR path = some nodeR) :
    nodeR.label = f nodeL.label := by
  induction path generalizing tL tR nodeL nodeR with
  | nil =>
      have nodeLEq : nodeL = tL := by
        have present := leftLookup
        simp only [compatibilitySubtreeAt?_nil, Option.some.injEq] at present
        exact present.symm
      have nodeREq : nodeR = tR := by
        have present := rightLookup
        simp only [compatibilitySubtreeAt?_nil, Option.some.injEq] at present
        exact present.symm
      rw [nodeLEq, nodeREq]
      have labelTables : table (fun node => node.label) tR =
          mapLabelTable f (table (fun node => node.label) tL) := by
        simpa only [labelTable] using labels
      have root := congrArg (fun entries => entries.getD 0 []) labelTables
      change (table (fun node => node.label) tR).getD 0 [] =
        (mapLabelTable f (table (fun node => node.label) tL)).getD 0 [] at root
      rw [table_getD_zero (fun node => node.label) tR,
          mapLabelTable_getD_zero f
            (table (fun node => node.label) tL)
            tL.label
            (table_getD_zero (fun node => node.label) tL)] at root
      have pairEq : (([], tR.label) : OfficialSparseEntry (Option LocalizedAuxiliaryLabel)) =
          ([], f tL.label) :=
        ((List.cons.injEq _ _ _ _).mp root).1
      exact congrArg Prod.snd pairEq
  | cons slot rest inductionHypothesis =>
      rw [compatibilitySubtreeAt?_cons_eq_some_iff] at leftLookup rightLookup
      obtain ⟨childL, childLAt, restL⟩ := leftLookup
      obtain ⟨childR, childRAt, restR⟩ := rightLookup
      have childTableL := normalizedChildTable_tail_eq_table
        (fun node => node.label) tL slot childL childLAt
      have childTableR := normalizedChildTable_tail_eq_table
        (fun node => node.label) tR slot childR childRAt
      have labelTables : table (fun node => node.label) tR =
          mapLabelTable f (table (fun node => node.label) tL) := by
        simpa only [labelTable] using labels
      have childLabelRel : childR.labelTable =
          mapLabelTable f childL.labelTable := by
        have tailed := congrArg List.tail labelTables
        rw [mapLabelTable_tail] at tailed
        have projected := congrArg (SparseAddress.normalizedChildTable slot) tailed
        simp only [mapLabelTable] at projected
        rw [normalizedChildTable_mapLabelTable] at projected
        rw [childTableL, childTableR] at projected
        exact projected
      exact inductionHypothesis (tL := childL) (tR := childR)
        (nodeL := nodeL) (nodeR := nodeR) childLabelRel restL restR

/-! ## The reader value carried by an actual node -/

/-- **A realised node carries the reader's value at its own actual cursor.**  The provenance
`LocalizedCumulativeTreeRealizes` constructs every node as the actual `localizedRootTree` at a real
cursor, whose `label` field is the reader value at that cursor. -/
theorem subtreeAt?_node_label_eq_read
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    {path : List Nat} {node : LocalizedCumulativeDecoratedTree input carrierFuel}
    (lookup : subtreeAt? tree path = some node) :
    node.label = read node.source := by
  induction path generalizing tree with
  | nil =>
      rw [subtreeAt?_nil] at lookup
      have nodeEq : node = tree := (Option.some.inj lookup).symm
      subst node
      cases realizes with
      | mk cursor children sortedChildren childrenComputed sourcePerm childrenRealize =>
          rfl
  | cons slot rest inductionHypothesis =>
      rw [subtreeAt?_cons_eq_some_iff] at lookup
      obtain ⟨child, childLookup, restLookup⟩ := lookup
      exact inductionHypothesis (realizes_of_child realizes childLookup) restLookup

/-- The realised node at a position carries the reader's value at its actual source. -/
theorem positionNode_label_eq_read
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree) (p : Position tree) :
    (positionNode p).label = read (positionSource p) :=
  subtreeAt?_node_label_eq_read realizes (positionNode_spec p)

/-! ## Transport across two positions with the same raw address -/








theorem labelTable_transport_at_positionAddress
    (f : Option LocalizedAuxiliaryLabel → Option LocalizedAuxiliaryLabel)
    {tL tR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (labels : tR.labelTable = mapLabelTable f tL.labelTable)
    {p : Position tL} {q : Position tR} (addressEq : q.val = p.val) :
    (positionNode q).label = f (positionNode p).label := by
  have leftLookup : subtreeAt? tL p.val = some (positionNode p) := positionNode_spec p
  have rightLookup : subtreeAt? tR q.val = some (positionNode q) := positionNode_spec q
  rw [addressEq] at rightLookup
  exact labelTable_transport_at_subtree f labels leftLookup rightLookup

/-! ## Application to two actual successful `.rule4b` builds at one comparison tie -/












theorem actual_rule4b_key_tie_labelTableTransport
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (readerSparse : ∀ cursor, LocalizedRule4bSparseLabel (read cursor))
    (leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel)
    (rule4aLeftFuel rule4aRightFuel rule4bLeftFuel rule4bRightFuel : Nat)
    (leftReference rightReference : RS)
    (aL aR bL bR : input.LocalizedRerootCumulativeRule45Key)
    (aLComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      .rule4a read rule4aLeftFuel leftCursor = some aL)
    (aRComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      .rule4a read rule4aRightFuel rightCursor = some aR)
    (bLComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (.rule4b leftReference) read rule4bLeftFuel leftCursor = some bL)
    (bRComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (.rule4b rightReference) read rule4bRightFuel rightCursor = some bR)
    (rule4aTie : input.compareLocalizedRerootCumulativeRule45Keys aL aR = Ordering.eq)
    (descriptorTie : OfficialRuleMajorKey.compareSparseLayers
      compareLocalizedCumulativeRule45Priority bL.descriptor bR.descriptor = Ordering.eq) :
    ∃ tL tR : LocalizedCumulativeDecoratedTree input carrierFuel,
      tL.source = leftCursor ∧
        tR.source = rightCursor ∧
          LocalizedCumulativeTreeRealizes input read tL ∧
            LocalizedCumulativeTreeRealizes input read tR ∧
              shape tL = shape tR ∧
                tR.labelTable =
                  mapLabelTable
                    (labelMirror (referenceMirror leftReference rightReference))
                    tL.labelTable ∧
                  ∀ (path : List Nat)
                    (nodeL nodeR : LocalizedCumulativeDecoratedTree input carrierFuel),
                    compatibilitySubtreeAt? tL path = some nodeL →
                      compatibilitySubtreeAt? tR path = some nodeR →
                        nodeR.label =
                          labelMirror (referenceMirror leftReference rightReference)
                            nodeL.label := by
  obtain ⟨tL, sourceL, fullMatchL, realizesL, _⟩ :=
    exists_decoratedTree_of_buildWithRead_fullMatch input (.rule4b leftReference)
      read rule4bLeftFuel leftCursor bL bLComputed
  obtain ⟨tR, sourceR, fullMatchR, realizesR, _⟩ :=
    exists_decoratedTree_of_buildWithRead_fullMatch input (.rule4b rightReference)
      read rule4bRightFuel rightCursor bR bRComputed
  have capstone := actual_stage_alignment_capstone input read readerSparse
    leftCursor rightCursor rule4aLeftFuel rule4aRightFuel rule4bLeftFuel rule4bRightFuel
    leftReference rightReference aL aR bL bR aLComputed aRComputed bLComputed bRComputed
    rule4aTie descriptorTie
  have observableEq := capstone.1
  have labelsEq : bR.labels =
      mapLabelTable (labelMirror (referenceMirror leftReference rightReference)) bL.labels :=
    labels_eq_mapLabelTable_of_referenceMirror capstone.2
  have rule1aEq : bL.constitutional.rule1a = bR.constitutional.rule1a :=
    congrArg LocalizedCumulativeRule45Observable.rule1a observableEq
  have rule1bEq : bL.constitutional.rule1b = bR.constitutional.rule1b :=
    congrArg LocalizedCumulativeRule45Observable.rule1b observableEq
  have rule2Eq : bL.constitutional.rule2 = bR.constitutional.rule2 :=
    congrArg LocalizedCumulativeRule45Observable.rule2 observableEq
  have column1a : (tL.tables (.rule4b leftReference)).rule1a =
      (tR.tables (.rule4b rightReference)).rule1a := by
    rw [fullMatchL.tableMatch.1, fullMatchR.tableMatch.1, rule1aEq]
  have column1b : (tL.tables (.rule4b leftReference)).rule1b =
      (tR.tables (.rule4b rightReference)).rule1b := by
    rw [fullMatchL.tableMatch.2.1, fullMatchR.tableMatch.2.1, rule1bEq]
  have column2 : (tL.tables (.rule4b leftReference)).rule2 =
      (tR.tables (.rule4b rightReference)).rule2 := by
    rw [fullMatchL.tableMatch.2.2.1, fullMatchR.tableMatch.2.2.1, rule2Eq]
  have shapeEq : shape tL = shape tR :=
    table_shape_eq_of_columns_eq (.rule4b leftReference) (.rule4b rightReference)
      tL tR column1a column1b column2
  have labelTableEq : tR.labelTable =
      mapLabelTable (labelMirror (referenceMirror leftReference rightReference))
        tL.labelTable := by
    rw [fullMatchR.labelMatch, labelsEq, fullMatchL.labelMatch]
  refine ⟨tL, tR, sourceL, sourceR, realizesL, realizesR, shapeEq, labelTableEq, ?_⟩
  intro path nodeL nodeR foundL foundR
  exact labelTable_transport_at_subtree _ labelTableEq foundL foundR

/-! ## Actual compound Rule-5 tie: builder-level data extraction

The full-tie route extracts a tie of the actual compound through-Rule-5 comparator all the way to
the paired head Rule-5 reading and its actual common-`R` build.  The extraction is needed before the
tree layer because the comparator tie only concerns the two compound keys; the trees come from the
actual common-`R` cumulative builds recorded by the same builders.

Nothing here assumes a nearest-singleton domain or a supplied reader agreement.  The prior reading
list is never empty: `localizedRule4bcReferenceAlternatives` is `[none]` when the Rule-4a key has no
uppercase reference and otherwise the `some` image of a nonempty list. -/

/-- The Rule-4b alternative list has positive length.  No reference gives the genuine `[none]`
alternative; a reference list gives at least one `some` alternative. -/
theorem referenceAlternatives_length_pos (references : List RS) :
    0 < (localizedRule4bcReferenceAlternatives references).length := by
  cases references with
  | nil => simp [localizedRule4bcReferenceAlternatives]
  | cons reference rest => simp [localizedRule4bcReferenceAlternatives]

/-- Every successful alternative-reading compilation preserves the alternative-list length. -/
theorem buildLocalizedRerootRule4bcReadings?_length_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    ∀ (alternatives : List (Option RS))
      (readings : List input.LocalizedRerootRule4bcReading),
      input.buildLocalizedRerootRule4bcReadings?
        target view fuel cursor alternatives = some readings →
      readings.length = alternatives.length := by
  intro alternatives
  induction alternatives with
  | nil =>
      intro readings computed
      simp [buildLocalizedRerootRule4bcReadings?] at computed
      subst readings
      rfl
  | cons alternative rest inductionHypothesis =>
      intro readings computed
      unfold buildLocalizedRerootRule4bcReadings? at computed
      cases headComputed : input.buildLocalizedRerootRule4bcReading?
          target view fuel cursor alternative with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : input.buildLocalizedRerootRule4bcReadings?
              target view fuel cursor rest with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst readings
              simp [inductionHypothesis tail tailComputed]

/-- A successful Rule-5 reading compilation exposes the actual common-`R` cumulative build. -/
theorem buildLocalizedRerootRule5Reading?_commonR_built
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (prior : input.LocalizedRerootRule4bcReading)
    (reading : input.LocalizedRerootRule5Reading)
    (computed : input.buildLocalizedRerootRule5Reading?
      target view fuel cursor prior = some reading) :
    input.buildLocalizedRerootCumulativeRule45Key?
      (localizedRule5StageFor prior.reference? .R) target view fuel cursor =
      some reading.commonR := by
  unfold buildLocalizedRerootRule5Reading? at computed
  cases commonRComputed : input.buildLocalizedRerootCumulativeRule45Key?
      (localizedRule5StageFor prior.reference? .R) target view fuel cursor with
  | none => simp [commonRComputed] at computed
  | some commonR =>
      cases commonSComputed : input.buildLocalizedRerootCumulativeRule45Key?
          (localizedRule5StageFor prior.reference? .S) target view fuel cursor with
      | none => simp [commonRComputed, commonSComputed] at computed
      | some commonS =>
          simp [commonRComputed, commonSComputed] at computed
          rw [← computed]

/-- A successful reading-list compilation over a cons prior list exposes its head reading, the
actual per-reading build, the recorded prior, and the actual common-`R` cumulative build. -/
theorem buildLocalizedRerootRule5Readings?_cons_exposes
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (prior : input.LocalizedRerootRule4bcReading)
    (priors : List input.LocalizedRerootRule4bcReading)
    (readings : List input.LocalizedRerootRule5Reading)
    (computed : input.buildLocalizedRerootRule5Readings?
      target view fuel cursor (prior :: priors) = some readings) :
    ∃ head tail,
      readings = head :: tail ∧
        input.buildLocalizedRerootRule5Reading? target view fuel cursor prior = some head ∧
          head.prior = prior ∧
            input.buildLocalizedRerootCumulativeRule45Key?
              (localizedRule5StageFor prior.reference? .R) target view fuel cursor =
              some head.commonR := by
  unfold buildLocalizedRerootRule5Readings? at computed
  cases headComputed : input.buildLocalizedRerootRule5Reading?
      target view fuel cursor prior with
  | none => simp [headComputed] at computed
  | some head =>
      cases tailComputed : input.buildLocalizedRerootRule5Readings?
          target view fuel cursor priors with
      | none => simp [headComputed, tailComputed] at computed
      | some tail =>
          simp [headComputed, tailComputed] at computed
          exact ⟨head, tail, computed.symm, rfl,
            (input.buildLocalizedRerootRule5Reading?_sound target view fuel cursor
              prior head headComputed).1,
            buildLocalizedRerootRule5Reading?_commonR_built input target view fuel cursor
              prior head headComputed⟩

/-- A successful compound through-Rule-5 build exposes its actual compound Rules-4b/4c build and
its actual reading-list build over that compound key's own prior readings. -/
theorem buildLocalizedRerootCompoundRule45Key?_prior_built
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule45Key)
    (computed : input.buildLocalizedRerootCompoundRule45Key?
      target view fuel cursor = some key) :
    input.buildLocalizedRerootCompoundRule4bcKey? target view fuel cursor = some key.prior ∧
      input.buildLocalizedRerootRule5Readings? target view fuel cursor key.prior.readings
        = some key.rule5Readings := by
  unfold buildLocalizedRerootCompoundRule45Key? at computed
  cases priorComputed : input.buildLocalizedRerootCompoundRule4bcKey?
      target view fuel cursor with
  | none => simp [priorComputed] at computed
  | some prior =>
      cases readingsComputed : input.buildLocalizedRerootRule5Readings?
          target view fuel cursor prior.readings with
      | none => simp [priorComputed, readingsComputed] at computed
      | some readings =>
          simp [priorComputed, readingsComputed] at computed
          rw [← computed]
          exact ⟨rfl, by simpa using readingsComputed⟩

/-- A successful compound Rules-4b/4c build has nonempty prior readings and exposes its actual
Rule-4a cumulative build.  Nonemptiness comes from the positive length of the alternative list. -/
theorem buildLocalizedRerootCompoundRule4bcKey?_readings_cons
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule4bcKey)
    (computed : input.buildLocalizedRerootCompoundRule4bcKey?
      target view fuel cursor = some key) :
    (∃ prior priors, key.readings = prior :: priors) ∧
      input.buildLocalizedRerootCumulativeRule45Key?
        .rule4a target view fuel cursor = some key.rule4aKey := by
  unfold buildLocalizedRerootCompoundRule4bcKey? at computed
  cases rule4aComputed : input.buildLocalizedRerootCumulativeRule45Key?
      .rule4a target view fuel cursor with
  | none => simp [rule4aComputed] at computed
  | some rule4aKey =>
      cases readingsComputed : input.buildLocalizedRerootRule4bcReadings?
          target view fuel cursor
          (localizedRule4bcReferenceAlternatives
            (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels)) with
      | none => simp [rule4aComputed, readingsComputed] at computed
      | some readings =>
          simp [rule4aComputed, readingsComputed] at computed
          rw [← computed]
          refine ⟨?_, rfl⟩
          have lengthEq := buildLocalizedRerootRule4bcReadings?_length_eq input
            target view fuel cursor
            (localizedRule4bcReferenceAlternatives
              (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels))
            readings readingsComputed
          have positive : 0 < readings.length := by
            rw [lengthEq]
            exact referenceAlternatives_length_pos _
          cases readings with
          | nil => simp at positive
          | cons prior priors => exact ⟨prior, priors, rfl⟩

/-- A full actual compound through-Rule-5 comparator tie splits into the compound Rules-4b/4c
prior tie and the common-`R` reading-list tie. -/
theorem compoundRule45Tie_prior_readings
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule45Key)
    (tie : input.compareLocalizedRerootCompoundRule45Keys left right = Ordering.eq) :
    input.compareLocalizedRerootCompoundRule4bcKeys left.prior right.prior = Ordering.eq ∧
      input.compareLocalizedRerootCompoundRule5Readings .R
        left.rule5Readings right.rule5Readings = Ordering.eq := by
  have decomposed := tie
  simp only [compareLocalizedRerootCompoundRule45Keys, compareLex, Ordering.byKey,
    Ordering.then_eq_eq] at decomposed
  exact ⟨decomposed.1, decomposed.2⟩

/-- The paired heads of a tied nonempty common-reference reading list carry equal descriptors. -/
theorem compareLocalizedRerootCompoundRule5Readings_heads_descriptor_eq
    (input : CertifiedLocalizedCIPInput) (commonReference : RS)
    (headLeft headRight : input.LocalizedRerootRule5Reading)
    (tailLeft tailRight : List input.LocalizedRerootRule5Reading)
    (same : input.compareLocalizedRerootCompoundRule5Readings commonReference
      (headLeft :: tailLeft) (headRight :: tailRight) = Ordering.eq) :
    input.localizedRerootRule5Descriptor commonReference headLeft =
      input.localizedRerootRule5Descriptor commonReference headRight := by
  have headTie := same
  simp only [compareLocalizedRerootCompoundRule5Readings, List.compareLex_cons_cons,
    Ordering.byKey, Ordering.then_eq_eq] at headTie
  exact (compareSparseLayers_compareLocalizedCumulativeRule45Priority_eq_iff _ _).mp headTie.1

/-- A cumulative key tie exposes the three constitutional rule columns. -/
theorem cumulativeRule45Tie_constitutional_columns
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCumulativeRule45Key)
    (tie : input.compareLocalizedRerootCumulativeRule45Keys left right = Ordering.eq) :
    left.constitutional.rule1a = right.constitutional.rule1a ∧
      left.constitutional.rule1b = right.constitutional.rule1b ∧
        left.constitutional.rule2 = right.constitutional.rule2 := by
  have parts :
      OfficialRuleMajorKey.compare left.constitutional right.constitutional = Ordering.eq ∧
        OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
            left.descriptor right.descriptor = Ordering.eq := by
    have decomposed := tie
    simp only [compareLocalizedRerootCumulativeRule45Keys, compareLex, Ordering.byKey,
      Ordering.then_eq_eq] at decomposed
    exact decomposed
  exact (officialRuleMajorKey_compare_eq_iff left.constitutional right.constitutional).mp parts.1

/-! ## Observation-level label recovery -/

/-- The root decoration of a decorated observation carries exactly the tree's own label. -/
@[simp] theorem observation_decoration_label
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    (observation tree).decoration.label = tree.label := by
  cases tree with
  | mk source atomicNumber rule1bDistance isotopeMass label children =>
      rw [table_observation_mk]

/-- The child observations of a decorated observation are the observations of the children. -/
@[simp] theorem observation_children_eq
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    (observation tree).children = tree.children.map observation := by
  cases tree with
  | mk source atomicNumber rule1bDistance isotopeMass label children =>
      rw [table_observation_mk, table_observationList_eq_map]

/-- **Decorated observation equality forces equal labels at every shared actual slot address.**
The proof descends the raw slot path, using the observation's child list at each cons step.  No
shape hypothesis and no tree matching relation is assumed; only the equality of the two fully
decorated observations. -/
theorem subtreeAt?_label_eq_of_observation_eq :
    ∀ (path : List Nat)
      (tL tR : LocalizedCumulativeDecoratedTree input carrierFuel),
      observation tL = observation tR →
        ∀ (nodeL nodeR : LocalizedCumulativeDecoratedTree input carrierFuel),
        subtreeAt? tL path = some nodeL →
          subtreeAt? tR path = some nodeR → nodeR.label = nodeL.label := by
  intro path
  induction path with
  | nil =>
      intro tL tR same nodeL nodeR foundL foundR
      rw [subtreeAt?_nil] at foundL foundR
      have nodeEqL : nodeL = tL := (Option.some.inj foundL).symm
      have nodeEqR : nodeR = tR := (Option.some.inj foundR).symm
      subst nodeL
      subst nodeR
      have labelEq : tL.label = tR.label := by
        have := congrArg (fun observation => observation.decoration.label) same
        simpa using this
      exact labelEq.symm
  | cons slot rest inductionHypothesis =>
      intro tL tR same nodeL nodeR foundL foundR
      rw [subtreeAt?_cons_eq_some_iff] at foundL foundR
      obtain ⟨childL, childFoundL, restFoundL⟩ := foundL
      obtain ⟨childR, childFoundR, restFoundR⟩ := foundR
      have childrenSame : tL.children.map observation = tR.children.map observation := by
        have := congrArg (fun observation => observation.children) same
        simpa using this
      have slotSame :
          (tL.children.map observation)[slot]? =
            (tR.children.map observation)[slot]? := by
        rw [childrenSame]
      have mappedL : (tL.children.map observation)[slot]? = some (observation childL) := by
        simp [List.getElem?_map, childFoundL]
      have mappedR : (tR.children.map observation)[slot]? = some (observation childR) := by
        simp [List.getElem?_map, childFoundR]
      have childObservationEq : observation childL = observation childR := by
        rw [mappedL, mappedR] at slotSame
        exact Option.some.inj slotSame
      exact inductionHypothesis childL childR childObservationEq nodeL nodeR
        restFoundL restFoundR

/-- **Descriptor equality at a shared root forces equality of the actual priority vectors.**
Each realized tree's descriptor root sphere is the single entry carrying the priority vector of the
root node label (`table_getD_zero`); equality of the whole descriptors therefore equates those two
vectors. -/
theorem headCommonR_priority_eq_of_descriptor_eq
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {tL tR : LocalizedCumulativeDecoratedTree input carrierFuel}
    {keyL keyR : input.LocalizedRerootCumulativeRule45Key}
    (stageL stageR : LocalizedCumulativeRule45Stage)
    (matchL : LocalizedCumulativeTreeTableMatch stageL tL keyL)
    (matchR : LocalizedCumulativeTreeTableMatch stageR tR keyR)
    (descriptorEq : keyL.descriptor = keyR.descriptor) :
    localizedCumulativeRule45Priority stageL tL.label =
      localizedCumulativeRule45Priority stageR tR.label := by
  have rootL : keyL.descriptor.getD 0 [] =
      [([], localizedCumulativeRule45Priority stageL tL.label)] := by
    rw [← matchL.2.2.2]
    exact table_getD_zero (fun node => localizedCumulativeRule45Priority stageL node.label) tL
  have rootR : keyR.descriptor.getD 0 [] =
      [([], localizedCumulativeRule45Priority stageR tR.label)] := by
    rw [← matchR.2.2.2]
    exact table_getD_zero (fun node => localizedCumulativeRule45Priority stageR node.label) tR
  have rootsEq : keyL.descriptor.getD 0 [] = keyR.descriptor.getD 0 [] :=
    congrArg (fun descriptor => descriptor.getD 0 []) descriptorEq
  rw [rootL, rootR] at rootsEq
  have pairEq :
      (([], localizedCumulativeRule45Priority stageL tL.label) : OfficialSparseEntry (List Nat)) =
        ([], localizedCumulativeRule45Priority stageR tR.label) :=
    (List.cons.injEq _ _ _ _).mp rootsEq |>.1
  exact congrArg Prod.snd pairEq

/-! ## Full actual compound Rule-5 tie: same-label realized trees

The comparator tie is unpacked into actual builder data only: the paired prior readings, the paired
head Rule-5 readings, their actual common-`R` cumulative builds, the real decorated trees those
builds realize with the dependency reader, and the equality of the two fully decorated observations
at every shared actual slot address.  No sparse-label, nearest-singleton, reading-agreement or
physical-isomorphism premise is used or supplied. -/

/-- **A full actual compound through-Rule-5 comparator tie yields same-label realized trees.**
Both sides of the tie are actual successful builds of `buildLocalizedRerootCompoundRule45Key?` for
the same target, dependency view and cursor record; the tie alone forces the paired head Rule-5
readings, their actual common-`R` cumulative builds, equal head common-`R` descriptors, realized
decorated trees for those builds, equal shapes and equal fully decorated observations.  Hence the
two trees carry the same actual label at every shared slot address. -/
theorem actual_compoundRule5_tie_sameLabels
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel)
    (leftFuel rightFuel : Nat)
    (leftKey rightKey : input.LocalizedRerootCompoundRule45Key)
    (leftComputed : input.buildLocalizedRerootCompoundRule45Key?
      target view leftFuel leftCursor = some leftKey)
    (rightComputed : input.buildLocalizedRerootCompoundRule45Key?
      target view rightFuel rightCursor = some rightKey)
    (tie : input.compareLocalizedRerootCompoundRule45Keys leftKey rightKey =
      Ordering.eq) :
    ∃ (leftPrior : input.LocalizedRerootRule4bcReading)
      (leftPriors : List input.LocalizedRerootRule4bcReading)
      (rightPrior : input.LocalizedRerootRule4bcReading)
      (rightPriors : List input.LocalizedRerootRule4bcReading)
      (leftHead : input.LocalizedRerootRule5Reading)
      (leftTail : List input.LocalizedRerootRule5Reading)
      (rightHead : input.LocalizedRerootRule5Reading)
      (rightTail : List input.LocalizedRerootRule5Reading)
      (tL tR : LocalizedCumulativeDecoratedTree input carrierFuel),
      leftKey.prior.readings = leftPrior :: leftPriors ∧
        rightKey.prior.readings = rightPrior :: rightPriors ∧
          leftKey.rule5Readings = leftHead :: leftTail ∧
            rightKey.rule5Readings = rightHead :: rightTail ∧
              leftHead.prior = leftPrior ∧
                rightHead.prior = rightPrior ∧
                  input.buildLocalizedRerootCumulativeRule45Key?
                      (localizedRule5StageFor leftPrior.reference? .R) target view
                      leftFuel leftCursor = some leftHead.commonR ∧
                    input.buildLocalizedRerootCumulativeRule45Key?
                        (localizedRule5StageFor rightPrior.reference? .R) target view
                        rightFuel rightCursor = some rightHead.commonR ∧
                      leftHead.commonR.descriptor = rightHead.commonR.descriptor ∧
                        tL.source = leftCursor ∧
                          tR.source = rightCursor ∧
                            LocalizedCumulativeTreeRealizes input
                                (fun cursor =>
                                  input.localizedDependencyLabel target view cursor) tL ∧
                              LocalizedCumulativeTreeRealizes input
                                  (fun cursor =>
                                    input.localizedDependencyLabel target view cursor) tR ∧
                                shape tL = shape tR ∧
                                  observation tL = observation tR ∧
                                    (∀ (path : List Nat)
                                        (nodeL nodeR :
                                          LocalizedCumulativeDecoratedTree input carrierFuel),
                                      subtreeAt? tL path = some nodeL →
                                        subtreeAt? tR path = some nodeR →
                                          nodeR.label = nodeL.label) := by
  obtain ⟨leftPriorBuild, leftReadingsBuild⟩ :=
    buildLocalizedRerootCompoundRule45Key?_prior_built input target view
      leftFuel leftCursor leftKey leftComputed
  obtain ⟨rightPriorBuild, rightReadingsBuild⟩ :=
    buildLocalizedRerootCompoundRule45Key?_prior_built input target view
      rightFuel rightCursor rightKey rightComputed
  obtain ⟨⟨leftPrior, leftPriors, leftPriorReadings⟩, leftRule4aBuild⟩ :=
    buildLocalizedRerootCompoundRule4bcKey?_readings_cons input target view
      leftFuel leftCursor leftKey.prior leftPriorBuild
  obtain ⟨⟨rightPrior, rightPriors, rightPriorReadings⟩, rightRule4aBuild⟩ :=
    buildLocalizedRerootCompoundRule4bcKey?_readings_cons input target view
      rightFuel rightCursor rightKey.prior rightPriorBuild
  have leftReadingsBuild' : input.buildLocalizedRerootRule5Readings?
      target view leftFuel leftCursor (leftPrior :: leftPriors) =
      some leftKey.rule5Readings := by
    rw [← leftPriorReadings]
    exact leftReadingsBuild
  have rightReadingsBuild' : input.buildLocalizedRerootRule5Readings?
      target view rightFuel rightCursor (rightPrior :: rightPriors) =
      some rightKey.rule5Readings := by
    rw [← rightPriorReadings]
    exact rightReadingsBuild
  obtain ⟨leftHead, leftTail, leftReadingsEq, leftHeadBuild, leftHeadPrior,
    leftHeadCommonR⟩ :=
    buildLocalizedRerootRule5Readings?_cons_exposes input target view
      leftFuel leftCursor leftPrior leftPriors leftKey.rule5Readings leftReadingsBuild'
  obtain ⟨rightHead, rightTail, rightReadingsEq, rightHeadBuild, rightHeadPrior,
    rightHeadCommonR⟩ :=
    buildLocalizedRerootRule5Readings?_cons_exposes input target view
      rightFuel rightCursor rightPrior rightPriors rightKey.rule5Readings rightReadingsBuild'
  obtain ⟨priorTie, readingsTie⟩ :=
    compoundRule45Tie_prior_readings input leftKey rightKey tie
  have rule4aTie : input.compareLocalizedRerootCumulativeRule45Keys
      leftKey.prior.rule4aKey rightKey.prior.rule4aKey = Ordering.eq :=
    ((input.compareLocalizedRerootCompoundRule4bcKeys_eq_eq_iff
      leftKey.prior rightKey.prior).mp priorTie).1
  have rule4aColumns := cumulativeRule45Tie_constitutional_columns input
    leftKey.prior.rule4aKey rightKey.prior.rule4aKey rule4aTie
  have readingsConsTie : input.compareLocalizedRerootCompoundRule5Readings .R
      (leftHead :: leftTail) (rightHead :: rightTail) = Ordering.eq := by
    rw [← leftReadingsEq, ← rightReadingsEq]
    exact readingsTie
  have headDescriptorEq : leftHead.commonR.descriptor =
      rightHead.commonR.descriptor := by
    have headEq := compareLocalizedRerootCompoundRule5Readings_heads_descriptor_eq
      input .R leftHead rightHead leftTail rightTail readingsConsTie
    simpa [localizedRerootRule5Descriptor] using headEq
  have leftConstitutional : constitutionalObservable leftHead.commonR.constitutional =
      constitutionalObservable leftKey.prior.rule4aKey.constitutional :=
    cumulative_builds_constitutional_observable_equal input leftCursor
      leftHeadCommonR leftRule4aBuild
  have rightConstitutional : constitutionalObservable rightHead.commonR.constitutional =
      constitutionalObservable rightKey.prior.rule4aKey.constitutional :=
    cumulative_builds_constitutional_observable_equal input rightCursor
      rightHeadCommonR rightRule4aBuild
  have leftRule1a : leftHead.commonR.constitutional.rule1a =
      leftKey.prior.rule4aKey.constitutional.rule1a :=
    congrArg (fun observable => observable.rule1a) leftConstitutional
  have leftRule1b : leftHead.commonR.constitutional.rule1b =
      leftKey.prior.rule4aKey.constitutional.rule1b :=
    congrArg (fun observable => observable.rule1b) leftConstitutional
  have leftRule2 : leftHead.commonR.constitutional.rule2 =
      leftKey.prior.rule4aKey.constitutional.rule2 :=
    congrArg (fun observable => observable.rule2) leftConstitutional
  have rightRule1a : rightHead.commonR.constitutional.rule1a =
      rightKey.prior.rule4aKey.constitutional.rule1a :=
    congrArg (fun observable => observable.rule1a) rightConstitutional
  have rightRule1b : rightHead.commonR.constitutional.rule1b =
      rightKey.prior.rule4aKey.constitutional.rule1b :=
    congrArg (fun observable => observable.rule1b) rightConstitutional
  have rightRule2 : rightHead.commonR.constitutional.rule2 =
      rightKey.prior.rule4aKey.constitutional.rule2 :=
    congrArg (fun observable => observable.rule2) rightConstitutional
  have leftWithRead : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (localizedRule5StageFor leftPrior.reference? .R)
      (fun cursor => input.localizedDependencyLabel target view cursor)
      leftFuel leftCursor = some leftHead.commonR := by
    rw [buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
      input (localizedRule5StageFor leftPrior.reference? .R) target view
      leftFuel leftCursor]
    exact leftHeadCommonR
  have rightWithRead : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (localizedRule5StageFor rightPrior.reference? .R)
      (fun cursor => input.localizedDependencyLabel target view cursor)
      rightFuel rightCursor = some rightHead.commonR := by
    rw [buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
      input (localizedRule5StageFor rightPrior.reference? .R) target view
      rightFuel rightCursor]
    exact rightHeadCommonR
  obtain ⟨tL, tLsource, tLmatch, tLrealizes, _⟩ :=
    exists_decoratedTree_of_buildWithRead_fullMatch input
      (localizedRule5StageFor leftPrior.reference? .R)
      (fun cursor => input.localizedDependencyLabel target view cursor)
      leftFuel leftCursor leftHead.commonR leftWithRead
  obtain ⟨tR, tRsource, tRmatch, tRrealizes, _⟩ :=
    exists_decoratedTree_of_buildWithRead_fullMatch input
      (localizedRule5StageFor rightPrior.reference? .R)
      (fun cursor => input.localizedDependencyLabel target view cursor)
      rightFuel rightCursor rightHead.commonR rightWithRead
  have tableRule1aEq :
      (tL.tables (localizedRule5StageFor leftPrior.reference? .R)).rule1a =
        (tR.tables (localizedRule5StageFor rightPrior.reference? .R)).rule1a := by
    rw [tLmatch.tableMatch.1, leftRule1a, rule4aColumns.1, ← rightRule1a,
      ← tRmatch.tableMatch.1]
  have tableRule1bEq :
      (tL.tables (localizedRule5StageFor leftPrior.reference? .R)).rule1b =
        (tR.tables (localizedRule5StageFor rightPrior.reference? .R)).rule1b := by
    rw [tLmatch.tableMatch.2.1, leftRule1b, rule4aColumns.2.1, ← rightRule1b,
      ← tRmatch.tableMatch.2.1]
  have tableRule2Eq :
      (tL.tables (localizedRule5StageFor leftPrior.reference? .R)).rule2 =
        (tR.tables (localizedRule5StageFor rightPrior.reference? .R)).rule2 := by
    rw [tLmatch.tableMatch.2.2.1, leftRule2, rule4aColumns.2.2, ← rightRule2,
      ← tRmatch.tableMatch.2.2.1]
  have tableDescriptorEq :
      (tL.tables (localizedRule5StageFor leftPrior.reference? .R)).descriptor =
        (tR.tables (localizedRule5StageFor rightPrior.reference? .R)).descriptor := by
    rw [tLmatch.tableMatch.2.2.2, headDescriptorEq, ← tRmatch.tableMatch.2.2.2]
  have priorityEq : localizedCumulativeRule45Priority
      (localizedRule5StageFor leftPrior.reference? .R) tL.label =
      localizedCumulativeRule45Priority
        (localizedRule5StageFor rightPrior.reference? .R) tR.label :=
    headCommonR_priority_eq_of_descriptor_eq _ _ tLmatch.tableMatch
      tRmatch.tableMatch headDescriptorEq
  have observationEq : observation tL = observation tR := by
    cases hrefL : leftPrior.reference? with
    | none =>
        cases hrefR : rightPrior.reference? with
        | none =>
            exact table_observation_eq_of_rule5NoRule4bReference_columns_eq .R tL tR
              (by simpa [hrefL, hrefR, localizedRule5StageFor] using tableRule1aEq)
              (by simpa [hrefL, hrefR, localizedRule5StageFor] using tableRule1bEq)
              (by simpa [hrefL, hrefR, localizedRule5StageFor] using tableRule2Eq)
              (by simpa [hrefL, hrefR, localizedRule5StageFor] using tableDescriptorEq)
        | some refR =>
            exfalso
            have lengthEq := congrArg List.length priorityEq
            simp [hrefL, hrefR, localizedRule5StageFor,
              localizedCumulativeRule45Priority] at lengthEq
    | some refL =>
        cases hrefR : rightPrior.reference? with
        | none =>
            exfalso
            have lengthEq := congrArg List.length priorityEq
            simp [hrefL, hrefR, localizedRule5StageFor,
              localizedCumulativeRule45Priority] at lengthEq
        | some refR =>
            exact table_observation_eq_of_rule5_commonReference_columns_eq
              refL refR .R tL tR
              (by simpa [hrefL, hrefR, localizedRule5StageFor] using tableRule1aEq)
              (by simpa [hrefL, hrefR, localizedRule5StageFor] using tableRule1bEq)
              (by simpa [hrefL, hrefR, localizedRule5StageFor] using tableRule2Eq)
              (by simpa [hrefL, hrefR, localizedRule5StageFor] using tableDescriptorEq)
  have shapeEq : shape tL = shape tR :=
    table_shape_eq_of_columns_eq
      (localizedRule5StageFor leftPrior.reference? .R)
      (localizedRule5StageFor rightPrior.reference? .R)
      tL tR tableRule1aEq tableRule1bEq tableRule2Eq
  refine ⟨leftPrior, leftPriors, rightPrior, rightPriors, leftHead, leftTail,
    rightHead, rightTail, tL, tR, leftPriorReadings, rightPriorReadings,
    leftReadingsEq, rightReadingsEq, leftHeadPrior, rightHeadPrior,
    leftHeadCommonR, rightHeadCommonR, headDescriptorEq, tLsource, ?_, tLrealizes,
    tRrealizes, shapeEq, observationEq, ?_⟩
  · exact tRsource
  · intro path nodeL nodeR foundL foundR
    exact subtreeAt?_label_eq_of_observation_eq path tL tR observationEq
      nodeL nodeR foundL foundR

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.referenceMirror
assert_kernel_only TetraStereo.OneCenter.referenceMirror_eq_true_iff
assert_kernel_only TetraStereo.OneCenter.referenceMirror_eq_false_iff
assert_kernel_only TetraStereo.OneCenter.labelMirror
assert_kernel_only TetraStereo.OneCenter.labelMirror_false
assert_kernel_only TetraStereo.OneCenter.labelMirror_true
assert_kernel_only TetraStereo.OneCenter.labelMirror_eq_if
assert_kernel_only TetraStereo.OneCenter.labelMirror_involutive
assert_kernel_only TetraStereo.OneCenter.mapLabelTable
assert_kernel_only TetraStereo.OneCenter.mapLabelTable_id
assert_kernel_only TetraStereo.OneCenter.mapLabelTable_reflectUppercase
assert_kernel_only TetraStereo.OneCenter.mapLabelTable_labelMirror_false
assert_kernel_only TetraStereo.OneCenter.mapLabelTable_labelMirror_true
assert_kernel_only TetraStereo.OneCenter.mapLabelTable_tail
assert_kernel_only TetraStereo.OneCenter.mapLabelTable_getD
assert_kernel_only TetraStereo.OneCenter.mapLabelTable_getD_zero
assert_kernel_only TetraStereo.OneCenter.mapLabelTable_mapLabelTable
assert_kernel_only TetraStereo.OneCenter.entriesAtSlot_mapLabelTable
assert_kernel_only TetraStereo.OneCenter.dropAddressHeadLayer_mapLabelTable
assert_kernel_only TetraStereo.OneCenter.nonemptySphere_mapLabelTable
assert_kernel_only TetraStereo.OneCenter.takeWhile_mapLabelTable
assert_kernel_only TetraStereo.OneCenter.normalizedChildTable_mapLabelTable
assert_kernel_only TetraStereo.OneCenter.compatibilitySubtreeAt?
assert_kernel_only TetraStereo.OneCenter.compatibilitySubtreeAt?_nil
assert_kernel_only TetraStereo.OneCenter.compatibilitySubtreeAt?_cons
assert_kernel_only TetraStereo.OneCenter.compatibilitySubtreeAt?_cons_eq_some_iff
assert_kernel_only TetraStereo.OneCenter.labels_eq_mapLabelTable_of_referenceMirror
assert_kernel_only TetraStereo.OneCenter.labelTable_transport_at_subtree
assert_kernel_only TetraStereo.OneCenter.subtreeAt?_node_label_eq_read
assert_kernel_only TetraStereo.OneCenter.positionNode_label_eq_read
assert_kernel_only TetraStereo.OneCenter.labelTable_transport_at_positionAddress
assert_kernel_only TetraStereo.OneCenter.actual_rule4b_key_tie_labelTableTransport
assert_kernel_only TetraStereo.OneCenter.referenceAlternatives_length_pos
assert_kernel_only TetraStereo.OneCenter.buildLocalizedRerootRule4bcReadings?_length_eq
assert_kernel_only TetraStereo.OneCenter.buildLocalizedRerootRule5Reading?_commonR_built
assert_kernel_only TetraStereo.OneCenter.buildLocalizedRerootRule5Readings?_cons_exposes
assert_kernel_only TetraStereo.OneCenter.buildLocalizedRerootCompoundRule45Key?_prior_built
assert_kernel_only TetraStereo.OneCenter.buildLocalizedRerootCompoundRule4bcKey?_readings_cons
assert_kernel_only TetraStereo.OneCenter.compoundRule45Tie_prior_readings
assert_kernel_only TetraStereo.OneCenter.compareLocalizedRerootCompoundRule5Readings_heads_descriptor_eq
assert_kernel_only TetraStereo.OneCenter.cumulativeRule45Tie_constitutional_columns
assert_kernel_only TetraStereo.OneCenter.observation_decoration_label
assert_kernel_only TetraStereo.OneCenter.observation_children_eq
assert_kernel_only TetraStereo.OneCenter.subtreeAt?_label_eq_of_observation_eq
assert_kernel_only TetraStereo.OneCenter.headCommonR_priority_eq_of_descriptor_eq
assert_kernel_only TetraStereo.OneCenter.actual_compoundRule5_tie_sameLabels

end TetraStereo.OneCenter
