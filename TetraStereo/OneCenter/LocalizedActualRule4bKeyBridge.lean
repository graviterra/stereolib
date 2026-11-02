import TetraStereo.OneCenter.LocalizedActualRule4bNodeReadback
import TetraStereo.OneCenter.LocalizedActualRankKeyBridge
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# The actual stage-`.rule4b ρ` key against the independent reading

Bridge stages C1–C3.  For an original-root arm built at stage `.rule4b ρ` whose labels read back
as the molecular readings and whose constitutionally tied siblings agree in their Rule-4a kind
tables (`ArmReadback4b`), the trace induction `arm_node_bridge4b` gives at every node:

* the occupied sibling slots are descending for the independent triple key
  `(ruleKey, K₄ₐ, K₄ᵦ)` over `readingEvidence (senseOf ρ)`, and
* the actual key's Rule-4a and Rule-4b columns are represented by the independent Rule-4a and
  Rule-4b sphere keys.

Consequences: the arm's addressing is ordinary-canonical for the reading evidence (C2,
`arm_ordinaryCanonicalAddressing_readingEvidence`), the actual Rule-4b column of the root key is
represented by the independent complete reading `reading (senseOf ρ)` (C1,
`arm_root_represents4b`), and the production Rule-4b comparison of two arms' readings — built
under possibly different references — is the comparison of their independent readings, under an
explicit Rule-1a tie and Rule-4a table agreement of the two root keys (C3,
`compareReadingsByRule4b_eq_compare_reading`).
-/

namespace TetraStereo.OneCenter
namespace Rule4aTableBridge

open LocalizedCumulativeDecoratedTree
open CertifiedLocalizedCIPInput
open CertifiedLocalizedCIPInput.OriginalRootArm
open OfficialSparseCanonicalVectorComparison
open DeclarativeCIP

noncomputable section
open scoped Classical

variable {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
  {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
    Option LocalizedAuxiliaryLabel} {ρ : RS}

/-- The readback hypotheses of the stage-`.rule4b ρ` bridge. -/
structure ArmReadback4b (arm : input.OriginalRootArm center index (.rule4b ρ) read)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph) : Prop where
  label : ∀ (node : (armGraph arm).Node)
    (actual : LocalizedCumulativeDecoratedTree input (input.certified.input.molecule.atomCount + 1)),
    arm.tree.decoratedSubtreeAt? node.1 = some actual →
      actual.label =
        (occurrenceReading input.moleculeGraph descriptorMap unit (armGraph arm) node).toLocalizedLabel
  tetrahedral : ∀ node : (armGraph arm).Node,
    (occurrenceReading input.moleculeGraph descriptorMap unit (armGraph arm) node).IsTetrahedral
  available : ∀ node : (armGraph arm).Node,
    occurrenceReading input.moleculeGraph descriptorMap unit (armGraph arm) node ≠ .unavailable
  rule4abOnly : Rule4abOnly (armGraph arm)
    (readingEvidence input.moleculeGraph descriptorMap unit (armGraph arm) (senseOf ρ))
  /-- Constitutionally tied **distinct** siblings, each successfully built by the stage-`.rule4b ρ`
  builder at its own source cursor, carry the same Rule-4a kind table.  Stated with the build
  equations (not just table matches) because that is the form the physical sibling theorem
  consumes. -/
  siblingKind : ∀ (node : (armGraph arm).Node)
    (dsub : LocalizedCumulativeDecoratedTree input (input.certified.input.molecule.atomCount + 1)),
    arm.tree.decoratedSubtreeAt? node.1 = some dsub →
      ∀ (i j : Nat) (hi : i < dsub.children.length) (hj : j < dsub.children.length), i ≠ j →
        ∀ (fuelI fuelJ : Nat) (keyI keyJ : input.LocalizedRerootCumulativeRule45Key),
        input.buildLocalizedRerootCumulativeRule45KeyWithRead? (.rule4b ρ) read fuelI
          (dsub.children[i]'hi).source = some keyI →
        input.buildLocalizedRerootCumulativeRule45KeyWithRead? (.rule4b ρ) read fuelJ
          (dsub.children[j]'hj).source = some keyJ →
        OfficialRuleMajorKey.compare keyI.constitutional keyJ.constitutional = Ordering.eq →
          scalar4a keyI = scalar4a keyJ

/-- A recursive sort trace replays as a successful build at the tree's own source cursor (at the
trace's fuel for a node, at fuel `0` for a terminal). -/
theorem _root_.TetraStereo.OneCenter.LocalizedActualRecursiveSortTrace.exists_build_of_trace
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {fuel : Nat} {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedActualRecursiveSortTrace input stage read fuel tree key) :
    ∃ fuel' : Nat,
      input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read fuel' tree.source =
        some key := by
  cases trace with
  | terminal _fuel cursor children childrenComputed terminalChildren _fullMatch _realizes =>
      refine ⟨0, ?_⟩
      show input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read 0 cursor = some _
      unfold CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?
      simp [childrenComputed, terminalChildren]
  | node fuel cursor children childKeys sortedKeys sortedTrees childrenComputed nonempty
      childKeysComputed sortedEq _constitutionalDescending _fullMatch _realizes _childrenTraced =>
      refine ⟨fuel + 1, ?_⟩
      show input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read (fuel + 1) cursor =
        some _
      unfold CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?
      simp [childrenComputed, nonempty, childKeysComputed, sortedEq]

section Bridge

variable (arm : input.OriginalRootArm center index (.rule4b ρ) read)
  {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
  {unit : DetectedOccurrence input.moleculeGraph}

/-- Terminal case. -/
theorem arm_terminal_bridge4b (hyp : ArmReadback4b arm descriptorMap unit)
    (cursor : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1))
    (fullMatch : LocalizedCumulativeTreeFullMatch (.rule4b ρ)
      (localizedRootTree input cursor (read cursor) [])
      (localizedCumulativeRule45TerminalKey input (.rule4b ρ) cursor (read cursor)))
    (realizes : LocalizedCumulativeTreeRealizes input read
      (localizedRootTree input cursor (read cursor) []))
    {W D : ℕ} (node : (armGraph arm).Node)
    (lookup : arm.tree.decoratedSubtreeAt? node.1 =
      some (localizedRootTree input cursor (read cursor) [])) :
    (((slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
          (localizedRootTree input cursor (read cursor) []).children.length).map
        (tripleKey input.moleculeGraph (armGraph arm)
          (readingEvidence input.moleculeGraph descriptorMap unit (armGraph arm) (senseOf ρ)) W D)).Pairwise
      fun x y => y ≤ x) ∧
      Represents4a W D (rule4aComponent input.moleculeGraph (armGraph arm)
        (readingEvidence input.moleculeGraph descriptorMap unit (armGraph arm) (senseOf ρ)) W D node)
        (localizedCumulativeRule45TerminalKey input (.rule4b ρ) cursor (read cursor)) ∧
      Represents4b W D (rule4bComponent input.moleculeGraph (armGraph arm)
        (readingEvidence input.moleculeGraph descriptorMap unit (armGraph arm) (senseOf ρ)) W D node)
        (localizedCumulativeRule45TerminalKey input (.rule4b ρ) cursor (read cursor)) := by
  have childrenEq : (localizedRootTree input cursor (read cursor) []).children = [] := by
    unfold localizedRootTree; rfl
  have pairedNil : List.Forall₂ (fun childKey childTree =>
      LocalizedCumulativeTreeTableMatch (.rule4b ρ) childTree childKey ∧
        LocalizedCumulativeTreeRealizes input read childTree)
      ([] : List input.LocalizedRerootCumulativeRule45Key)
      (localizedRootTree input cursor (read cursor) []).children := by
    rw [childrenEq]; exact List.Forall₂.nil
  have constBot : ∀ digit path, nodePathObservation input.moleculeGraph (armGraph arm) W D 0 node
      (digit :: path) = ⊥ := by
    intro digit path
    have h := (arm_terminal_bridge arm cursor fullMatch realizes (W := W) (D := D) node lookup).2
    have h' := h 0 (by omega) (digit :: path)
    unfold nodePathObservation
    rw [h', encodedObservation_cons_of_key fullMatch.tableMatch realizes pairedNil
      (ruleOfIndex 0) digit path]
    rfl
  refine ⟨by rw [childrenEq]; simp [slotList], ?_, ?_⟩
  · intro path
    cases path with
    | nil =>
        exact stereoNodePathObservation_nil_eq_encoded4a_rule4b descriptorMap unit (armGraph arm) W D
          node fullMatch.tableMatch realizes (hyp.label node _ lookup) (hyp.tetrahedral node)
          (hyp.available node) _
    | cons digit path =>
        have rhs : encoded4a (localizedCumulativeRule45TerminalKey input (.rule4b ρ) cursor (read cursor))
            (digit :: path) = ⊥ := by
          rw [encoded4a_cons_of_key_rule4b fullMatch.tableMatch realizes pairedNil digit path]; rfl
        rw [rhs]
        exact (stereoNodePathObservation_eq_bot_iff input.moleculeGraph (armGraph arm) _ _ W D
          (digit :: path) node).2 (constBot digit path)
  · intro path
    cases path with
    | nil =>
        exact stereoNodePathObservation_nil_eq_encoded4b descriptorMap unit (armGraph arm) W D node
          fullMatch.tableMatch realizes (hyp.label node _ lookup) (hyp.tetrahedral node)
    | cons digit path =>
        have rhs : encoded4b (localizedCumulativeRule45TerminalKey input (.rule4b ρ) cursor (read cursor))
            (digit :: path) = ⊥ := by
          rw [encoded4b_cons_of_key fullMatch.tableMatch realizes pairedNil digit path]; rfl
        rw [rhs]
        exact (stereoNodePathObservation_eq_bot_iff input.moleculeGraph (armGraph arm) _ _ W D
          (digit :: path) node).2 (constBot digit path)

/-- **Recursive Rule-4b bridge.** -/
theorem arm_node_bridge4b (hyp : ArmReadback4b arm descriptorMap unit)
    {W D : ℕ} (hW : (armGraph arm).width ≤ W) (hD : (armGraph arm).height ≤ D)
    {fuel : Nat} (node : (armGraph arm).Node)
    (dsub : LocalizedCumulativeDecoratedTree input (input.certified.input.molecule.atomCount + 1))
    (key : input.LocalizedRerootCumulativeRule45Key)
    (trace : LocalizedActualRecursiveSortTrace input (.rule4b ρ) read fuel dsub key)
    (lookup : arm.tree.decoratedSubtreeAt? node.1 = some dsub) :
    (((slotList (toOfficialSourceTree arm.tree).declarativeAddressing node dsub.children.length).map
        (tripleKey input.moleculeGraph (armGraph arm)
          (readingEvidence input.moleculeGraph descriptorMap unit (armGraph arm) (senseOf ρ)) W D)).Pairwise
      fun x y => y ≤ x) ∧
      Represents4a W D (rule4aComponent input.moleculeGraph (armGraph arm)
        (readingEvidence input.moleculeGraph descriptorMap unit (armGraph arm) (senseOf ρ)) W D node) key ∧
      Represents4b W D (rule4bComponent input.moleculeGraph (armGraph arm)
        (readingEvidence input.moleculeGraph descriptorMap unit (armGraph arm) (senseOf ρ)) W D node) key := by
  induction fuel generalizing dsub key node lookup with
  | zero =>
      cases trace with
      | terminal _fuel cursor _children _childrenComputed _terminalChildren fullMatch realizes =>
          exact arm_terminal_bridge4b arm hyp cursor fullMatch realizes node lookup
  | succ fuel ih =>
      have fullMatch := LocalizedActualRecursiveSortTrace.fullMatch_of_trace trace
      have realizes := LocalizedActualRecursiveSortTrace.realizes_of_trace trace
      rcases LocalizedActualRecursiveSortTrace.structure_of_trace trace with
        ⟨cursor, _children, dsubEq, keyEq, _childrenEq, _childrenComputed, _terminalChildren⟩ |
        ⟨cursor, _children, _childKeys, sortedKeys, sortedTrees, dsubEq, keyEq, childrenEq,
          _childrenComputed, _nonempty, _childKeysComputed, sortedEq, _constitutionalDescending,
          childrenTraced⟩
      · subst dsub; subst key
        exact arm_terminal_bridge4b arm hyp cursor fullMatch realizes node lookup
      · subst dsub; subst key
        set E := readingEvidence input.moleculeGraph descriptorMap unit (armGraph arm) (senseOf ρ)
          with hE
        have hdense : DenseAt (toOfficialSourceTree arm.tree).declarativeAddressing node
            (localizedRootTree input cursor (read cursor) sortedTrees).children.length :=
          denseAt_of_lookup arm node (localizedRootTree input cursor (read cursor) sortedTrees) lookup
        have paired := LocalizedActualRecursiveSortTraceList.to_forall₂ childrenTraced
        have lengthEq : sortedKeys.length = sortedTrees.length := List.Forall₂.length_eq paired
        have pairedMatch : List.Forall₂ (fun childKey childTree =>
            LocalizedCumulativeTreeTableMatch (.rule4b ρ) childTree childKey ∧
              LocalizedCumulativeTreeRealizes input read childTree) sortedKeys sortedTrees :=
          List.Forall₂.imp (fun childKey childTree related =>
            ⟨(LocalizedActualRecursiveSortTrace.fullMatch_of_trace related).tableMatch,
              LocalizedActualRecursiveSortTrace.realizes_of_trace related⟩) paired
        have descending : sortedKeys.Pairwise fun left right =>
            input.compareLocalizedRerootCumulativeRule45Keys left right ≠ Ordering.lt := by
          rw [sortedEq]
          exact input.sortLocalizedRerootCumulativeRule45Keys_descending _
        have countEq : (localizedRootTree input cursor (read cursor) sortedTrees).children.length =
            sortedTrees.length := by rw [childrenEq]
        have slotLength : (slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
            (localizedRootTree input cursor (read cursor) sortedTrees).children.length).length =
            sortedTrees.length := by simp [slotList, countEq]
        have childAt : ∀ i (hi : i < sortedTrees.length), ∃ child : (armGraph arm).Node,
            (slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
              (localizedRootTree input cursor (read cursor) sortedTrees).children.length)[i]? =
                some child ∧
              child.1 = node.1 ++ [i] ∧
                arm.tree.decoratedSubtreeAt? child.1 = some (sortedTrees[i]'hi) := by
          intro i hi
          obtain ⟨child, slotSome, addr⟩ := slotList_getD_of_lt
            (addressing := (toOfficialSourceTree arm.tree).declarativeAddressing) (parent := node)
            (count := (localizedRootTree input cursor (read cursor) sortedTrees).children.length)
            hdense (by rw [countEq]; exact hi)
          have addrFlat : child.1 = node.1 ++ [i] := by
            rw [(toOfficialSourceTree arm.tree).declarativeAddressing_address,
              (toOfficialSourceTree arm.tree).declarativeAddressing_address] at addr
            exact addr
          refine ⟨child, slotSome, addrFlat, ?_⟩
          rw [addrFlat, decoratedSubtreeAt?_append arm.tree node.1 [i], lookup]
          simp [childrenEq, decoratedSubtreeAt?, List.getElem?_eq_getElem hi]
        have traceAt : ∀ i (hi : i < sortedTrees.length),
            LocalizedActualRecursiveSortTrace input (.rule4b ρ) read fuel (sortedTrees[i]'hi)
              (sortedKeys[i]'(by omega)) :=
          fun i hi => List.Forall₂.get (i := i) paired (by omega) hi
        have ihAt : ∀ i (hi : i < sortedTrees.length) (child : (armGraph arm).Node),
            arm.tree.decoratedSubtreeAt? child.1 = some (sortedTrees[i]'hi) →
              Represents4a W D (rule4aComponent input.moleculeGraph (armGraph arm) E W D child)
                  (sortedKeys[i]'(by omega)) ∧
                Represents4b W D (rule4bComponent input.moleculeGraph (armGraph arm) E W D child)
                  (sortedKeys[i]'(by omega)) :=
          fun i hi child hl => (ih child (sortedTrees[i]'hi) (sortedKeys[i]'(by omega)) (traceAt i hi) hl).2
        have constAt : ∀ i (hi : i < sortedTrees.length) (child : (armGraph arm).Node),
            arm.tree.decoratedSubtreeAt? child.1 = some (sortedTrees[i]'hi) →
              Represents W D (ruleKey input.moleculeGraph (armGraph arm) W D child)
                (sortedKeys[i]'(by omega)).constitutional :=
          fun i hi child hl =>
            (arm_node_bridge arm hW hD child (sortedTrees[i]'hi) (sortedKeys[i]'(by omega))
              (traceAt i hi) hl).2
        have kindAt : ∀ i j (hi : i < sortedTrees.length) (hj : j < sortedTrees.length), i ≠ j →
            OfficialRuleMajorKey.compare (sortedKeys[i]'(by omega)).constitutional
                (sortedKeys[j]'(by omega)).constitutional = Ordering.eq →
              scalar4a (sortedKeys[i]'(by omega)) = scalar4a (sortedKeys[j]'(by omega)) := by
          intro i j hi hj hij htie
          obtain ⟨fuelI, builtI⟩ :=
            LocalizedActualRecursiveSortTrace.exists_build_of_trace (traceAt i hi)
          obtain ⟨fuelJ, builtJ⟩ :=
            LocalizedActualRecursiveSortTrace.exists_build_of_trace (traceAt j hj)
          exact hyp.siblingKind node _ lookup i j hi hj hij fuelI fuelJ _ _ builtI builtJ htie
        have slotSorted : ((slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
            (localizedRootTree input cursor (read cursor) sortedTrees).children.length).map
              (tripleKey input.moleculeGraph (armGraph arm) E W D)).Pairwise fun x y => y ≤ x := by
          rw [List.pairwise_iff_getElem]
          intro i j hi hj hij
          rw [List.length_map, slotLength] at hi hj
          obtain ⟨childI, slotI, _, lookupI⟩ := childAt i hi
          obtain ⟨childJ, slotJ, _, lookupJ⟩ := childAt j hj
          have hne : input.compareLocalizedRerootCumulativeRule45Keys (sortedKeys[i]'(by omega))
              (sortedKeys[j]'(by omega)) ≠ Ordering.lt :=
            (List.pairwise_iff_getElem.1 descending) i j (by omega) (by omega) hij
          have hle := tripleKey_le_of_compare_ne_lt (armGraph arm) E
            (LocalizedActualRecursiveSortTrace.fullMatch_of_trace (traceAt i hi)).tableMatch
            (LocalizedActualRecursiveSortTrace.fullMatch_of_trace (traceAt j hj)).tableMatch
            (LocalizedActualRecursiveSortTrace.realizes_of_trace (traceAt i hi))
            (LocalizedActualRecursiveSortTrace.realizes_of_trace (traceAt j hj))
            (constAt i hi childI lookupI) (constAt j hj childJ lookupJ)
            (ihAt i hi childI lookupI).1 (ihAt j hj childJ lookupJ).1
            (ihAt i hi childI lookupI).2 (ihAt j hj childJ lookupJ).2
            (kindAt i j hi hj (Nat.ne_of_lt hij)) hne
          have getI : (slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
              (localizedRootTree input cursor (read cursor) sortedTrees).children.length)[i]'(by
                rw [slotLength]; exact hi) = childI :=
            Option.some.inj ((List.getElem?_eq_getElem _).symm.trans slotI)
          have getJ : (slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
              (localizedRootTree input cursor (read cursor) sortedTrees).children.length)[j]'(by
                rw [slotLength]; exact hj) = childJ :=
            Option.some.inj ((List.getElem?_eq_getElem _).symm.trans slotJ)
          simpa [List.getElem_map, getI, getJ] using hle
        have slotSortedOrd : ((slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
            (localizedRootTree input cursor (read cursor) sortedTrees).children.length).map
              (ordinaryKey input.moleculeGraph (armGraph arm) E W D)).Pairwise fun x y => y ≤ x := by
          rw [List.pairwise_map] at slotSorted ⊢
          exact slotSorted.imp fun h =>
            (ordinaryKey_le_iff_tripleKey input.moleculeGraph (armGraph arm) E hyp.rule4abOnly W D
              _ _).2 h
        have hperm := slotList_perm (addressing := (toOfficialSourceTree arm.tree).declarativeAddressing)
          (parent := node)
          (count := (localizedRootTree input cursor (read cursor) sortedTrees).children.length) hdense
        -- the common `cons` argument for both columns
        have consCase : ∀ (rule : StereochemicalRule)
            (enc : input.LocalizedRerootCumulativeRule45Key → List Nat → WithBot StereoLabel)
            (comp : (armGraph arm).Node → Certificate.CanonicalSphereKey.Key StereoLabel),
            (∀ i (hi : i < sortedTrees.length) (child : (armGraph arm).Node),
              arm.tree.decoratedSubtreeAt? child.1 = some (sortedTrees[i]'hi) →
                ∀ path, Certificate.CanonicalSphereKey.pathObservationOf W D (comp child) path =
                  enc (sortedKeys[i]'(by omega)) path) →
            (∀ child : (armGraph arm).Node, comp child =
              (ofLex (ordinaryKey input.moleculeGraph (armGraph arm) E W D child)).2.getD
                (stereoIndex rule) []) →
            (∀ digit path, enc (localizedCumulativeRule45StepKey input (.rule4b ρ) cursor (read cursor)
                sortedKeys) (digit :: path) =
              ((sortedKeys[digit]?).map fun childKey => enc childKey path).getD ⊥) →
            ∀ digit path,
              Certificate.CanonicalSphereKey.pathObservationOf W D (comp node) (digit :: path) =
                enc (localizedCumulativeRule45StepKey input (.rule4b ρ) cursor (read cursor) sortedKeys)
                  (digit :: path) := by
          intro rule enc comp repAt compEq encCons digit path
          rw [compEq node]
          change stereoNodePathObservation input.moleculeGraph (armGraph arm) E W D rule node
            (digit :: path) = _
          rw [stereoNodePathObservation_cons input.moleculeGraph (armGraph arm) E W D rule node hperm
            slotSortedOrd digit path, encCons digit path]
          by_cases hdigit : digit < sortedTrees.length
          · obtain ⟨child, slotSome, childAddr, childLookup⟩ := childAt digit hdigit
            have digitLtKeys : digit < sortedKeys.length := by omega
            have repChild := repAt digit hdigit child childLookup path
            rw [compEq child] at repChild
            rw [slotSome, List.getElem?_eq_getElem digitLtKeys]
            simp only [Option.map_some, Option.getD_some]
            by_cases hgate : digit < W ∧ path.length < D
            · rw [if_pos hgate]
              exact repChild
            · rw [if_neg hgate, ← repChild]
              symm
              apply (stereoNodePathObservation_eq_bot_iff input.moleculeGraph (armGraph arm) E rule W D
                path child).2
              by_contra hne
              have bound := depth_add_length_le_of_nodePathObservation input.moleculeGraph (armGraph arm)
                (W := W) (D := D) (by omega : (0 : ℕ) < 3) path child hne
              have childDepth : (armGraph arm).depth child = (armGraph arm).depth node + 1 :=
                (armGraph arm).child_depth ⟨digit, childAddr⟩
              have hdigitLtW : digit < W := by
                have countLe : sortedTrees.length ≤ (armGraph arm).width := by
                  have := count_le_width
                    (addressing := (toOfficialSourceTree arm.tree).declarativeAddressing)
                    (parent := node)
                    (count := (localizedRootTree input cursor (read cursor) sortedTrees).children.length)
                    hdense
                  rw [countEq] at this
                  exact this
                omega
              have hpath : ¬ path.length < D := fun h => hgate ⟨hdigitLtW, h⟩
              omega
          · have slotNone : (slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
                (localizedRootTree input cursor (read cursor) sortedTrees).children.length)[digit]? =
                  none := by
              rw [List.getElem?_eq_none_iff, slotLength]; omega
            have keysNone : sortedKeys[digit]? = none := by
              rw [List.getElem?_eq_none_iff]; omega
            rw [slotNone, keysNone]
            split <;> rfl
        refine ⟨slotSorted, ?_, ?_⟩
        · intro path
          cases path with
          | nil =>
              exact stereoNodePathObservation_nil_eq_encoded4a_rule4b descriptorMap unit (armGraph arm)
                W D node fullMatch.tableMatch realizes (hyp.label node _ lookup) (hyp.tetrahedral node)
                (hyp.available node) _
          | cons digit path =>
              exact consCase .rule4aStereogenicUnitKind encoded4a
                (rule4aComponent input.moleculeGraph (armGraph arm) E W D)
                (fun i hi child hl => (ihAt i hi child hl).1) (fun _ => rfl)
                (fun digit path => encoded4a_cons_of_key_rule4b fullMatch.tableMatch realizes
                  pairedMatch digit path) digit path
        · intro path
          cases path with
          | nil =>
              exact stereoNodePathObservation_nil_eq_encoded4b descriptorMap unit (armGraph arm) W D
                node fullMatch.tableMatch realizes (hyp.label node _ lookup) (hyp.tetrahedral node)
          | cons digit path =>
              exact consCase .rule4bLikeUnlikeDescriptorPairs encoded4b
                (rule4bComponent input.moleculeGraph (armGraph arm) E W D)
                (fun i hi child hl => (ihAt i hi child hl).2) (fun _ => rfl)
                (fun digit path => encoded4b_cons_of_key fullMatch.tableMatch realizes
                  pairedMatch digit path) digit path

/-! ## C2: canonical membership for the reading evidence -/

theorem arm_keySorted_readingEvidence (hyp : ArmReadback4b arm descriptorMap unit) :
    KeySorted (ordinaryKey input.moleculeGraph (armGraph arm)
        (readingEvidence input.moleculeGraph descriptorMap unit (armGraph arm) (senseOf ρ))
        (armGraph arm).width (armGraph arm).height)
      (toOfficialSourceTree arm.tree).declarativeAddressing := by
  intro parent first second firstSlot secondSlot addrFirst addrSecond hlt
  obtain ⟨dsub, lookup, _⟩ := decoratedSubtree_of_node arm parent
  have hdense : DenseAt (toOfficialSourceTree arm.tree).declarativeAddressing parent
      dsub.children.length := denseAt_of_lookup arm parent dsub lookup
  rcases trace_of_subtree input (.rule4b ρ) read arm.trace parent.1 dsub lookup with
    ⟨fuel', key', trace'⟩
  have bridge := arm_node_bridge4b arm hyp (W := (armGraph arm).width) (D := (armGraph arm).height)
    le_rfl le_rfl parent dsub key' trace' lookup
  have slotSorted := bridge.1
  have firstLt : firstSlot < dsub.children.length := (hdense firstSlot).1 ⟨first, addrFirst⟩
  have secondLt : secondSlot < dsub.children.length := (hdense secondSlot).1 ⟨second, addrSecond⟩
  obtain ⟨childI, slotI, addrI⟩ := slotList_getD_of_lt
    (addressing := (toOfficialSourceTree arm.tree).declarativeAddressing) (parent := parent)
    (count := dsub.children.length) hdense firstLt
  obtain ⟨childJ, slotJ, addrJ⟩ := slotList_getD_of_lt
    (addressing := (toOfficialSourceTree arm.tree).declarativeAddressing) (parent := parent)
    (count := dsub.children.length) hdense secondLt
  have firstEq : first = childI :=
    Subtype.ext (by
      rw [(toOfficialSourceTree arm.tree).declarativeAddressing_address,
        (toOfficialSourceTree arm.tree).declarativeAddressing_address] at addrFirst addrI
      exact addrFirst.trans addrI.symm)
  have secondEq : second = childJ :=
    Subtype.ext (by
      rw [(toOfficialSourceTree arm.tree).declarativeAddressing_address,
        (toOfficialSourceTree arm.tree).declarativeAddressing_address] at addrSecond addrJ
      exact addrSecond.trans addrJ.symm)
  have slotLength : (slotList (toOfficialSourceTree arm.tree).declarativeAddressing parent
      dsub.children.length).length = dsub.children.length := by simp [slotList]
  have getI : (slotList (toOfficialSourceTree arm.tree).declarativeAddressing parent
      dsub.children.length)[firstSlot]'(by rw [slotLength]; exact firstLt) = childI :=
    Option.some.inj ((List.getElem?_eq_getElem _).symm.trans slotI)
  have getJ : (slotList (toOfficialSourceTree arm.tree).declarativeAddressing parent
      dsub.children.length)[secondSlot]'(by rw [slotLength]; exact secondLt) = childJ :=
    Option.some.inj ((List.getElem?_eq_getElem _).symm.trans slotJ)
  have hpair := (List.pairwise_iff_getElem.1 slotSorted) firstSlot secondSlot
    (by rw [List.length_map, slotLength]; exact firstLt)
    (by rw [List.length_map, slotLength]; exact secondLt) hlt
  simp only [List.getElem_map, getI, getJ] at hpair
  rw [firstEq, secondEq]
  exact (ordinaryKey_le_iff_tripleKey input.moleculeGraph (armGraph arm) _ hyp.rule4abOnly _ _ _ _).2
    hpair

/-- **C2.**  The actual stage-`.rule4b ρ` addressing is ordinary-canonical for the reading
evidence under `senseOf ρ`. -/
theorem arm_ordinaryCanonicalAddressing_readingEvidence (hyp : ArmReadback4b arm descriptorMap unit) :
    OrdinaryCanonicalAddressing input.moleculeGraph
      (readingEvidence input.moleculeGraph descriptorMap unit (armGraph arm) (senseOf ρ))
      (toOfficialSourceTree arm.tree).declarativeAddressing :=
  ⟨(toOfficialSourceTree arm.tree).declarativeAddressing_dense, arm_keySorted_readingEvidence arm hyp⟩

/-! ## C1: the root key's Rule-4b column is the independent reading -/

/-- **C1.**  The actual Rule-4b column of the arm's root key is represented by the independent
complete reading under `senseOf ρ`. -/
theorem arm_root_represents4b (hyp : ArmReadback4b arm descriptorMap unit) :
    Represents4b (armGraph arm).width (armGraph arm).height
      (reading input.moleculeGraph descriptorMap unit (armGraph arm) (senseOf ρ)) arm.key :=
  (arm_node_bridge4b arm hyp le_rfl le_rfl (armGraph arm).root arm.tree arm.key arm.trace rfl).2.2

theorem arm_root_represents4a (hyp : ArmReadback4b arm descriptorMap unit) :
    Represents4a (armGraph arm).width (armGraph arm).height
      (rule4aComponent input.moleculeGraph (armGraph arm)
        (readingEvidence input.moleculeGraph descriptorMap unit (armGraph arm) (senseOf ρ))
        (armGraph arm).width (armGraph arm).height (armGraph arm).root) arm.key :=
  (arm_node_bridge4b arm hyp le_rfl le_rfl (armGraph arm).root arm.tree arm.key arm.trace rfl).2.1

end Bridge

/-! ## C3: the production Rule-4b comparison of two arms' readings -/

/-- **C3.**  For two arms built under references `ρ₁`, `ρ₂` (possibly different) whose root keys
tie at Rule 1a and agree in their Rule-4a kind tables, the production Rule-4b comparison of their
readings is the comparison of the independent Rule-4b components of the two roots, laid out at any
common layout `(W, D)` bounding both arms. -/
theorem compareReadingsByRule4b_eq_compare_rule4bComponent
    {center₁ center₂ : input.TetrahedralCenter} {index₁ index₂ : Fin 4} {ρ₁ ρ₂ : RS}
    {read₁ read₂ : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm₁ : input.OriginalRootArm center₁ index₁ (.rule4b ρ₁) read₁)
    (arm₂ : input.OriginalRootArm center₂ index₂ (.rule4b ρ₂) read₂)
    {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
    {unit₁ unit₂ : DetectedOccurrence input.moleculeGraph}
    (hyp₁ : ArmReadback4b arm₁ descriptorMap unit₁) (hyp₂ : ArmReadback4b arm₂ descriptorMap unit₂)
    (reading₁ reading₂ : input.LocalizedRerootRule4bcReading)
    (hkey₁ : reading₁.rule4bKey = arm₁.key) (hkey₂ : reading₂.rule4bKey = arm₂.key)
    {W D : ℕ} (hW₁ : (armGraph arm₁).width ≤ W) (hD₁ : (armGraph arm₁).height ≤ D)
    (hW₂ : (armGraph arm₂).width ≤ W) (hD₂ : (armGraph arm₂).height ≤ D)
    (tied1a : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      arm₁.key.constitutional.rule1a arm₂.key.constitutional.rule1a = Ordering.eq)
    (tied4a : scalar4a arm₁.key = scalar4a arm₂.key) :
    input.compareLocalizedRerootRule4bcReadingsByRule4b reading₁ reading₂ =
      compare
        (rule4bComponent input.moleculeGraph (armGraph arm₁)
          (readingEvidence input.moleculeGraph descriptorMap unit₁ (armGraph arm₁) (senseOf ρ₁)) W D
          (armGraph arm₁).root)
        (rule4bComponent input.moleculeGraph (armGraph arm₂)
          (readingEvidence input.moleculeGraph descriptorMap unit₂ (armGraph arm₂) (senseOf ρ₂)) W D
          (armGraph arm₂).root) := by
  unfold compareLocalizedRerootRule4bcReadingsByRule4b
  simp only [Ordering.byKey]
  rw [hkey₁, hkey₂]
  have rep₁ := (arm_node_bridge4b arm₁ hyp₁ hW₁ hD₁ (armGraph arm₁).root arm₁.tree arm₁.key
    arm₁.trace rfl).2.2
  have rep₂ := (arm_node_bridge4b arm₂ hyp₂ hW₂ hD₂ (armGraph arm₂).root arm₂.tree arm₂.key
    arm₂.trace rfl).2.2
  have tied4a' : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (scalar4a arm₁.key) (scalar4a arm₂.key) = Ordering.eq := by
    rw [tied4a]
    exact CompilerProjectionFidelity.compareSparseLayers_self OfficialRuleMajorKey.compareNat
      CompilerProjectionFidelity.compareNat_self _
  rw [compare_descriptor_eq_scalar4b_of_scalar4a_eq arm₁.tableMatch arm₂.tableMatch tied4a]
  exact compare_of_pathFirstDifference
    (ordinaryKey_stereo_wellShaped input.moleculeGraph (armGraph arm₁) _ W D
      .rule4bLikeUnlikeDescriptorPairs (armGraph arm₁).root)
    (ordinaryKey_stereo_wellShaped input.moleculeGraph (armGraph arm₂) _ W D
      .rule4bLikeUnlikeDescriptorPairs (armGraph arm₂).root)
    rep₁ rep₂
    (fun outcome => rule4b_pathFirstDifference_iff arm₁.tableMatch arm₂.tableMatch arm₁.realizes
      arm₂.realizes tied1a tied4a' outcome)

/-- **C3 at the arms' own layouts.**  When the two arms have the same width and height, the
production Rule-4b comparison is the comparison of the independent complete readings. -/
theorem compareReadingsByRule4b_eq_compare_reading
    {center₁ center₂ : input.TetrahedralCenter} {index₁ index₂ : Fin 4} {ρ₁ ρ₂ : RS}
    {read₁ read₂ : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm₁ : input.OriginalRootArm center₁ index₁ (.rule4b ρ₁) read₁)
    (arm₂ : input.OriginalRootArm center₂ index₂ (.rule4b ρ₂) read₂)
    {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
    {unit₁ unit₂ : DetectedOccurrence input.moleculeGraph}
    (hyp₁ : ArmReadback4b arm₁ descriptorMap unit₁) (hyp₂ : ArmReadback4b arm₂ descriptorMap unit₂)
    (reading₁ reading₂ : input.LocalizedRerootRule4bcReading)
    (hkey₁ : reading₁.rule4bKey = arm₁.key) (hkey₂ : reading₂.rule4bKey = arm₂.key)
    (hW : (armGraph arm₁).width = (armGraph arm₂).width)
    (hD : (armGraph arm₁).height = (armGraph arm₂).height)
    (tied1a : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      arm₁.key.constitutional.rule1a arm₂.key.constitutional.rule1a = Ordering.eq)
    (tied4a : scalar4a arm₁.key = scalar4a arm₂.key) :
    input.compareLocalizedRerootRule4bcReadingsByRule4b reading₁ reading₂ =
      compare (reading input.moleculeGraph descriptorMap unit₁ (armGraph arm₁) (senseOf ρ₁))
        (reading input.moleculeGraph descriptorMap unit₂ (armGraph arm₂) (senseOf ρ₂)) := by
  have h := compareReadingsByRule4b_eq_compare_rule4bComponent arm₁ arm₂ hyp₁ hyp₂ reading₁ reading₂
    hkey₁ hkey₂ (W := (armGraph arm₁).width) (D := (armGraph arm₁).height) le_rfl le_rfl hW.ge hD.ge
    tied1a tied4a
  rw [h]
  unfold reading rule4bComponent
  rw [hW, hD]

end
end Rule4aTableBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.arm_node_bridge4b
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.arm_ordinaryCanonicalAddressing_readingEvidence
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.arm_root_represents4b
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.compareReadingsByRule4b_eq_compare_rule4bComponent
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.compareReadingsByRule4b_eq_compare_reading
