import TetraStereo.OneCenter.LocalizedChemicalRingActualFullLabelMatch
import TetraStereo.OneCenter.LocalizedCumulativeMirrorPopulationTransport
import TetraStereo.OneCenter.LocalizedRuleMajorRule4aAgreement
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Ring-safe replay of decoded occurrence correspondences

Equal fully decorated observations give a relation on actual occurrence cursors preserving
the actual atom-label columns, stored duplicate distance, child multisets and exact reader.
No acyclicity, global atom permutation or real-atom restriction is needed. In particular, ring
duplicate nodes keep their own stored observations rather than being replaced by their atoms.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingDecodedRelation

open CertifiedLocalizedCIPInput LocalizedCumulativeDecoratedTree

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}

theorem shape_eq_of_observation_eq
    (left right : LocalizedCumulativeDecoratedTree input carrierFuel)
    (same : observation left = observation right) : shape left = shape right := by
  cases left with
  | mk src z dist mass label children =>
    cases right with
    | mk src' z' dist' mass' label' children' =>
      simp only [table_observation_mk, LocalizedCumulativeBranchObservation.mk.injEq,
        LocalizedCumulativeBranchDecoration.mk.injEq] at same
      rcases same with ⟨⟨rfl, rfl, rfl, _⟩, childObs⟩
      rw [table_shape_mk, table_shape_mk, table_shapeList_eq_map, table_shapeList_eq_map]
      congr 1
      rw [table_observationList_eq_map, table_observationList_eq_map] at childObs
      have lengths : children.length = children'.length := by
        simpa using congrArg List.length childObs
      apply List.ext_getElem (by simpa using lengths)
      intro i hi hj
      simp only [List.getElem_map]
      apply shape_eq_of_observation_eq
      have sameAt := congrArg (fun xs => xs[i]?) childObs
      simpa only [List.getElem?_map, List.getElem?_eq_getElem
        (by simpa using hi : i < children.length), List.getElem?_eq_getElem
        (by simpa using hj : i < children'.length), Option.map_some, Option.some.injEq] using sameAt
termination_by sizeOf left
decreasing_by
  have childLt := List.sizeOf_lt_of_mem (List.getElem_mem (by simpa using hi : i < children.length))
  simp_all only [List.length_map]
  simp_all
  omega

theorem realized_atomLabel (read : input.LocalizedRerootCursor carrierFuel →
    Option LocalizedAuxiliaryLabel) (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (realizes : LocalizedCumulativeTreeRealizes input read tree) :
    input.moleculeGraph.officialNodeAtomLabel tree.source.occurrence.1.node =
      toLex (tree.atomicNumber, tree.isotopeMass) := by
  cases realizes
  rfl

theorem related_atomLabel
    {left right : LocalizedCumulativeDecoratedTree input carrierFuel}
    (same : shape left = shape right)
    {readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (realL : LocalizedCumulativeTreeRealizes input readL left)
    (realR : LocalizedCumulativeTreeRealizes input readR right)
    {x y : input.LocalizedRerootCursor carrierFuel}
    (related : ShapePositionCursorRelation same x y) :
    input.moleculeGraph.officialNodeAtomLabel x.occurrence.1.node =
      input.moleculeGraph.officialNodeAtomLabel y.occurrence.1.node := by
  obtain ⟨p, rfl, rfl⟩ := related
  change input.moleculeGraph.officialNodeAtomLabel (positionNode p).source.occurrence.1.node =
    input.moleculeGraph.officialNodeAtomLabel
      (positionNode (shapePositionEquiv same p)).source.occurrence.1.node
  rw [realized_atomLabel readL _ (realizes_of_subtree realL (positionNode_spec p)),
    realized_atomLabel readR _
      (realizes_of_subtree realR (positionNode_spec (shapePositionEquiv same p))),
    shapePositionEquiv_positionNode_atomicNumber_eq,
    shapePositionEquiv_positionNode_isotopeMass_eq]

theorem related_readers
    {left right : LocalizedCumulativeDecoratedTree input carrierFuel}
    (same : observation left = observation right)
    {readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (realL : LocalizedCumulativeTreeRealizes input readL left)
    (realR : LocalizedCumulativeTreeRealizes input readR right)
    {x y : input.LocalizedRerootCursor carrierFuel}
    (related : ShapePositionCursorRelation (shape_eq_of_observation_eq left right same) x y) :
    readL x = readR y := by
  obtain ⟨p, rfl, rfl⟩ := related
  let q := shapePositionEquiv (shape_eq_of_observation_eq left right same) p
  have labels := subtreeAt?_label_eq_of_observation_eq p.1 left right same
    (positionNode p) (positionNode q) (positionNode_spec p)
    (by simpa only [q, shapePositionEquiv_val] using positionNode_spec q)
  exact (label_eq_read_source (realizes_of_subtree realL (positionNode_spec p))).symm.trans
    (labels.symm.trans (label_eq_read_source (realizes_of_subtree realR (positionNode_spec q))))

/-- Actual Rule-4a populations agree as multisets at every rank and depth. The relation may
pair different cursors and different readers; successful builds supply the populations. -/
theorem rule4a_population_perm_of_related
    (readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (R : input.LocalizedRerootCursor carrierFuel → input.LocalizedRerootCursor carrierFuel → Prop)
    (atomLabel : ∀ x y, R x y → input.moleculeGraph.officialNodeAtomLabel x.occurrence.1.node =
      input.moleculeGraph.officialNodeAtomLabel y.occurrence.1.node)
    (distance : ∀ x y, R x y → x.occurrence.1.node.rule1bRootDistance =
      y.occurrence.1.node.rule1bRootDistance)
    (children : ∀ x y, R x y → ∃ frame,
      (input.executableLocalizedRerootChildren x).Perm frame ∧
        List.Forall₂ R frame (input.executableLocalizedRerootChildren y))
    (readers : ∀ x y, R x y → readL x = readR y)
    (fuel : Nat) (x y : input.LocalizedRerootCursor carrierFuel) (related : R x y)
    (keyL keyR : input.LocalizedRerootCumulativeRule45Key)
    (builtL : input.buildRuleMajorCumulativeWithRead? .rule4a readL fuel x = some keyL)
    (builtR : input.buildRuleMajorCumulativeWithRead? .rule4a readR fuel y = some keyR)
    (depth : Nat) (rank : List Nat) :
    (localizedChiralDescriptorsAtRank rank (keyL.rankedLabels.getD depth [])).Perm
      (localizedChiralDescriptorsAtRank rank (keyR.rankedLabels.getD depth [])) := by
  rw [input.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized] at builtL builtR
  have reflected := input.buildLocalizedRerootCumulativeRule45KeyWithRead?_reflectUppercase
    .rule4a readR fuel y
  rw [builtR] at reflected
  have populations :=
    input.buildLocalizedRerootCumulativeRule45KeyWithRead?_rule4a_population_swap_perm_of_related
      readL (fun z => reflectUppercaseOptionalLabel (readR z)) R atomLabel distance children
      (fun a b h => by rw [readers a b h]) fuel x y related builtL reflected depth rank
  rw [reflectLocalizedRerootCumulativeRule45Key_rankedLabels,
    localizedChiralDescriptorsAtRank_reflect_getD] at populations
  have twice : ∀ rs : RS, rs.swap.swap = rs := by intro rs; cases rs <;> rfl
  simpa [List.map_map, Function.comp_def, twice] using populations.map RS.swap

/-- With the actual dependency reader, equality of the full decoded observation determines the
reference selector after rebuilding at any corresponding positions, not merely at the root. -/
theorem references_eq_of_observations
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    {left right : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realL : LocalizedCumulativeTreeRealizes input (input.localizedDependencyLabel target view) left)
    (realR : LocalizedCumulativeTreeRealizes input (input.localizedDependencyLabel target view) right)
    (same : observation left = observation right)
    (fuel : Nat) (x y : input.LocalizedRerootCursor carrierFuel)
    (related : ShapePositionCursorRelation (shape_eq_of_observation_eq left right same) x y)
    (keyL keyR : input.LocalizedRerootCumulativeRule45Key)
    (builtL : input.buildRuleMajorCumulativeWithRead? .rule4a
      (input.localizedDependencyLabel target view) fuel x = some keyL)
    (builtR : input.buildRuleMajorCumulativeWithRead? .rule4a
      (input.localizedDependencyLabel target view) fuel y = some keyR) :
    localizedRule4bReferencesFromRankedLabels keyL.rankedLabels =
      localizedRule4bReferencesFromRankedLabels keyR.rankedLabels := by
  let hs := shape_eq_of_observation_eq left right same
  let R := ShapePositionCursorRelation hs
  have atomLabel := fun a b (h : R a b) => related_atomLabel hs realL realR h
  have distance := fun a b (h : R a b) => shapePositionCursorRelation_rootDistance hs realL realR h
  have children := fun a b (h : R a b) => shapePositionCursorRelation_children hs realL realR h
  have readers := fun a b (h : R a b) => related_readers same realL realR h
  have populations := rule4a_population_perm_of_related _ _ R atomLabel distance children readers
    fuel x y related keyL keyR builtL builtR
  rw [input.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized] at builtL builtR
  have obs := input.buildLocalizedRerootCumulativeRule45KeyWithRead?_map_observable_eq_of_related
    .rule4a .rule4a (input.localizedDependencyLabel target view)
    (input.localizedDependencyLabel target view) R atomLabel distance children
    (fun a b h => by rw [readers a b h]) fuel x y related
  rw [builtL, builtR] at obs
  have obsEq := Option.some.inj obs
  rw [input.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel]
    at builtL builtR
  have projection := input.declarative_rule4a_rankedLabels_projection_eq target view fuel x y keyL keyR
    (input.buildLocalizedRerootCumulativeRule45Key?_sound _ _ _ _ _ _ builtL)
    (input.buildLocalizedRerootCumulativeRule45Key?_sound _ _ _ _ _ _ builtR) obsEq
  exact localizedRule4bReferencesFromRankedLabels_eq_of_rankedChiralAgrees projection populations

end TetraStereo.OneCenter.LocalizedChemicalRingDecodedRelation

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDecodedRelation.shape_eq_of_observation_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDecodedRelation.related_atomLabel
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDecodedRelation.related_readers
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDecodedRelation.rule4a_population_perm_of_related
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDecodedRelation.references_eq_of_observations
