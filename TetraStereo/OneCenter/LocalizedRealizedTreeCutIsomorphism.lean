import TetraStereo.OneCenter.LocalizedCumulativeTreeTableReconstruction
import TetraStereo.OneCenter.LocalizedRealizedTreeCutEmbedding
import TetraStereo.OneCenter.LocalizedRealizedTreeCutEquivalence
import TetraStereo.OneCenter.AcyclicCutBranchAutomorphism
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput
open LocalizedCumulativeDecoratedTree
open AcyclicCutBranchAutomorphism














































variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}

/-- Recursive node correspondence between two source-erased decorated occurrence trees.  The
source cursor and reader label are retained on both sides but are not compared: only the three
constitutional columns and the sorted child alignment are part of the relation. -/
inductive RealizedTreeMatch :
    LocalizedCumulativeDecoratedTree input carrierFuel →
      LocalizedCumulativeDecoratedTree input carrierFuel → Prop where
  | mk (sourceL sourceR : input.LocalizedRerootCursor carrierFuel)
      (atomicNumberL atomicNumberR rule1bDistanceL rule1bDistanceR
        isotopeMassL isotopeMassR : Nat)
      (labelL labelR : Option LocalizedAuxiliaryLabel)
      (childrenL childrenR : List (LocalizedCumulativeDecoratedTree input carrierFuel))
      (atomicNumberEq : atomicNumberL = atomicNumberR)
      (rule1bDistanceEq : rule1bDistanceL = rule1bDistanceR)
      (isotopeMassEq : isotopeMassL = isotopeMassR)
      (childrenMatch : List.Forall₂ RealizedTreeMatch childrenL childrenR) :
      RealizedTreeMatch
        ⟨sourceL, atomicNumberL, rule1bDistanceL, isotopeMassL, labelL, childrenL⟩
        ⟨sourceR, atomicNumberR, rule1bDistanceR, isotopeMassR, labelR, childrenR⟩

/-! ## List helpers for the correspondence -/

/-- Equality of pointwise mapped lists exposes the pointwise relation, with no alignment
assumption beyond the maps being equal. -/
theorem forall₂_of_map_eq {α β γ : Type*} (f : α → γ) (g : β → γ) :
    ∀ {left : List α} {right : List β},
      left.map f = right.map g → List.Forall₂ (fun a b => f a = g b) left right
  | [], [], _ => List.Forall₂.nil
  | [], _ :: _, same => by simp at same
  | _ :: _, [], same => by simp at same
  | a :: as, b :: bs, same => by
      simp only [List.map_cons, List.cons.injEq] at same
      exact List.Forall₂.cons same.1 (forall₂_of_map_eq f g same.2)

/-- Pointwise lifting of a relation along a left-list membership witness. -/
theorem forall₂_imp_of_mem {α β : Type*} {R S : α → β → Prop}
    {left : List α} {right : List β} (h : List.Forall₂ R left right)
    (step : ∀ a b, a ∈ left → R a b → S a b) : List.Forall₂ S left right := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons head tail inductionHypothesis =>
      exact List.Forall₂.cons (step _ _ (by simp) head)
        (inductionHypothesis (fun a b present related =>
          step a b (List.mem_cons_of_mem _ present) related))

/-- Pointwise equality of shapes over corresponding children gives equality of the erased
child-shape lists.  This is a plain structural induction on the sorted sibling list. -/
theorem shapeList_eq_of_forall₂_shape
    {childrenL childrenR : List (LocalizedCumulativeDecoratedTree input carrierFuel)}
    (h : List.Forall₂ (fun a b => shape a = shape b) childrenL childrenR) :
    shapeList childrenL = shapeList childrenR := by
  induction h with
  | nil => rw [shapeList]
  | cons head tail inductionHypothesis =>
      rw [shapeList, shapeList, head, inductionHypothesis]

/-! ## Shape equality from the correspondence -/

/-- **The recursive correspondence implies equality of the erased constitutional shapes.**  The
proof is a strong induction on the intrinsic height of the left tree; the children of a related
pair are strictly shorter than their parent, and their shapes are compared pointwise by
`shapeList_eq_of_forall₂_shape`. -/
theorem shape_eq_of_realizedTreeMatch {tL tR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (h : RealizedTreeMatch tL tR) : shape tL = shape tR := by
  have main : ∀ n : Nat,
      ∀ tL : LocalizedCumulativeDecoratedTree input carrierFuel, height tL ≤ n →
        ∀ tR : LocalizedCumulativeDecoratedTree input carrierFuel,
          RealizedTreeMatch tL tR → shape tL = shape tR := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro k inductionHypothesis tL _bound tR matched
    cases matched with
    | mk sourceL sourceR atomicL atomicR distL distR massL massR labelL labelR
        childrenL childrenR atomicEq distEq massEq childrenMatch =>
        rw [table_shape_mk sourceL atomicL distL massL labelL childrenL,
          table_shape_mk sourceR atomicR distR massR labelR childrenR]
        simp only [LocalizedCumulativeBranchShape.mk.injEq]
        refine ⟨atomicEq, distEq, massEq, ?_⟩
        apply shapeList_eq_of_forall₂_shape
        exact forall₂_imp_of_mem childrenMatch (fun childL childR present related =>
          inductionHypothesis (height childL) (by
            have smaller := height_lt_height_of_mem
              (⟨sourceL, atomicL, distL, massL, labelL, childrenL⟩ :
                LocalizedCumulativeDecoratedTree input carrierFuel) present
            omega) childL le_rfl childR related)
  exact main (height tL) tL le_rfl tR h

/-! ## The correspondence from shape equality -/

/-- **Shape equality gives the recursive node correspondence.**  The proof is a strong induction
on the intrinsic height of the left tree.  Sphere zero determines the root decoration, and equality
of the erased child-shape lists gives the pointwise sorted-sibling alignment used by the
correspondence; each child is strictly shorter, so the induction hypothesis applies. -/
theorem realizedTreeMatch_of_shape_eq {tL tR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (hshape : shape tL = shape tR) : RealizedTreeMatch tL tR := by
  have main : ∀ n : Nat,
      ∀ tL : LocalizedCumulativeDecoratedTree input carrierFuel, height tL ≤ n →
        ∀ tR : LocalizedCumulativeDecoratedTree input carrierFuel,
          shape tL = shape tR → RealizedTreeMatch tL tR := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro k inductionHypothesis tL _bound tR hshape
    cases tL with
    | mk sourceL atomicL distL massL labelL childrenL =>
      cases tR with
      | mk sourceR atomicR distR massR labelR childrenR =>
        rw [table_shape_mk sourceL atomicL distL massL labelL childrenL,
          table_shape_mk sourceR atomicR distR massR labelR childrenR] at hshape
        have atomicEq : atomicL = atomicR :=
          congrArg LocalizedCumulativeBranchShape.atomicNumber hshape
        have distEq : distL = distR :=
          congrArg LocalizedCumulativeBranchShape.rule1bDistance hshape
        have massEq : massL = massR :=
          congrArg LocalizedCumulativeBranchShape.isotopeMass hshape
        have childrenEq : shapeList childrenL = shapeList childrenR :=
          congrArg LocalizedCumulativeBranchShape.children hshape
        rw [table_shapeList_eq_map, table_shapeList_eq_map] at childrenEq
        have rel := forall₂_of_map_eq shape shape childrenEq
        have relMatch : List.Forall₂
            (RealizedTreeMatch (input := input) (carrierFuel := carrierFuel))
            childrenL childrenR :=
          forall₂_imp_of_mem rel (fun a b present related =>
            inductionHypothesis (height a) (by
              have smaller := height_lt_height_of_mem
                (⟨sourceL, atomicL, distL, massL, labelL, childrenL⟩ :
                  LocalizedCumulativeDecoratedTree input carrierFuel) present
              omega) a le_rfl b related)
        exact RealizedTreeMatch.mk sourceL sourceR atomicL atomicR distL distR massL massR
          labelL labelR childrenL childrenR atomicEq distEq massEq relMatch
  exact main (height tL) tL le_rfl tR hshape

/-- The recursive correspondence is exactly erased-shape equality. -/
theorem realizedTreeMatch_iff_shape_eq
    {tL tR : LocalizedCumulativeDecoratedTree input carrierFuel} :
    RealizedTreeMatch tL tR ↔ shape tL = shape tR :=
  ⟨shape_eq_of_realizedTreeMatch, realizedTreeMatch_of_shape_eq⟩

/-- **The recursive correspondence is symmetric.**  Since the relation is exactly erased-shape
equality, symmetry follows from symmetry of that equality. -/
theorem realizedTreeMatch_symm {tL tR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (h : RealizedTreeMatch tL tR) : RealizedTreeMatch tR tL :=
  realizedTreeMatch_of_shape_eq (shape_eq_of_realizedTreeMatch h).symm

/-- The correspondence is reflexive. -/
theorem realizedTreeMatch_refl (t : LocalizedCumulativeDecoratedTree input carrierFuel) :
    RealizedTreeMatch t t :=
  realizedTreeMatch_of_shape_eq rfl

/-- The correspondence is transitive, because it is exactly erased-shape equality. -/
theorem realizedTreeMatch_trans
    {t₁ t₂ t₃ : LocalizedCumulativeDecoratedTree input carrierFuel}
    (h₁₂ : RealizedTreeMatch t₁ t₂) (h₂₃ : RealizedTreeMatch t₂ t₃) :
    RealizedTreeMatch t₁ t₃ :=
  realizedTreeMatch_of_shape_eq
    ((shape_eq_of_realizedTreeMatch h₁₂).trans (shape_eq_of_realizedTreeMatch h₂₃))

/-! ## Root and child data of a related pair -/

/-- Related nodes carry the same Rule-1a atomic number. -/
theorem realizedTreeMatch_root_atomicNumber_eq
    {tL tR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (h : RealizedTreeMatch tL tR) : tL.atomicNumber = tR.atomicNumber := by
  cases h with
  | mk sourceL sourceR atomicL atomicR distL distR massL massR labelL labelR
      childrenL childrenR atomicEq distEq massEq childrenMatch => exact atomicEq

/-- Related nodes carry the same Rule-1b original-root distance. -/
theorem realizedTreeMatch_root_rule1bDistance_eq
    {tL tR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (h : RealizedTreeMatch tL tR) : tL.rule1bDistance = tR.rule1bDistance := by
  cases h with
  | mk sourceL sourceR atomicL atomicR distL distR massL massR labelL labelR
      childrenL childrenR atomicEq distEq massEq childrenMatch => exact distEq

/-- Related nodes carry the same Rule-2 isotope mass. -/
theorem realizedTreeMatch_root_isotopeMass_eq
    {tL tR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (h : RealizedTreeMatch tL tR) : tL.isotopeMass = tR.isotopeMass := by
  cases h with
  | mk sourceL sourceR atomicL atomicR distL distR massL massR labelL labelR
      childrenL childrenR atomicEq distEq massEq childrenMatch => exact massEq

/-- Related nodes have the same number of sorted children, so the sorted-sibling alignment is
forced by the correspondence rather than supplied. -/
theorem realizedTreeMatch_children_length_eq
    {tL tR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (h : RealizedTreeMatch tL tR) : tL.children.length = tR.children.length := by
  cases h with
  | mk sourceL sourceR atomicL atomicR distL distR massL massR labelL labelR
      childrenL childrenR atomicEq distEq massEq childrenMatch =>
      exact List.Forall₂.length_eq childrenMatch

/-- Each child of the left tree is matched by the child at the same sorted sibling slot of the
right tree, with no alignment hypothesis. -/
theorem realizedTreeMatch_children_getElem?
    {tL tR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (h : RealizedTreeMatch tL tR) {slot : Nat}
    {childL : LocalizedCumulativeDecoratedTree input carrierFuel}
    (present : tL.children[slot]? = some childL) :
    ∃ childR : LocalizedCumulativeDecoratedTree input carrierFuel,
      tR.children[slot]? = some childR ∧ RealizedTreeMatch childL childR := by
  cases h with
  | mk sourceL sourceR atomicL atomicR distL distR massL massR labelL labelR
      childrenL childrenR atomicEq distEq massEq childrenMatch =>
      obtain ⟨hslot, hget⟩ := List.getElem?_eq_some_iff.mp present
      have lengthEq : childrenL.length = childrenR.length :=
        List.Forall₂.length_eq childrenMatch
      have slotRight : slot < childrenR.length := by
        rw [← lengthEq]
        exact hslot
      have pairEq : RealizedTreeMatch (childrenL.get ⟨slot, hslot⟩)
          (childrenR.get ⟨slot, slotRight⟩) := childrenMatch.get hslot slotRight
      have leftEq : childrenL.get ⟨slot, hslot⟩ = childL := by
        simpa only [List.get_eq_getElem] using hget
      refine ⟨childrenR.get ⟨slot, slotRight⟩, ?_, ?_⟩
      · rw [List.getElem?_eq_getElem slotRight]; rfl
      · simpa only [leftEq] using pairEq

/-- Reverse child lookup: each child of the right tree is matched by the child at the same sorted
sibling slot of the left tree. -/
theorem realizedTreeMatch_children_getElem?_symm
    {tL tR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (h : RealizedTreeMatch tL tR) {slot : Nat}
    {childR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (present : tR.children[slot]? = some childR) :
    ∃ childL : LocalizedCumulativeDecoratedTree input carrierFuel,
      tL.children[slot]? = some childL ∧ RealizedTreeMatch childL childR := by
  cases h with
  | mk sourceL sourceR atomicL atomicR distL distR massL massR labelL labelR
      childrenL childrenR atomicEq distEq massEq childrenMatch =>
      obtain ⟨hslotR, hgetR⟩ := List.getElem?_eq_some_iff.mp present
      have lengthEq : childrenL.length = childrenR.length :=
        List.Forall₂.length_eq childrenMatch
      have slotLeft : slot < childrenL.length := by
        rw [lengthEq]
        exact hslotR
      have pairEq : RealizedTreeMatch (childrenL.get ⟨slot, slotLeft⟩)
          (childrenR.get ⟨slot, hslotR⟩) := childrenMatch.get slotLeft hslotR
      have rightEq : childrenR.get ⟨slot, hslotR⟩ = childR := by
        simpa only [List.get_eq_getElem] using hgetR
      refine ⟨childrenL.get ⟨slot, slotLeft⟩, ?_, ?_⟩
      · rw [List.getElem?_eq_getElem slotLeft]; rfl
      · simpa only [rightEq] using pairEq

/-! ## Actual successful builders -/

/-- **Two actual successful cumulative builds with equal constitutional tables produce two
actually realised decorated trees in the recursive node correspondence.**  The trees are obtained
from `exists_decoratedTree_of_buildWithRead`; their shape equality is derived from the actual
three constitutional table equalities through
`table_shape_eq_of_columns_eq`; the recursive correspondence then follows from the shape equality.

All actual provenance is retained: each tree's root source is the actual cursor, each table
matches its actual key, and each tree carries full recursive `LocalizedCumulativeTreeRealizes`
provenance.  No source equality, child alignment, label relation or physical position data is
assumed. -/
theorem exists_matchedTrees_of_buildWithRead
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stageL stageR : LocalizedCumulativeRule45Stage)
    (readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuelL fuelR : Nat)
    (cursorL cursorR : input.LocalizedRerootCursor carrierFuel)
    (keyL keyR : input.LocalizedRerootCumulativeRule45Key)
    (builtL : CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?
      input stageL readL fuelL cursorL = some keyL)
    (builtR : CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?
      input stageR readR fuelR cursorR = some keyR)
    (rule1aEq : keyL.constitutional.rule1a = keyR.constitutional.rule1a)
    (rule1bEq : keyL.constitutional.rule1b = keyR.constitutional.rule1b)
    (rule2Eq : keyL.constitutional.rule2 = keyR.constitutional.rule2) :
    ∃ tL tR : LocalizedCumulativeDecoratedTree input carrierFuel,
      tL.source = cursorL ∧
        tR.source = cursorR ∧
          LocalizedCumulativeTreeTableMatch stageL tL keyL ∧
            LocalizedCumulativeTreeTableMatch stageR tR keyR ∧
              LocalizedCumulativeTreeRealizes input readL tL ∧
                LocalizedCumulativeTreeRealizes input readR tR ∧
                  shape tL = shape tR ∧ RealizedTreeMatch tL tR := by
  obtain ⟨tL, sourceL, matchL, realizesL, _⟩ :=
    exists_decoratedTree_of_buildWithRead input stageL readL fuelL cursorL keyL builtL
  obtain ⟨tR, sourceR, matchR, realizesR, _⟩ :=
    exists_decoratedTree_of_buildWithRead input stageR readR fuelR cursorR keyR builtR
  have columnsRule1a : (tL.tables stageL).rule1a = (tR.tables stageR).rule1a := by
    rw [matchL.1, matchR.1, rule1aEq]
  have columnsRule1b : (tL.tables stageL).rule1b = (tR.tables stageR).rule1b := by
    rw [matchL.2.1, matchR.2.1, rule1bEq]
  have columnsRule2 : (tL.tables stageL).rule2 = (tR.tables stageR).rule2 := by
    rw [matchL.2.2.1, matchR.2.2.1, rule2Eq]
  have shapeEq : shape tL = shape tR :=
    table_shape_eq_of_columns_eq stageL stageR tL tR columnsRule1a columnsRule1b columnsRule2
  exact ⟨tL, tR, sourceL, sourceR, matchL, matchR, realizesL, realizesR, shapeEq,
    realizedTreeMatch_of_shape_eq shapeEq⟩









/-- **Equal erased shape gives equal erased lookup at every raw address.**  A successful left
lookup and a successful right lookup at the same slot path, when they exist, carry equal erased
shapes; both sides succeed or both fail. -/
theorem shape_subtreeAt?_eq
    {tL tR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (hshape : shape tL = shape tR) (addr : List Nat) :
    (subtreeAt? tL addr).map shape = (subtreeAt? tR addr).map shape := by
  induction addr generalizing tL tR with
  | nil => simpa only [subtreeAt?_nil] using congrArg some hshape
  | cons slot rest inductionHypothesis =>
      rw [subtreeAt?_cons, subtreeAt?_cons]
      have matched : RealizedTreeMatch tL tR := realizedTreeMatch_of_shape_eq hshape
      have lengthEq : tL.children.length = tR.children.length :=
        realizedTreeMatch_children_length_eq matched
      cases hL : tL.children[slot]? with
      | none =>
          have hR : tR.children[slot]? = none := by
            rw [List.getElem?_eq_none_iff] at hL ⊢
            omega
          rw [hR]
      | some childL =>
          obtain ⟨childR, hR, childMatch⟩ :=
            realizedTreeMatch_children_getElem? matched hL
          rw [hR]
          simp only [Option.bind_some]
          exact inductionHypothesis (shape_eq_of_realizedTreeMatch childMatch)

/-! ## The equal-shape position equivalence

`shapePositionEquiv` is the identity on raw sibling-slot addresses, restricted to the positions at
which both lookups succeed.  It preserves the root, every raw address, and `PositionAdjacent`
exactly.  Because the erased position node shape is determined by the equal shape, the three
constitutional node columns (Rule-1a atomic number, Rule-1b original-root distance and Rule-2
isotope mass) agree at corresponding positions. -/

/-- **The equal-shape position equivalence.**  The underlying raw address is preserved exactly;
only the success proof is transported across the equal-shape lookup theorem. -/
def shapePositionEquiv
    {tL tR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (hshape : shape tL = shape tR) : Position tL ≃ Position tR where
  toFun p :=
    ⟨p.val, by
      have transported := shape_subtreeAt?_eq hshape p.val
      have leftSome : ((subtreeAt? tL p.val).map shape).isSome = true := by
        simpa only [Option.isSome_map] using p.property
      rw [transported] at leftSome
      simpa only [Option.isSome_map] using leftSome⟩
  invFun q :=
    ⟨q.val, by
      have transported := shape_subtreeAt?_eq hshape.symm q.val
      have rightSome : ((subtreeAt? tR q.val).map shape).isSome = true := by
        simpa only [Option.isSome_map] using q.property
      rw [transported] at rightSome
      simpa only [Option.isSome_map] using rightSome⟩
  left_inv p := Subtype.ext rfl
  right_inv q := Subtype.ext rfl

/-- `shapePositionEquiv` preserves the raw sibling-slot address. -/
@[simp] theorem shapePositionEquiv_val
    {tL tR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (hshape : shape tL = shape tR) (p : Position tL) :
    (shapePositionEquiv hshape p).val = p.val := rfl

/-- `shapePositionEquiv` sends the root position of the left tree to the root position of the
right tree. -/
@[simp] theorem shapePositionEquiv_rootPosition
    {tL tR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (hshape : shape tL = shape tR) :
    shapePositionEquiv hshape (rootPosition tL) = rootPosition tR :=
  Subtype.ext rfl

/-- `shapePositionEquiv` preserves and reflects `PositionAdjacent` exactly, because it preserves
the raw address. -/
theorem shapePositionEquiv_positionAdjacent_iff
    {tL tR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (hshape : shape tL = shape tR) (p q : Position tL) :
    PositionAdjacent (shapePositionEquiv hshape p) (shapePositionEquiv hshape q) ↔
      PositionAdjacent p q := by
  simp only [PositionAdjacent, shapePositionEquiv_val]

/-- The erased shape of the subtree found at a position is transported by
`shapePositionEquiv`. -/
theorem shapePositionEquiv_positionNode_shape_eq
    {tL tR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (hshape : shape tL = shape tR) (p : Position tL) :
    shape (positionNode (shapePositionEquiv hshape p)) = shape (positionNode p) := by
  have leftEq : (subtreeAt? tL p.val).map shape = some (shape (positionNode p)) := by
    rw [positionNode_spec p]
    rfl
  have rightEq : (subtreeAt? tR p.val).map shape =
      some (shape (positionNode (shapePositionEquiv hshape p))) := by
    have hval : (shapePositionEquiv hshape p).val = p.val := rfl
    rw [← hval, positionNode_spec (shapePositionEquiv hshape p)]
    rfl
  have transported := shape_subtreeAt?_eq hshape p.val
  rw [leftEq, rightEq] at transported
  exact (Option.some.inj transported).symm

/-- The Rule-1a projection of the erased shape is the node's atomic number. -/
@[simp] theorem shape_atomicNumber
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    (shape tree).atomicNumber = tree.atomicNumber := by
  cases tree with
  | mk source atomic dist mass label children => rw [table_shape_mk]

/-- The Rule-1b projection of the erased shape is the node's original-root distance. -/
@[simp] theorem shape_rule1bDistance
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    (shape tree).rule1bDistance = tree.rule1bDistance := by
  cases tree with
  | mk source atomic dist mass label children => rw [table_shape_mk]

/-- The Rule-2 projection of the erased shape is the node's isotope mass. -/
@[simp] theorem shape_isotopeMass
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    (shape tree).isotopeMass = tree.isotopeMass := by
  cases tree with
  | mk source atomic dist mass label children => rw [table_shape_mk]

/-- Erasing a child list preserves its length. -/
theorem shapeList_length
    (children : List (LocalizedCumulativeDecoratedTree input carrierFuel)) :
    (shapeList children).length = children.length := by
  rw [table_shapeList_eq_map]
  simp

/-- The erased child list has the node's child count. -/
@[simp] theorem shape_children_length
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    (shape tree).children.length = tree.children.length := by
  cases tree with
  | mk source atomic dist mass label children =>
      rw [table_shape_mk, shapeList_length]

/-- Corresponding positions carry the same number of sorted children. -/
theorem shapePositionEquiv_positionNode_children_length_eq
    {tL tR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (hshape : shape tL = shape tR) (p : Position tL) :
    (positionNode (shapePositionEquiv hshape p)).children.length =
      (positionNode p).children.length := by
  have h := congrArg (fun erased => erased.children.length)
    (shapePositionEquiv_positionNode_shape_eq hshape p)
  simpa only [shape_children_length] using h

/-- Corresponding positions carry the same Rule-1a atomic number. -/
theorem shapePositionEquiv_positionNode_atomicNumber_eq
    {tL tR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (hshape : shape tL = shape tR) (p : Position tL) :
    (positionNode (shapePositionEquiv hshape p)).atomicNumber =
      (positionNode p).atomicNumber := by
  have h := congrArg LocalizedCumulativeBranchShape.atomicNumber
    (shapePositionEquiv_positionNode_shape_eq hshape p)
  simpa only [shape_atomicNumber] using h

/-- Corresponding positions carry the same Rule-1b original-root distance. -/
theorem shapePositionEquiv_positionNode_rule1bDistance_eq
    {tL tR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (hshape : shape tL = shape tR) (p : Position tL) :
    (positionNode (shapePositionEquiv hshape p)).rule1bDistance =
      (positionNode p).rule1bDistance := by
  have h := congrArg LocalizedCumulativeBranchShape.rule1bDistance
    (shapePositionEquiv_positionNode_shape_eq hshape p)
  simpa only [shape_rule1bDistance] using h

/-- Corresponding positions carry the same Rule-2 isotope mass. -/
theorem shapePositionEquiv_positionNode_isotopeMass_eq
    {tL tR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (hshape : shape tL = shape tR) (p : Position tL) :
    (positionNode (shapePositionEquiv hshape p)).isotopeMass =
      (positionNode p).isotopeMass := by
  have h := congrArg LocalizedCumulativeBranchShape.isotopeMass
    (shapePositionEquiv_positionNode_shape_eq hshape p)
  simpa only [shape_isotopeMass] using h





theorem shapePositionEquiv_positionAtom_atomZ_eq
    {singleBonded : input.moleculeGraph.SimpleBonded}
    {acyclic : input.moleculeGraph.Acyclic}
    {readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tL tR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (hshape : shape tL = shape tR)
    (realizesL : LocalizedCumulativeTreeRealizes input readL tL)
    (realizesR : LocalizedCumulativeTreeRealizes input readR tR)
    (p : Position tL) :
    input.moleculeGraph.atomZ
        (positionAtom singleBonded acyclic (shapePositionEquiv hshape p)) =
      input.moleculeGraph.atomZ (positionAtom singleBonded acyclic p) := by
  have nodeEq := shapePositionEquiv_positionNode_atomicNumber_eq hshape p
  have leftEq := positionAtomicNumber_eq_atomZ singleBonded acyclic realizesL p
  have rightEq := positionAtomicNumber_eq_atomZ singleBonded acyclic realizesR
    (shapePositionEquiv hshape p)
  rw [← rightEq, nodeEq, leftEq]

/-- **Corresponding physical position atoms have the same isotope mass.** -/
theorem shapePositionEquiv_positionAtom_atomMass_eq
    {singleBonded : input.moleculeGraph.SimpleBonded}
    {acyclic : input.moleculeGraph.Acyclic}
    {readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tL tR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (hshape : shape tL = shape tR)
    (realizesL : LocalizedCumulativeTreeRealizes input readL tL)
    (realizesR : LocalizedCumulativeTreeRealizes input readR tR)
    (p : Position tL) :
    input.moleculeGraph.atomMass
        (positionAtom singleBonded acyclic (shapePositionEquiv hshape p)) =
      input.moleculeGraph.atomMass (positionAtom singleBonded acyclic p) := by
  have nodeEq := shapePositionEquiv_positionNode_isotopeMass_eq hshape p
  have leftEq := positionIsotopeMass_eq_atomMass singleBonded acyclic realizesL p
  have rightEq := positionIsotopeMass_eq_atomMass singleBonded acyclic realizesR
    (shapePositionEquiv hshape p)
  rw [← rightEq, nodeEq, leftEq]

/-- **Actual builders give the exact address-preserving position correspondence.**  From two
actual successful cumulative builders and equality of the three constitutional tables, construct
the two actual trees, their table matches and recursive realizations, and the equal-shape position
equivalence, and expose the exact correspondence at every raw address, at the root, on the three
constitutional columns and on `PositionAdjacent`.  Every component is the map
`shapePositionEquiv hshape` itself; no arbitrary position bijection is chosen. -/
theorem exists_shapePositionCorrespondence_of_buildWithRead
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stageL stageR : LocalizedCumulativeRule45Stage)
    (readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuelL fuelR : Nat)
    (cursorL cursorR : input.LocalizedRerootCursor carrierFuel)
    (keyL keyR : input.LocalizedRerootCumulativeRule45Key)
    (builtL : CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?
      input stageL readL fuelL cursorL = some keyL)
    (builtR : CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?
      input stageR readR fuelR cursorR = some keyR)
    (rule1aEq : keyL.constitutional.rule1a = keyR.constitutional.rule1a)
    (rule1bEq : keyL.constitutional.rule1b = keyR.constitutional.rule1b)
    (rule2Eq : keyL.constitutional.rule2 = keyR.constitutional.rule2) :
    ∃ (tL tR : LocalizedCumulativeDecoratedTree input carrierFuel)
      (hshape : shape tL = shape tR),
      tL.source = cursorL ∧
        tR.source = cursorR ∧
          LocalizedCumulativeTreeTableMatch stageL tL keyL ∧
            LocalizedCumulativeTreeTableMatch stageR tR keyR ∧
              LocalizedCumulativeTreeRealizes input readL tL ∧
                LocalizedCumulativeTreeRealizes input readR tR ∧
                  shapePositionEquiv hshape (rootPosition tL) = rootPosition tR ∧
                    (∀ addr : List Nat,
                      (subtreeAt? tL addr).map shape = (subtreeAt? tR addr).map shape) ∧
                      (∀ p : Position tL,
                        (positionNode (shapePositionEquiv hshape p)).atomicNumber =
                            (positionNode p).atomicNumber ∧
                          (positionNode (shapePositionEquiv hshape p)).rule1bDistance =
                            (positionNode p).rule1bDistance ∧
                          (positionNode (shapePositionEquiv hshape p)).isotopeMass =
                            (positionNode p).isotopeMass) ∧
                        (∀ p q : Position tL,
                          PositionAdjacent (shapePositionEquiv hshape p)
                              (shapePositionEquiv hshape q) ↔
                            PositionAdjacent p q) := by
  obtain ⟨tL, tR, sourceL, sourceR, matchL, matchR, realizesL, realizesR, hshape, _match⟩ :=
    exists_matchedTrees_of_buildWithRead input stageL stageR readL readR fuelL fuelR
      cursorL cursorR keyL keyR builtL builtR rule1aEq rule1bEq rule2Eq
  exact ⟨tL, tR, hshape, sourceL, sourceR, matchL, matchR, realizesL, realizesR,
    shapePositionEquiv_rootPosition hshape,
    fun addr => shape_subtreeAt?_eq hshape addr,
    fun p =>
      ⟨shapePositionEquiv_positionNode_atomicNumber_eq hshape p,
        shapePositionEquiv_positionNode_rule1bDistance_eq hshape p,
        shapePositionEquiv_positionNode_isotopeMass_eq hshape p⟩,
    fun p q => shapePositionEquiv_positionAdjacent_iff hshape p q⟩












section RootedCutBranchIsoPackaging

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {m : MoleculeGraph V} {c u v : V}

/-- **Package a rooted cut-branch isomorphism from an exact position equivalence.**  The input
equivalences identify a left and a right position type with the two cut branches.  The position
equivalence `e` is required to fix the attachment points (`e rootL = rootR`), to preserve the node
atomic number and mass at every position, and to reflect physical adjacency exactly.  The output is
the `RootedCutBranchIso` whose underlying equivalence is
`EL.symm.trans (e.trans ER)`, i.e. the physical map induced by the *same* position map `e`. -/
noncomputable def rootedCutBranchIso_of_positionEquiv
    (hcu : m.Adj c u) (hcv : m.Adj c v)
    {PosL PosR : Type*}
    (EL : PosL ≃ CutBranch m c u) (ER : PosR ≃ CutBranch m c v)
    (e : PosL ≃ PosR)
    (rootL : PosL) (rootR : PosR)
    (eRoot : e rootL = rootR)
    (ELRoot : EL rootL = ⟨u, cutBranch_mem_self m hcu⟩)
    (ERoot : ER rootR = ⟨v, cutBranch_mem_self m hcv⟩)
    (atomZ : ∀ p : PosL,
      m.atomZ ((ER (e p) : CutBranch m c v) : V) =
        m.atomZ ((EL p : CutBranch m c u) : V))
    (atomMass : ∀ p : PosL,
      m.atomMass ((ER (e p) : CutBranch m c v) : V) =
        m.atomMass ((EL p : CutBranch m c u) : V))
    (adj : ∀ p q : PosL,
      m.Adj ((ER (e p) : CutBranch m c v) : V) ((ER (e q) : CutBranch m c v) : V) ↔
        m.Adj ((EL p : CutBranch m c u) : V) ((EL q : CutBranch m c u) : V)) :
    RootedCutBranchIso m c u v where
  toEquiv := EL.symm.trans (e.trans ER)
  map_attach := by
    intro hu hv
    apply Subtype.ext
    have hEL : EL rootL = (⟨u, hu⟩ : CutBranch m c u) := by
      rw [ELRoot]
    have hsymm : EL.symm (⟨u, hu⟩ : CutBranch m c u) = rootL := by
      rw [← hEL, Equiv.symm_apply_apply]
    change ((ER (e (EL.symm (⟨u, hu⟩ : CutBranch m c u))) :
      CutBranch m c v) : V) = ((⟨v, hv⟩ : CutBranch m c v) : V)
    rw [hsymm, eRoot, ERoot]
  atomZ_eq := by
    intro x
    change m.atomZ ((ER (e (EL.symm x)) : CutBranch m c v) : V) = m.atomZ (x : V)
    rw [atomZ (EL.symm x), Equiv.apply_symm_apply]
  atomMass_eq := by
    intro x
    change m.atomMass ((ER (e (EL.symm x)) : CutBranch m c v) : V) =
      m.atomMass (x : V)
    rw [atomMass (EL.symm x), Equiv.apply_symm_apply]
  adj_iff := by
    intro x y
    change m.Adj ((ER (e (EL.symm x)) : CutBranch m c v) : V)
        ((ER (e (EL.symm y)) : CutBranch m c v) : V) ↔
      m.Adj (x : V) (y : V)
    rw [adj (EL.symm x) (EL.symm y), Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- **The packaged isomorphism uses the exact position map.**  On the left branch point `EL p`
the packaged `RootedCutBranchIso` is exactly `ER (e p)`; no arbitrary choice of isomorphism is
made anywhere in the construction. -/
theorem rootedCutBranchIso_of_positionEquiv_toEquiv_apply
    (hcu : m.Adj c u) (hcv : m.Adj c v)
    {PosL PosR : Type*}
    (EL : PosL ≃ CutBranch m c u) (ER : PosR ≃ CutBranch m c v)
    (e : PosL ≃ PosR)
    (rootL : PosL) (rootR : PosR)
    (eRoot : e rootL = rootR)
    (ELRoot : EL rootL = ⟨u, cutBranch_mem_self m hcu⟩)
    (ERoot : ER rootR = ⟨v, cutBranch_mem_self m hcv⟩)
    (atomZ : ∀ p : PosL,
      m.atomZ ((ER (e p) : CutBranch m c v) : V) =
        m.atomZ ((EL p : CutBranch m c u) : V))
    (atomMass : ∀ p : PosL,
      m.atomMass ((ER (e p) : CutBranch m c v) : V) =
        m.atomMass ((EL p : CutBranch m c u) : V))
    (adj : ∀ p q : PosL,
      m.Adj ((ER (e p) : CutBranch m c v) : V) ((ER (e q) : CutBranch m c v) : V) ↔
        m.Adj ((EL p : CutBranch m c u) : V) ((EL q : CutBranch m c u) : V))
    (p : PosL) :
    ((rootedCutBranchIso_of_positionEquiv hcu hcv EL ER e rootL rootR eRoot ELRoot ERoot
      atomZ atomMass adj).toEquiv (EL p) : CutBranch m c v) = ER (e p) := by
  apply Subtype.ext
  change ((ER (e (EL.symm (EL p))) : CutBranch m c v) : V) = ((ER (e p) : CutBranch m c v) : V)
  rw [Equiv.symm_apply_apply]

/-- **The global cut-branch swap uses the same position map on the left branch.**  For every left
position `p`, the automorphism built by `cutBranchSwapAut` from the packaged rooted isomorphism
sends the physical atom of `EL p` to the physical atom of `ER (e p)`.  This retains the decoded
label pairing at the individual branch occurrence rather than only an existential branch-level
isomorphism. -/
theorem cutBranchSwapAut_apply_positionEquiv
    (hcu : m.Adj c u) (hcv : m.Adj c v)
    {PosL PosR : Type*}
    (EL : PosL ≃ CutBranch m c u) (ER : PosR ≃ CutBranch m c v)
    (e : PosL ≃ PosR)
    (rootL : PosL) (rootR : PosR)
    (eRoot : e rootL = rootR)
    (ELRoot : EL rootL = ⟨u, cutBranch_mem_self m hcu⟩)
    (ERoot : ER rootR = ⟨v, cutBranch_mem_self m hcv⟩)
    (atomZ : ∀ p : PosL,
      m.atomZ ((ER (e p) : CutBranch m c v) : V) =
        m.atomZ ((EL p : CutBranch m c u) : V))
    (atomMass : ∀ p : PosL,
      m.atomMass ((ER (e p) : CutBranch m c v) : V) =
        m.atomMass ((EL p : CutBranch m c u) : V))
    (adj : ∀ p q : PosL,
      m.Adj ((ER (e p) : CutBranch m c v) : V) ((ER (e q) : CutBranch m c v) : V) ↔
        m.Adj ((EL p : CutBranch m c u) : V) ((EL q : CutBranch m c u) : V))
    (hacyc : m.Acyclic) (huv : u ≠ v) (hsimple : m.SimpleBonded)
    (hcharge : ConstantFormalCharge m) (p : PosL) :
    ((cutBranchSwapAut m c u v hacyc hcu hcv huv hsimple hcharge
        (rootedCutBranchIso_of_positionEquiv hcu hcv EL ER e rootL rootR eRoot ELRoot ERoot
          atomZ atomMass adj) : Equiv.Perm V)
      ((EL p : CutBranch m c u) : V)) =
      ((ER (e p) : CutBranch m c v) : V) := by
  have hφ := rootedCutBranchIso_of_positionEquiv_toEquiv_apply hcu hcv EL ER e rootL rootR
    eRoot ELRoot ERoot atomZ atomMass adj p
  have hx : ((EL p : CutBranch m c u) : V) ∈ CutBranch m c u := (EL p).2
  rw [cutBranchSwapAut_apply, cutBranchSwap_apply,
    cutBranchSwapFun_of_mem_left m c u v
      (rootedCutBranchIso_of_positionEquiv hcu hcv EL ER e rootL rootR eRoot ELRoot ERoot
        atomZ atomMass adj) hx]
  simpa using congrArg Subtype.val hφ

end RootedCutBranchIsoPackaging










section ConcreteActualCutIso

variable {singleBonded : input.moleculeGraph.SimpleBonded}
variable {acyclic : input.moleculeGraph.Acyclic}
variable {enough : input.certified.input.molecule.atomCount ≤ carrierFuel}
variable {readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
variable {tL tR : LocalizedCumulativeDecoratedTree input carrierFuel}
variable {c u v : input.Atom}
variable {previousL previousR : input.LocalizedCIPOccurrence carrierFuel}






noncomputable def rootedCutBranchIso_of_shapeMatch
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (hshape : shape tL = shape tR)
    (realizesL : LocalizedCumulativeTreeRealizes input readL tL)
    (realizesR : LocalizedCumulativeTreeRealizes input readR tR)
    (previousEqL : tL.source.previous? = some previousL)
    (validL : input.LocalizedRerootCursorValid tL.source)
    (sameRootL : tL.source.occurrence.1.root = previousL.1.root)
    (previousEqR : tR.source.previous? = some previousR)
    (validR : input.LocalizedRerootCursorValid tR.source)
    (sameRootR : tR.source.occurrence.1.root = previousR.1.root)
    (oObservedL : tL.source.occurrence.1.node.current? = some u)
    (pObservedL : previousL.1.node.current? = some c)
    (oObservedR : tR.source.occurrence.1.node.current? = some v)
    (pObservedR : previousR.1.node.current? = some c)
    (hcu : input.moleculeGraph.Adj c u)
    (hcv : input.moleculeGraph.Adj c v) :
    RootedCutBranchIso input.moleculeGraph c u v :=
  rootedCutBranchIso_of_positionEquiv hcu hcv
    (positionCutEquiv singleBonded acyclic enough realizesL previousL previousEqL validL
      sameRootL oObservedL pObservedL hcu)
    (positionCutEquiv singleBonded acyclic enough realizesR previousR previousEqR validR
      sameRootR oObservedR pObservedR hcv)
    (shapePositionEquiv hshape)
    (rootPosition tL) (rootPosition tR)
    (shapePositionEquiv_rootPosition hshape)
    (positionCutEquiv_rootPosition singleBonded acyclic enough realizesL previousL previousEqL
      validL sameRootL oObservedL pObservedL hcu)
    (positionCutEquiv_rootPosition singleBonded acyclic enough realizesR previousR previousEqR
      validR sameRootR oObservedR pObservedR hcv)
    (fun p => by
      rw [positionCutEquiv_apply_coe, positionCutEquiv_apply_coe]
      exact shapePositionEquiv_positionAtom_atomZ_eq hshape realizesL realizesR p)
    (fun p => by
      rw [positionCutEquiv_apply_coe, positionCutEquiv_apply_coe]
      exact shapePositionEquiv_positionAtom_atomMass_eq hshape realizesL realizesR p)
    (fun p q => by
      rw [positionCutEquiv_apply_coe, positionCutEquiv_apply_coe,
        positionCutEquiv_apply_coe, positionCutEquiv_apply_coe]
      rw [positionAtom_adjacent_iff_positionAdjacent singleBonded acyclic enough realizesR
          previousR previousEqR sameRootR validR oObservedR pObservedR hcv
          (shapePositionEquiv hshape p) (shapePositionEquiv hshape q),
        positionAtom_adjacent_iff_positionAdjacent singleBonded acyclic enough realizesL
          previousL previousEqL sameRootL validL oObservedL pObservedL hcu p q]
      exact shapePositionEquiv_positionAdjacent_iff hshape p q)

/-- **The concrete isomorphism sends each left position to the exactly matching right position.**
For every left position `p`, the physical cut-branch point `E_L p` is mapped to `E_R (e p)`, and
therefore its actual source atom is exactly the source atom at the matching right position. -/
theorem rootedCutBranchIso_of_shapeMatch_toEquiv_apply
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (hshape : shape tL = shape tR)
    (realizesL : LocalizedCumulativeTreeRealizes input readL tL)
    (realizesR : LocalizedCumulativeTreeRealizes input readR tR)
    (previousEqL : tL.source.previous? = some previousL)
    (validL : input.LocalizedRerootCursorValid tL.source)
    (sameRootL : tL.source.occurrence.1.root = previousL.1.root)
    (previousEqR : tR.source.previous? = some previousR)
    (validR : input.LocalizedRerootCursorValid tR.source)
    (sameRootR : tR.source.occurrence.1.root = previousR.1.root)
    (oObservedL : tL.source.occurrence.1.node.current? = some u)
    (pObservedL : previousL.1.node.current? = some c)
    (oObservedR : tR.source.occurrence.1.node.current? = some v)
    (pObservedR : previousR.1.node.current? = some c)
    (hcu : input.moleculeGraph.Adj c u)
    (hcv : input.moleculeGraph.Adj c v)
    (p : Position tL) :
    (((rootedCutBranchIso_of_shapeMatch (singleBonded := singleBonded) (acyclic := acyclic)
        enough hshape realizesL realizesR previousEqL validL sameRootL
        previousEqR validR sameRootR oObservedL pObservedL oObservedR pObservedR hcu hcv).toEquiv
        (positionCutEquiv singleBonded acyclic enough realizesL previousL previousEqL validL
          sameRootL oObservedL pObservedL hcu p) : CutBranch input.moleculeGraph c v) :
        input.Atom) =
      positionAtom singleBonded acyclic (shapePositionEquiv hshape p) := by
  have h := congrArg Subtype.val
    (rootedCutBranchIso_of_positionEquiv_toEquiv_apply hcu hcv
      (positionCutEquiv singleBonded acyclic enough realizesL previousL previousEqL validL
        sameRootL oObservedL pObservedL hcu)
      (positionCutEquiv singleBonded acyclic enough realizesR previousR previousEqR validR
        sameRootR oObservedR pObservedR hcv)
      (shapePositionEquiv hshape) (rootPosition tL) (rootPosition tR)
      (shapePositionEquiv_rootPosition hshape)
      (positionCutEquiv_rootPosition singleBonded acyclic enough realizesL previousL previousEqL
        validL sameRootL oObservedL pObservedL hcu)
      (positionCutEquiv_rootPosition singleBonded acyclic enough realizesR previousR previousEqR
        validR sameRootR oObservedR pObservedR hcv)
      (fun p => by
        rw [positionCutEquiv_apply_coe, positionCutEquiv_apply_coe]
        exact shapePositionEquiv_positionAtom_atomZ_eq hshape realizesL realizesR p)
      (fun p => by
        rw [positionCutEquiv_apply_coe, positionCutEquiv_apply_coe]
        exact shapePositionEquiv_positionAtom_atomMass_eq hshape realizesL realizesR p)
      (fun p q => by
        rw [positionCutEquiv_apply_coe, positionCutEquiv_apply_coe,
          positionCutEquiv_apply_coe, positionCutEquiv_apply_coe]
        rw [positionAtom_adjacent_iff_positionAdjacent singleBonded acyclic enough realizesR
            previousR previousEqR sameRootR validR oObservedR pObservedR hcv
            (shapePositionEquiv hshape p) (shapePositionEquiv hshape q),
          positionAtom_adjacent_iff_positionAdjacent singleBonded acyclic enough realizesL
            previousL previousEqL sameRootL validL oObservedL pObservedL hcu p q]
        exact shapePositionEquiv_positionAdjacent_iff hshape p q)
      p)
  simpa [rootedCutBranchIso_of_shapeMatch, positionCutEquiv_apply_coe] using h

/-- **The global cut-branch swap retains the exact position-to-atom pairing.**  On the actual left
source atom at position `p`, the global automorphism built from the constructed cut iso acts as
the identity on positions: it sends that atom to the actual right source atom at
`shapePositionEquiv hshape p`.  `ConstantFormalCharge` is used only here, for the global
automorphism extension, never for the cut-branch isomorphism itself. -/
theorem rootedCutBranchIso_of_shapeMatch_swap_apply
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (hshape : shape tL = shape tR)
    (realizesL : LocalizedCumulativeTreeRealizes input readL tL)
    (realizesR : LocalizedCumulativeTreeRealizes input readR tR)
    (previousEqL : tL.source.previous? = some previousL)
    (validL : input.LocalizedRerootCursorValid tL.source)
    (sameRootL : tL.source.occurrence.1.root = previousL.1.root)
    (previousEqR : tR.source.previous? = some previousR)
    (validR : input.LocalizedRerootCursorValid tR.source)
    (sameRootR : tR.source.occurrence.1.root = previousR.1.root)
    (oObservedL : tL.source.occurrence.1.node.current? = some u)
    (pObservedL : previousL.1.node.current? = some c)
    (oObservedR : tR.source.occurrence.1.node.current? = some v)
    (pObservedR : previousR.1.node.current? = some c)
    (hcu : input.moleculeGraph.Adj c u)
    (hcv : input.moleculeGraph.Adj c v)
    (hacyc : input.moleculeGraph.Acyclic)
    (huv : u ≠ v)
    (hsimple : input.moleculeGraph.SimpleBonded)
    (hcharge : ConstantFormalCharge input.moleculeGraph)
    (p : Position tL) :
    ((cutBranchSwapAut input.moleculeGraph c u v hacyc hcu hcv huv hsimple hcharge
        (rootedCutBranchIso_of_shapeMatch (singleBonded := singleBonded) (acyclic := acyclic)
          enough hshape realizesL realizesR previousEqL validL sameRootL
          previousEqR validR sameRootR oObservedL pObservedL oObservedR pObservedR hcu hcv) :
        Equiv.Perm input.Atom)
      (positionAtom singleBonded acyclic p)) =
      positionAtom singleBonded acyclic (shapePositionEquiv hshape p) := by
  rw [← positionCutEquiv_apply_coe singleBonded acyclic enough realizesL previousL previousEqL
    validL sameRootL oObservedL pObservedL hcu p]
  have h := cutBranchSwapAut_apply_positionEquiv hcu hcv
    (positionCutEquiv singleBonded acyclic enough realizesL previousL previousEqL validL
      sameRootL oObservedL pObservedL hcu)
    (positionCutEquiv singleBonded acyclic enough realizesR previousR previousEqR validR
      sameRootR oObservedR pObservedR hcv)
    (shapePositionEquiv hshape) (rootPosition tL) (rootPosition tR)
    (shapePositionEquiv_rootPosition hshape)
    (positionCutEquiv_rootPosition singleBonded acyclic enough realizesL previousL previousEqL
      validL sameRootL oObservedL pObservedL hcu)
    (positionCutEquiv_rootPosition singleBonded acyclic enough realizesR previousR previousEqR
      validR sameRootR oObservedR pObservedR hcv)
    (fun p => by
      rw [positionCutEquiv_apply_coe, positionCutEquiv_apply_coe]
      exact shapePositionEquiv_positionAtom_atomZ_eq hshape realizesL realizesR p)
    (fun p => by
      rw [positionCutEquiv_apply_coe, positionCutEquiv_apply_coe]
      exact shapePositionEquiv_positionAtom_atomMass_eq hshape realizesL realizesR p)
    (fun p q => by
      rw [positionCutEquiv_apply_coe, positionCutEquiv_apply_coe,
        positionCutEquiv_apply_coe, positionCutEquiv_apply_coe]
      rw [positionAtom_adjacent_iff_positionAdjacent singleBonded acyclic enough realizesR
          previousR previousEqR sameRootR validR oObservedR pObservedR hcv
          (shapePositionEquiv hshape p) (shapePositionEquiv hshape q),
        positionAtom_adjacent_iff_positionAdjacent singleBonded acyclic enough realizesL
          previousL previousEqL sameRootL validL oObservedL pObservedL hcu p q]
      exact shapePositionEquiv_positionAdjacent_iff hshape p q)
    hacyc huv hsimple hcharge p
  simpa [rootedCutBranchIso_of_shapeMatch, positionCutEquiv_apply_coe] using h

end ConcreteActualCutIso

/-! ## The final corollary from actual successful cumulative builders

This composes the actual-builder endpoint with the concrete physical isomorphism.  The hypotheses on
the two actual cursors (`previousEq`, `valid`, `sameRoot`, the observed current atoms and the two
incoming edges) are exactly the physical incoming-cursor data of the cut; they are not a desired
isomorphism, a physical bijection, key transport or label covariance.  The conclusion names the
exact constructed isomorphism and states the atom-level action of its global swap extension, so the
downstream label consumers receive the actual position-to-current pairing rather than an arbitrary
existential isomorphism. -/

theorem exists_rootedCutBranchIso_of_buildWithRead
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stageL stageR : LocalizedCumulativeRule45Stage)
    (readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuelL fuelR : Nat)
    (cursorL cursorR : input.LocalizedRerootCursor carrierFuel)
    (keyL keyR : input.LocalizedRerootCumulativeRule45Key)
    (builtL : CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?
      input stageL readL fuelL cursorL = some keyL)
    (builtR : CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?
      input stageR readR fuelR cursorR = some keyR)
    (rule1aEq : keyL.constitutional.rule1a = keyR.constitutional.rule1a)
    (rule1bEq : keyL.constitutional.rule1b = keyR.constitutional.rule1b)
    (rule2Eq : keyL.constitutional.rule2 = keyR.constitutional.rule2)
    {singleBonded : input.moleculeGraph.SimpleBonded}
    {acyclic : input.moleculeGraph.Acyclic}
    {enough : input.certified.input.molecule.atomCount ≤ carrierFuel}
    {c u v : input.Atom}
    {previousL previousR : input.LocalizedCIPOccurrence carrierFuel}
    (previousEqL : cursorL.previous? = some previousL)
    (validL : input.LocalizedRerootCursorValid cursorL)
    (sameRootL : cursorL.occurrence.1.root = previousL.1.root)
    (previousEqR : cursorR.previous? = some previousR)
    (validR : input.LocalizedRerootCursorValid cursorR)
    (sameRootR : cursorR.occurrence.1.root = previousR.1.root)
    (oObservedL : cursorL.occurrence.1.node.current? = some u)
    (pObservedL : previousL.1.node.current? = some c)
    (oObservedR : cursorR.occurrence.1.node.current? = some v)
    (pObservedR : previousR.1.node.current? = some c)
    (hcu : input.moleculeGraph.Adj c u)
    (hcv : input.moleculeGraph.Adj c v)
    (hacyc : input.moleculeGraph.Acyclic)
    (huv : u ≠ v)
    (hsimple : input.moleculeGraph.SimpleBonded)
    (hcharge : ConstantFormalCharge input.moleculeGraph) :
    ∃ (tL tR : LocalizedCumulativeDecoratedTree input carrierFuel)
      (hshape : shape tL = shape tR)
      (sourceL : tL.source = cursorL) (sourceR : tR.source = cursorR)
      (_matchL : LocalizedCumulativeTreeTableMatch stageL tL keyL)
      (_matchR : LocalizedCumulativeTreeTableMatch stageR tR keyR)
      (realizesL : LocalizedCumulativeTreeRealizes input readL tL)
      (realizesR : LocalizedCumulativeTreeRealizes input readR tR),
      ∀ p : Position tL,
        ((cutBranchSwapAut input.moleculeGraph c u v hacyc hcu hcv huv hsimple hcharge
            (rootedCutBranchIso_of_shapeMatch (singleBonded := singleBonded)
              (acyclic := acyclic) enough hshape realizesL realizesR
              (sourceL ▸ previousEqL) (sourceL ▸ validL) (sourceL ▸ sameRootL)
              (sourceR ▸ previousEqR) (sourceR ▸ validR) (sourceR ▸ sameRootR)
              (sourceL ▸ oObservedL) pObservedL (sourceR ▸ oObservedR) pObservedR
              hcu hcv) : Equiv.Perm input.Atom)
          (positionAtom singleBonded acyclic p)) =
          positionAtom singleBonded acyclic (shapePositionEquiv hshape p) := by
  obtain ⟨tL, tR, sourceL, sourceR, matchL, matchR, realizesL, realizesR, hshape, _match⟩ :=
    exists_matchedTrees_of_buildWithRead input stageL stageR readL readR fuelL fuelR
      cursorL cursorR keyL keyR builtL builtR rule1aEq rule1bEq rule2Eq
  refine ⟨tL, tR, hshape, sourceL, sourceR, matchL, matchR, realizesL, realizesR, ?_⟩
  intro p
  exact rootedCutBranchIso_of_shapeMatch_swap_apply
    (singleBonded := singleBonded) (acyclic := acyclic) enough hshape realizesL realizesR
    (sourceL ▸ previousEqL) (sourceL ▸ validL) (sourceL ▸ sameRootL)
    (sourceR ▸ previousEqR) (sourceR ▸ validR) (sourceR ▸ sameRootR)
    (sourceL ▸ oObservedL) pObservedL (sourceR ▸ oObservedR) pObservedR
    hcu hcv hacyc huv hsimple hcharge p

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.RealizedTreeMatch
assert_kernel_only TetraStereo.OneCenter.forall₂_of_map_eq
assert_kernel_only TetraStereo.OneCenter.forall₂_imp_of_mem
assert_kernel_only TetraStereo.OneCenter.shapeList_eq_of_forall₂_shape
assert_kernel_only TetraStereo.OneCenter.shape_eq_of_realizedTreeMatch
assert_kernel_only TetraStereo.OneCenter.realizedTreeMatch_of_shape_eq
assert_kernel_only TetraStereo.OneCenter.realizedTreeMatch_iff_shape_eq
assert_kernel_only TetraStereo.OneCenter.realizedTreeMatch_symm
assert_kernel_only TetraStereo.OneCenter.realizedTreeMatch_refl
assert_kernel_only TetraStereo.OneCenter.realizedTreeMatch_trans
assert_kernel_only TetraStereo.OneCenter.realizedTreeMatch_root_atomicNumber_eq
assert_kernel_only TetraStereo.OneCenter.realizedTreeMatch_root_rule1bDistance_eq
assert_kernel_only TetraStereo.OneCenter.realizedTreeMatch_root_isotopeMass_eq
assert_kernel_only TetraStereo.OneCenter.realizedTreeMatch_children_length_eq
assert_kernel_only TetraStereo.OneCenter.realizedTreeMatch_children_getElem?
assert_kernel_only TetraStereo.OneCenter.realizedTreeMatch_children_getElem?_symm
assert_kernel_only TetraStereo.OneCenter.exists_matchedTrees_of_buildWithRead
assert_kernel_only TetraStereo.OneCenter.shape_subtreeAt?_eq
assert_kernel_only TetraStereo.OneCenter.shapePositionEquiv
assert_kernel_only TetraStereo.OneCenter.shapePositionEquiv_val
assert_kernel_only TetraStereo.OneCenter.shapePositionEquiv_rootPosition
assert_kernel_only TetraStereo.OneCenter.shapePositionEquiv_positionAdjacent_iff
assert_kernel_only TetraStereo.OneCenter.shapePositionEquiv_positionNode_shape_eq
assert_kernel_only TetraStereo.OneCenter.shape_atomicNumber
assert_kernel_only TetraStereo.OneCenter.shape_rule1bDistance
assert_kernel_only TetraStereo.OneCenter.shape_isotopeMass
assert_kernel_only TetraStereo.OneCenter.shapeList_length
assert_kernel_only TetraStereo.OneCenter.shape_children_length
assert_kernel_only TetraStereo.OneCenter.shapePositionEquiv_positionNode_children_length_eq
assert_kernel_only TetraStereo.OneCenter.shapePositionEquiv_positionNode_atomicNumber_eq
assert_kernel_only TetraStereo.OneCenter.shapePositionEquiv_positionNode_rule1bDistance_eq
assert_kernel_only TetraStereo.OneCenter.shapePositionEquiv_positionNode_isotopeMass_eq
assert_kernel_only TetraStereo.OneCenter.shapePositionEquiv_positionAtom_atomZ_eq
assert_kernel_only TetraStereo.OneCenter.shapePositionEquiv_positionAtom_atomMass_eq
assert_kernel_only TetraStereo.OneCenter.exists_shapePositionCorrespondence_of_buildWithRead
assert_kernel_only TetraStereo.OneCenter.rootedCutBranchIso_of_positionEquiv
assert_kernel_only TetraStereo.OneCenter.rootedCutBranchIso_of_positionEquiv_toEquiv_apply
assert_kernel_only TetraStereo.OneCenter.cutBranchSwapAut_apply_positionEquiv
assert_kernel_only TetraStereo.OneCenter.rootedCutBranchIso_of_shapeMatch
assert_kernel_only TetraStereo.OneCenter.rootedCutBranchIso_of_shapeMatch_toEquiv_apply
assert_kernel_only TetraStereo.OneCenter.rootedCutBranchIso_of_shapeMatch_swap_apply
assert_kernel_only TetraStereo.OneCenter.exists_rootedCutBranchIso_of_buildWithRead
