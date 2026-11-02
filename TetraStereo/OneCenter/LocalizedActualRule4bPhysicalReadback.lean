import TetraStereo.OneCenter.LocalizedActualRule4bKeyBridge
import TetraStereo.OneCenter.LocalizedActualArmReadback
import TetraStereo.OneCenter.LocalizedActualSiblingSortRefinement
import TetraStereo.KernelOnly

set_option autoImplicit false





























namespace TetraStereo.OneCenter
namespace Rule4aTableBridge

open LocalizedCumulativeDecoratedTree
open CertifiedLocalizedCIPInput
open CertifiedLocalizedCIPInput.OriginalRootArm
open DeclarativeCIP
open SameStageKindComparison
open ActualSiblingSortRefinement

noncomputable section
open scoped Classical

/-! ## Rule-4a scalars of aligned descriptor tables -/

theorem map_eq_map_of_forall₂ {α β γ : Type*} {R : α → β → Prop} {f : α → γ} {g : β → γ}
    {l₁ : List α} {l₂ : List β} (h : List.Forall₂ R l₁ l₂) (hf : ∀ a b, R a b → f a = g b) :
    l₁.map f = l₂.map g := by
  induction h with
  | nil => rfl
  | cons hab _ ih => simp [List.map_cons, hf _ _ hab, ih]

theorem headD_eq_getD_zero (l : List Nat) : l.headD 0 = l.getD 0 0 := by
  cases l <;> rfl

/-- Descriptor tables aligned at stage `.rule4b ρ` (controlling component `1`) have equal Rule-4a
scalar tables (component `0`). -/
theorem scalar4a_eq_of_tableAligned {input : CertifiedLocalizedCIPInput} {ρ : RS}
    {keyL keyR : input.LocalizedRerootCumulativeRule45Key}
    (aligned : TableAligned (.rule4b ρ) keyL.descriptor keyR.descriptor) :
    scalar4a keyL = scalar4a keyR := by
  unfold scalar4a
  refine map_eq_map_of_forall₂ aligned fun rowL rowR hrow => ?_
  refine map_eq_map_of_forall₂ hrow fun eL eR he => ?_
  show (eL.1, eL.2.headD 0) = (eR.1, eR.2.headD 0)
  rw [he.addressEq, headD_eq_getD_zero, headD_eq_getD_zero,
    he.before 0 (show 0 < controllingComponent (.rule4b ρ) from Nat.zero_lt_one)]

/-! ## The sibling-kind clause from the physical sibling theorem -/

section Physical

variable {input : LocalizedUniversalReference.Input} (setup : ActualSlotPhysicalSetup input)
  {center : input.certified.TetrahedralCenter} {index : Fin 4} {ρ : RS}

/-- **Sibling-kind agreement on the physical domain.**  For an arm realized under the production
dependency reader whose root is reachable from the slot tree, two constitutionally tied distinct
children of any node, built at their own sources, have equal Rule-4a kind tables. -/
theorem siblingKind_of_setup
    {read : input.certified.LocalizedRerootCursor
      (input.certified.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel}
    (hread : read = ActualReaderPhysicalBranchInverse.dependencyReader input setup.c)
    (arm : input.certified.OriginalRootArm center index (.rule4b ρ) read)
    (reachable : input.certified.ActualChildReachable setup.tree.source arm.tree.source)
    (node : (armGraph arm).Node)
    (dsub : LocalizedCumulativeDecoratedTree input.certified
      (input.certified.certified.input.molecule.atomCount + 1))
    (lookup : arm.tree.decoratedSubtreeAt? node.1 = some dsub)
    (i j : Nat) (hi : i < dsub.children.length) (hj : j < dsub.children.length) (hij : i ≠ j)
    (fuelI fuelJ : Nat) (keyI keyJ : input.certified.LocalizedRerootCumulativeRule45Key)
    (builtI : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? (.rule4b ρ) read
      fuelI (dsub.children[i]'hi).source = some keyI)
    (builtJ : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? (.rule4b ρ) read
      fuelJ (dsub.children[j]'hj).source = some keyJ)
    (tie : OfficialRuleMajorKey.compare keyI.constitutional keyJ.constitutional = Ordering.eq) :
    scalar4a keyI = scalar4a keyJ := by
  subst hread
  have hpos : (subtreeAt? arm.tree node.1).isSome = true := by
    rw [← decoratedSubtreeAt?_eq_subtreeAt?, lookup]; rfl
  have hp : positionNode (⟨node.1, hpos⟩ : Position arm.tree) = dsub := by
    have spec := positionNode_spec (⟨node.1, hpos⟩ : Position arm.tree)
    rw [← decoratedSubtreeAt?_eq_subtreeAt?, lookup] at spec
    exact (Option.some.inj spec).symm
  subst hp
  have builtI' : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? (.rule4b ρ)
      (ActualReaderPhysicalBranchInverse.dependencyReader input setup.c) fuelI
      (positionSource (positionChild (⟨node.1, hpos⟩ : Position arm.tree) i hi)) = some keyI := by
    show input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? (.rule4b ρ) _ fuelI
      (positionNode (positionChild (⟨node.1, hpos⟩ : Position arm.tree) i hi)).source = some keyI
    rw [positionNode_positionChild]
    exact builtI
  have builtJ' : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? (.rule4b ρ)
      (ActualReaderPhysicalBranchInverse.dependencyReader input setup.c) fuelJ
      (positionSource (positionChild (⟨node.1, hpos⟩ : Position arm.tree) j hj)) = some keyJ := by
    show input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? (.rule4b ρ) _ fuelJ
      (positionNode (positionChild (⟨node.1, hpos⟩ : Position arm.tree) j hj)).source = some keyJ
    rw [positionNode_positionChild]
    exact builtJ
  obtain ⟨tL, tR, hshape, _sourceL, _sourceR, matchL, matchR, _realizesL, _realizesR,
      labelsL, labelsR, sparseL, sparseR, noneIff, _chiralIff, _rule4aEq, _markedEq⟩ :=
    exists_actualSiblingPhysicalKind setup arm.realizes reachable
      (⟨node.1, hpos⟩ : Position arm.tree) hi hj hij (.rule4b ρ) (.rule4b ρ) fuelI fuelJ
      keyI keyJ builtI' builtJ' tie
  refine scalar4a_eq_of_tableAligned
    (descriptor_forall₂_of_tableMatch hshape matchL matchR ?_ ?_ noneIff)
  · intro pL
    rcases sparseL pL with absent | ⟨descriptor, chiral⟩
    · exact Or.inl ((labelsL pL).trans absent)
    · exact Or.inr ⟨descriptor, (labelsL pL).trans chiral⟩
  · intro pR
    rcases sparseR pR with absent | ⟨descriptor, chiral⟩
    · exact Or.inl ((labelsR pR).trans absent)
    · exact Or.inr ⟨descriptor, (labelsR pR).trans chiral⟩

/-- **`ArmReadback4b` on the physical domain.**  An original-root arm of the actual molecular
reader at the final occurrence of the detected centre, reachable from the slot tree, satisfies
every stage-`.rule4b ρ` readback hypothesis including sibling-kind agreement. -/
theorem armReadback4b_of_setup (hcenter : setup.c.1 = center.1)
    (arm : input.certified.OriginalRootArm center index (.rule4b ρ)
      (input.certified.molecularReader (actualReferenceDescriptorMap input)
        (ActualReaderPhysicalBranchInverse.topTarget input setup.c)))
    (reachable : input.certified.ActualChildReachable setup.tree.source arm.tree.source) :
    ArmReadback4b arm (actualReferenceDescriptorMap input) (input.certified.topUnit center) := by
  have readback := molecularReader_arm_observations (actualReferenceDescriptorMap input)
    (ActualReaderPhysicalBranchInverse.topTarget input setup.c) arm
    ((ActualReaderPhysicalBranchInverse.topTarget_root input setup.c).trans hcenter)
    (ActualReaderPhysicalBranchInverse.topTarget_address input setup.c)
    setup.singleBonded setup.acyclic
  have hread : input.certified.molecularReader (actualReferenceDescriptorMap input)
      (ActualReaderPhysicalBranchInverse.topTarget input setup.c) =
      ActualReaderPhysicalBranchInverse.dependencyReader input setup.c :=
    actualReference_molecularReader input setup.singleBonded setup.acyclic setup.noDouble _
  have hsingle : ∀ atom other, input.certified.moleculeGraph.bond atom other ≤ 1 := by
    intro atom other
    rcases Nat.eq_zero_or_pos (input.certified.moleculeGraph.bond atom other) with hzero | hpos
    · rw [hzero]; exact Nat.zero_le 1
    · exact le_of_eq (setup.singleBonded atom other hpos)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro node actual lookup
    obtain ⟨actual', lookup', hlabel, _⟩ := readback node
    rw [decoratedSubtreeAt?_eq_subtreeAt?] at lookup
    cases Option.some.inj (lookup.symm.trans lookup')
    exact hlabel
  · intro node
    exact occurrenceReading_tetrahedral_of_map _ _ _ _
      (fun u d h => actualReferenceDescriptorMap_tetrahedral input u d h) node
  · intro node
    obtain ⟨_, _, _, havail⟩ := readback node
    exact havail
  · exact rule4abOnly_readingEvidence_of_single input.certified.moleculeGraph
      (actualReferenceDescriptorMap input) (input.certified.topUnit center) (armGraph arm)
      hsingle (senseOf ρ)
  · intro node dsub lookup i j hi hj hij fuelI fuelJ keyI keyJ builtI builtJ tie
    exact siblingKind_of_setup setup hread arm reachable node dsub lookup i j hi hj hij
      fuelI fuelJ keyI keyJ builtI builtJ tie

/-- The slot's own arm: its root cursor is the slot tree's source, so reachability is the
zero-step path. -/
theorem armReadback4b_of_setup_of_source (hcenter : setup.c.1 = center.1)
    (arm : input.certified.OriginalRootArm center index (.rule4b ρ)
      (input.certified.molecularReader (actualReferenceDescriptorMap input)
        (ActualReaderPhysicalBranchInverse.topTarget input setup.c)))
    (hsource : arm.tree.source = setup.tree.source) :
    ArmReadback4b arm (actualReferenceDescriptorMap input) (input.certified.topUnit center) :=
  armReadback4b_of_setup setup hcenter arm (by rw [hsource]; exact Relation.ReflTransGen.refl)

end Physical

end
end Rule4aTableBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.scalar4a_eq_of_tableAligned
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.siblingKind_of_setup
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.armReadback4b_of_setup
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.armReadback4b_of_setup_of_source
