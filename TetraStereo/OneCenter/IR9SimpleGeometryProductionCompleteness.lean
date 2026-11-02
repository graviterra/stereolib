import TetraStereo.OneCenter.IR9SimpleGeometryAbsoluteSymmetry

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.SimpleGeometryProductionCompleteness

open FiniteSymmetry
open SimpleGeometrySourceIndexCompleteness

theorem priorityOfProduction_injective :
    Function.Injective BlueBookP93.priorityOfProduction := by
  intro left right same
  cases left
  cases right
  simp [BlueBookP93.priorityOfProduction] at same
  simp_all

theorem mapPriorityOfProduction_injective :
    Function.Injective (List.map BlueBookP93.priorityOfProduction) :=
  List.map_injective_iff.mpr priorityOfProduction_injective

namespace TShape

open SimpleGeometrySourceIndexCompleteness.TShape

theorem productionConfigurationIndex_eq_iff_symmetryEquivalent
    (left right : Position → PolyhedralPriorityNumber)
    (leftInjective : Function.Injective left)
    (rightInjective : Function.Injective right)
    (sameMultiset : SamePriorityMultiset
      (fun position => BlueBookP93.priorityOfProduction (left position))
      (fun position => BlueBookP93.priorityOfProduction (right position))) :
    tShapeConfigurationIndex (left .stem) = tShapeConfigurationIndex (right .stem) ↔
      Equivalent
        (fun position => BlueBookP93.priorityOfProduction (left position))
        (fun position => BlueBookP93.priorityOfProduction (right position)) := by
  let leftSource := fun position => BlueBookP93.priorityOfProduction (left position)
  let rightSource := fun position => BlueBookP93.priorityOfProduction (right position)
  have sourceExact := sourceIndex_eq_iff_symmetryEquivalent_of_samePriorityMultiset
    leftSource rightSource (priorityOfProduction_injective.comp leftInjective)
      (priorityOfProduction_injective.comp rightInjective) sameMultiset
  constructor
  · intro sameProduction
    apply sourceExact.mp
    have mapped := congrArg (List.map BlueBookP93.priorityOfProduction) sameProduction
    simpa [leftSource, rightSource, sourceIndex,
      tShapeConfigurationIndex, BlueBookP93.tShapeIndex] using mapped
  · intro equivalent
    apply mapPriorityOfProduction_injective
    have sourceSame := sourceExact.mpr equivalent
    simpa [leftSource, rightSource, sourceIndex,
      tShapeConfigurationIndex, BlueBookP93.tShapeIndex] using sourceSame

end TShape

namespace FourOpposite

open SimpleGeometrySourceIndexCompleteness.FourOpposite

theorem productionSquarePlanarIndex_eq_iff_symmetryEquivalent
    (left right : Position → PolyhedralPriorityNumber)
    (leftSenior rightSenior : Position)
    (leftInjective : Function.Injective left)
    (rightInjective : Function.Injective right)
    (leftSeniorCorrect : IsSenior
      (fun position => BlueBookP93.priorityOfProduction (left position)) leftSenior)
    (rightSeniorCorrect : IsSenior
      (fun position => BlueBookP93.priorityOfProduction (right position)) rightSenior)
    (sameMultiset : SamePriorityMultiset
      (fun position => BlueBookP93.priorityOfProduction (left position))
      (fun position => BlueBookP93.priorityOfProduction (right position))) :
    squarePlanarConfigurationIndex (left (opposite leftSenior)) =
        squarePlanarConfigurationIndex (right (opposite rightSenior)) ↔
      Equivalent
        (fun position => BlueBookP93.priorityOfProduction (left position))
        (fun position => BlueBookP93.priorityOfProduction (right position)) := by
  let leftSource := fun position => BlueBookP93.priorityOfProduction (left position)
  let rightSource := fun position => BlueBookP93.priorityOfProduction (right position)
  have sourceExact := blueBook_squarePlanarIndex_eq_iff_symmetryEquivalent
    leftSource rightSource leftSenior rightSenior
      (priorityOfProduction_injective.comp leftInjective)
      (priorityOfProduction_injective.comp rightInjective)
      leftSeniorCorrect rightSeniorCorrect sameMultiset
  constructor
  · intro sameProduction
    apply sourceExact.mp
    have mapped := congrArg (List.map BlueBookP93.priorityOfProduction) sameProduction
    simpa [leftSource, rightSource, transPriority,
      squarePlanarConfigurationIndex, BlueBookP93.squarePlanarIndex] using mapped
  · intro equivalent
    apply mapPriorityOfProduction_injective
    have sourceSame := sourceExact.mpr equivalent
    simpa [leftSource, rightSource, transPriority,
      squarePlanarConfigurationIndex, BlueBookP93.squarePlanarIndex] using sourceSame

theorem productionSquarePyramid4Index_eq_iff_symmetryEquivalent
    (left right : Position → PolyhedralPriorityNumber)
    (leftSenior rightSenior : Position)
    (leftInjective : Function.Injective left)
    (rightInjective : Function.Injective right)
    (leftSeniorCorrect : IsSenior
      (fun position => BlueBookP93.priorityOfProduction (left position)) leftSenior)
    (rightSeniorCorrect : IsSenior
      (fun position => BlueBookP93.priorityOfProduction (right position)) rightSenior)
    (sameMultiset : SamePriorityMultiset
      (fun position => BlueBookP93.priorityOfProduction (left position))
      (fun position => BlueBookP93.priorityOfProduction (right position))) :
    squarePyramid4ConfigurationIndex (left (opposite leftSenior)) =
        squarePyramid4ConfigurationIndex (right (opposite rightSenior)) ↔
      Equivalent
        (fun position => BlueBookP93.priorityOfProduction (left position))
        (fun position => BlueBookP93.priorityOfProduction (right position)) := by
  let leftSource := fun position => BlueBookP93.priorityOfProduction (left position)
  let rightSource := fun position => BlueBookP93.priorityOfProduction (right position)
  have sourceExact := blueBook_squarePyramid4Index_eq_iff_symmetryEquivalent
    leftSource rightSource leftSenior rightSenior
      (priorityOfProduction_injective.comp leftInjective)
      (priorityOfProduction_injective.comp rightInjective)
      leftSeniorCorrect rightSeniorCorrect sameMultiset
  constructor
  · intro sameProduction
    apply sourceExact.mp
    have mapped := congrArg (List.map BlueBookP93.priorityOfProduction) sameProduction
    simpa [leftSource, rightSource, transPriority,
      squarePyramid4ConfigurationIndex, BlueBookP93.squarePyramid4Index] using mapped
  · intro equivalent
    apply mapPriorityOfProduction_injective
    have sourceSame := sourceExact.mpr equivalent
    simpa [leftSource, rightSource, transPriority,
      squarePyramid4ConfigurationIndex, BlueBookP93.squarePyramid4Index] using sourceSame

end FourOpposite

namespace SeeSaw

open SimpleGeometrySourceIndexCompleteness.SeeSaw

theorem productionConfigurationIndex_eq_iff_symmetryEquivalent
    (left right : Position → PolyhedralPriorityNumber)
    (leftInjective : Function.Injective left)
    (rightInjective : Function.Injective right)
    (sameMultiset : SamePriorityMultiset
      (fun position => BlueBookP93.priorityOfProduction (left position))
      (fun position => BlueBookP93.priorityOfProduction (right position))) :
    seeSawConfigurationIndex (left .wide0) (left .wide1) =
        seeSawConfigurationIndex (right .wide0) (right .wide1) ↔
      Equivalent
        (fun position => BlueBookP93.priorityOfProduction (left position))
        (fun position => BlueBookP93.priorityOfProduction (right position)) := by
  let leftSource := fun position => BlueBookP93.priorityOfProduction (left position)
  let rightSource := fun position => BlueBookP93.priorityOfProduction (right position)
  have sourceExact := sourceIndex_eq_iff_symmetryEquivalent_of_samePriorityMultiset
    leftSource rightSource (priorityOfProduction_injective.comp leftInjective)
      (priorityOfProduction_injective.comp rightInjective) sameMultiset
  constructor
  · intro sameProduction
    apply sourceExact.mp
    have mapped := congrArg (List.map BlueBookP93.priorityOfProduction) sameProduction
    simpa [leftSource, rightSource, sourceIndex,
      seeSawConfigurationIndex_conforms_P93] using mapped
  · intro equivalent
    apply mapPriorityOfProduction_injective
    have sourceSame := sourceExact.mpr equivalent
    simpa [leftSource, rightSource, sourceIndex,
      seeSawConfigurationIndex_conforms_P93] using sourceSame

end SeeSaw

end TetraStereo.OneCenter.RedBookIR9.SimpleGeometryProductionCompleteness
