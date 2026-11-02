import TetraStereo.OneCenter.LocalizedFamilyAssignmentsExecutable
import TetraStereo.OneCenter.AuthoritativeSemanticOrdinaryDoubleBondSpatialAssignment

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OrdinaryPlanar

/-- The same complete comparison as tetrahedral ordering, retaining its Rule5 parity bit. -/
def compareKeys (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedOccurrenceRule3Through5Key) :
    ConstitutionalDescriptorHierarchyComparison :=
  match input.compareLocalizedRerootRecursiveRule3SpatialKeys left.rule3 right.rule3 with
  | .lt => { ordering := .lt, pseudo := false }
  | .gt => { ordering := .gt, pseudo := false }
  | .eq => localizedOccurrenceRule45ComparisonRecord
      (input.compareLocalizedRerootCompoundThroughRule5 left.rule45 right.rule45)

theorem compareKeys_ordering (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedOccurrenceRule3Through5Key) :
    (compareKeys input left right).ordering =
      input.compareLocalizedOccurrenceRule3Through5Keys left right := by
  unfold compareKeys compareLocalizedOccurrenceRule3Through5Keys
  generalize compared : input.compareLocalizedRerootRecursiveRule3SpatialKeys
    left.rule3 right.rule3 = ordering
  cases ordering <;> simp [compareLex, Ordering.byKey, compared,
    localizedOccurrenceRule45ComparisonRecord,
    input.compareLocalizedRerootCompoundThroughRule5_ordering]

structure Selection (input : CertifiedLocalizedCIPInput) where
  reference : input.Atom
  enantiomorphic : Bool

/-- Independent meaning: the chosen exact endpoint candidate strictly outranks the other,
and the retained parity is the parity of that decisive complete comparison. -/
def SelectionMeaning (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedRule3EndpointKeyFrame) (selection : Selection input) : Prop :=
  (selection.reference = frame.first ∧
    (compareKeys input frame.firstKey frame.secondKey).ordering = .gt ∧
    selection.enantiomorphic = (compareKeys input frame.firstKey frame.secondKey).pseudo) ∨
  (selection.reference = frame.second ∧
    (compareKeys input frame.secondKey frame.firstKey).ordering = .gt ∧
    selection.enantiomorphic = (compareKeys input frame.secondKey frame.firstKey).pseudo)

/-- Both orientations are checked explicitly. A tie retains no arbitrary reference. -/
def select? (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedRule3EndpointKeyFrame) :
    Option { selection : Selection input // SelectionMeaning input frame selection } :=
  if first : (compareKeys input frame.firstKey frame.secondKey).ordering = .gt then
    some ⟨{ reference := frame.first,
             enantiomorphic := (compareKeys input frame.firstKey frame.secondKey).pseudo },
      Or.inl ⟨rfl, first, rfl⟩⟩
  else if second : (compareKeys input frame.secondKey frame.firstKey).ordering = .gt then
    some ⟨{ reference := frame.second,
             enantiomorphic := (compareKeys input frame.secondKey frame.firstKey).pseudo },
      Or.inr ⟨rfl, second, rfl⟩⟩
  else none

theorem select?_isSome_iff (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedRule3EndpointKeyFrame) :
    (select? input frame).isSome = true ↔ ∃ selection, SelectionMeaning input frame selection := by
  unfold select?
  split
  · rename_i first
    simp only [Option.isSome_some, true_iff]
    exact ⟨⟨frame.first, (compareKeys input frame.firstKey frame.secondKey).pseudo⟩,
      Or.inl ⟨rfl, first, rfl⟩⟩
  · rename_i first
    split
    · rename_i second
      simp only [Option.isSome_some, true_iff]
      exact ⟨⟨frame.second, (compareKeys input frame.secondKey frame.firstKey).pseudo⟩,
        Or.inr ⟨rfl, second, rfl⟩⟩
    · rename_i second
      simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_exists]
      intro selection meaning
      rcases meaning with left | right
      · exact first left.2.1
      · exact second right.2.1

/-- Any selected reference is senior in the existing complete key order. -/
theorem SelectionMeaning.strict
    {input : CertifiedLocalizedCIPInput} {frame : input.LocalizedRule3EndpointKeyFrame}
    {selection : Selection input} (meaning : SelectionMeaning input frame selection) :
    (selection.reference = frame.first ∧
      input.compareLocalizedOccurrenceRule3Through5Keys frame.firstKey frame.secondKey = .gt) ∨
    (selection.reference = frame.second ∧
      input.compareLocalizedOccurrenceRule3Through5Keys frame.secondKey frame.firstKey = .gt) := by
  rcases meaning with first | second
  · exact Or.inl ⟨first.1, (compareKeys_ordering input _ _).symm.trans first.2.1⟩
  · exact Or.inr ⟨second.1, (compareKeys_ordering input _ _).symm.trans second.2.1⟩

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OrdinaryPlanar
