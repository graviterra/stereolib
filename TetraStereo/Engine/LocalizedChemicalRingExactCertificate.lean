import TetraStereo.Engine.LocalizedChemicalRingPhysicalCertificate
import TetraStereo.OneCenter.LocalizedChemicalRingAllRootLetters
import TetraStereo.OneCenter.LocalizedChemicalRingRegeneratedLifetime
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.Engine.LocalizedChemicalRing

open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRingAllRootLetters
open LocalizedChemicalRingTwoPairReport (RootSuccess)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData)
open LocalizedChemicalRingJointPreparedRootInput (root_data)
open LocalizedChemicalRingPhysicalAdmission (detectedCoordinateCfg detected_all_calibrated)
open scoped Classical

/-- The named profile's earlier source, cancellation, applicability and PPD results together
with exact source-priority letters, casing and refusal criteria at every detected center. -/
structure ExactSourceMeaning (profile : Profile) (input : Input)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (p : LocalizedChemicalRingJointPreparedSourceModel.Profile input.certified input.molecule) : Prop
    extends SourceMeaning profile input cfg p where
  exactEntries : ∀ c : input.certified.detectedMultiCenterMolecule.Center,
    ∃ data : OccurrenceData input.certified input.molecule c (canonicalCenterRoot c.1.val),
      data.target.1.address = [] ∧ (∃ m, Eligible input.certified cfg c m) ∧
      ∀ m, Eligible input.certified cfg c m → ∀ outcome,
        (c.1.val, outcome) ∈ analyze profile input ↔
          (if RootSuccess input.certified input.molecule input.agreement input.single cfg c data p then
            let parity := orientation input.certified input.molecule input.agreement input.single c data p m
            some (orientedLabel (input.certified.detectedMultiCenterMolecule.configurationSign cfg c)
              (parity false) (parity true)) else none) = outcome
  viewedEntries : ∀ (c : input.certified.detectedMultiCenterMolecule.Center)
    (data : OccurrenceData input.certified input.molecule c (canonicalCenterRoot c.1.val)),
    data.target.1.address = [] → ∀ m, Eligible input.certified cfg c m →
      ∀ label, (c.1.val, some label) ∈ analyze profile input →
        let frame := priorityFrame input.certified input.molecule input.agreement input.single c data p m
        ∃ raw, ViewedLetter input.certified
            (LocalizedChemicalRingCompletenessMarked.enumeration input.certified c (frame false)) raw ∧
          label = (if LocalizedChemicalRingPairingParity.matchingEven (frame false) =
            LocalizedChemicalRingPairingParity.matchingEven (frame true) then
            .chiral raw else .pseudoasymmetric (pseudoRSOfRS raw))

theorem existsUnique_exactSourceMeaning (profile : Profile) (input : Input)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (calibrated : ∀ c, ActualPhysicalCalibratedCoordinates input.certified
      input.certified.detectedMultiCenterMolecule cfg c) :
    ∃! p, ExactSourceMeaning profile input cfg p := by
  obtain ⟨p, hp, unique⟩ := existsUnique_sourceMeaning profile input cfg calibrated
  refine ⟨p, ⟨hp, ?_, ?_⟩, fun q h => unique q h.toSourceMeaning⟩
  · intro c
    obtain ⟨data,addr⟩ := root_data input.certified input.molecule input.agreement input.admissible
      input.supported input.single c
    refine ⟨data, addr, exists_eligible input.certified cfg c, ?_⟩
    intro m hm outcome
    rw [analyze_eq_prepared]
    exact exact_entry input.certified input.molecule input.agreement input.admissible input.supported
      input.single input.charge cfg calibrated c data addr p hp.model m hm outcome
  · intro c data addr m eligible label entry
    rw [analyze_eq_prepared] at entry
    exact viewed_entry input.certified input.molecule input.agreement input.admissible input.supported
      input.single input.charge cfg calibrated c data addr p hp.model m eligible label entry

theorem existsUnique_exactSourceMeaning_of_coordinates (profile : Profile) (input : Input)
    (accepted : coordinatesAdmitted input = true) :
    ∃! p, ExactSourceMeaning profile input (detectedCoordinateCfg input.certified) p :=
  existsUnique_exactSourceMeaning profile input _ (detected_all_calibrated input.certified accepted)

open LocalizedChemicalRingRegeneratedLifetime
open LocalizedChemicalRingJointPreparedSourceQueries (SourceQuery)
open LocalizedChemicalRingJointPreparedSourceModelExistence (finalQuery)
open LocalizedGenericMarkedRecalculation (structuralDepth)
open LocalizedChemicalRingPhysicalSense (inputGeometry)

/-- Every covered depth-round schedule can start with arbitrary auxiliary entries and still
returns the literal public report value as soon as the center's root depth has passed. -/
theorem ExactSourceMeaning.scheduled_entry {profile : Profile} {input : Input} {cfg p}
    (meaning : ExactSourceMeaning profile input cfg p)
    (refresh : Nat → SourceQuery input.certified input.molecule → Bool)
    (covers : ∀ q, refresh (structuralDepth input.molecule q.1) q = true)
    (seed : LocalizedChemicalRingJointPreparedSourceModel.Profile input.certified input.molecule)
    (c : input.certified.detectedMultiCenterMolecule.Center) (n : Nat)
    (ready : structuralDepth input.molecule (canonicalCenterRoot c.1.val) < n)
    (outcome : Option LocalizedAuxiliaryLabel) :
    (c.1.val, outcome) ∈ analyze profile input ↔
      let frame := frames input.certified input.molecule input.agreement input.admissible input.supported input.single
      rounds input.certified input.molecule input.single frame .accumulated refresh seed n
        (inputGeometry input.certified) [] (finalQuery input.certified input.molecule input.agreement c) = outcome := by
  let q := finalQuery input.certified input.molecule input.agreement c
  let frame := frames input.certified input.molecule input.agreement input.admissible input.supported input.single
  have scheduled := schedule_independent input.certified input.molecule input.admissible input.single
    frame .accumulated refresh covers seed n q ready (inputGeometry input.certified) []
  rw [accumulated_eq_sourceModel input.certified input.molecule input.admissible input.single
    frame p meaning.model] at scheduled
  dsimp only
  rw [scheduled, analyze_eq_prepared, LocalizedChemicalRingJointPreparedReport.mem_analyze_at_center_iff,
    LocalizedChemicalRingJointPreparedSourceModelExistence.assignCenter_eq_sourceModel input.certified
      input.molecule input.agreement input.admissible input.supported input.single meaning.model]


/-- A discrepancy with independently regenerated scalar replacement on a public entry
requires a nested lifetime-sensitive query strictly below that very center. -/
theorem ExactSourceMeaning.replacement_disagreement {profile : Profile} {input : Input} {cfg p}
    (meaning : ExactSourceMeaning profile input cfg p)
    (c : input.certified.detectedMultiCenterMolecule.Center) (outcome : Option LocalizedAuxiliaryLabel)
    (member : (c.1.val, outcome) ∈ analyze profile input)
    (different :
      let frame := frames input.certified input.molecule input.agreement input.admissible input.supported input.single
      outcome ≠ solution input.certified input.molecule input.single frame .current
        (inputGeometry input.certified) [] (finalQuery input.certified input.molecule input.agreement c)) :
    let frame := frames input.certified input.molecule input.agreement input.admissible input.supported input.single
    ∃ d : SourceQuery input.certified input.molecule, LocalizedMarkedTerminalReferenceScope.StrictDescendant input.molecule (canonicalCenterRoot c.1.val) d.1 ∧
      NestedDifference input.certified input.molecule input.single frame d := by
  let q := finalQuery input.certified input.molecule input.agreement c
  let frame := frames input.certified input.molecule input.agreement input.admissible input.supported input.single
  apply empty_context_disagreement_descends input.certified input.molecule input.admissible
    input.single frame q (inputGeometry input.certified)
  rw [accumulated_eq_sourceModel input.certified input.molecule input.admissible input.single
    frame p meaning.model]
  rw [analyze_eq_prepared, LocalizedChemicalRingJointPreparedReport.mem_analyze_at_center_iff,
    LocalizedChemicalRingJointPreparedSourceModelExistence.assignCenter_eq_sourceModel input.certified
      input.molecule input.agreement input.admissible input.supported input.single meaning.model] at member
  change p _ [] q = outcome at member
  rw [member]
  exact different

/-- For this input and center it suffices to compare the two local updates under one
inherited atom, on the actual source profile and the two input geometries. This gives
equality with the independently regenerated replacement report, including refusals. -/
theorem ExactSourceMeaning.replacement_entry_of_singleton_agreement {profile : Profile} {input : Input} {cfg p}
    (meaning : ExactSourceMeaning profile input cfg p)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (agree :
      let frame := frames input.certified input.molecule input.agreement input.admissible input.supported input.single
      let geom := inputGeometry input.certified
      ∀ (d : SourceQuery input.certified input.molecule) (g : LocalizedGenericMarkedRecalculation.Geometry)
        (a : input.certified.Atom),
        LocalizedMarkedTerminalReferenceScope.StrictDescendant input.molecule (canonicalCenterRoot c.1.val) d.1 →
        (g = geom ∨ g = LocalizedGenericMarkedRecalculation.mirror geom) →
        update input.certified input.molecule input.single frame .accumulated p d g [a] =
          update input.certified input.molecule input.single frame .current p d g [a])
    (outcome : Option LocalizedAuxiliaryLabel) :
    (c.1.val, outcome) ∈ analyze profile input ↔
      let frame := frames input.certified input.molecule input.agreement input.admissible input.supported input.single
      solution input.certified input.molecule input.single frame .current (inputGeometry input.certified)
        [] (finalQuery input.certified input.molecule input.agreement c) = outcome := by
  let q := finalQuery input.certified input.molecule input.agreement c
  let frame := frames input.certified input.molecule input.agreement input.admissible input.supported input.single
  have source := accumulated_eq_sourceModel input.certified input.molecule input.admissible input.single
    frame p meaning.model
  have same : solution input.certified input.molecule input.single frame .accumulated (inputGeometry input.certified) [] q =
      solution input.certified input.molecule input.single frame .current (inputGeometry input.certified) [] q := by
    by_contra different
    obtain ⟨d,g,a,below,side,unequal⟩ := disagreement_singleton_on_input input.certified input.molecule
      input.admissible input.single frame q (inputGeometry input.certified) different
    dsimp only at unequal
    rw [source] at unequal
    exact unequal (agree d g a below side)
  dsimp only
  rw [analyze_eq_prepared, LocalizedChemicalRingJointPreparedReport.mem_analyze_at_center_iff,
    LocalizedChemicalRingJointPreparedSourceModelExistence.assignCenter_eq_sourceModel input.certified
      input.molecule input.agreement input.admissible input.supported input.single meaning.model]
  change p _ [] q = outcome ↔ _
  rw [← same, source]

/-- A public report discrepancy has a single eligible promotion witness on this input
or its reflection. The only auxiliary table used to compare the two readings is the
unique public source profile. -/
theorem ExactSourceMeaning.replacement_promotion_witness {profile : Profile} {input : Input} {cfg p}
    (meaning : ExactSourceMeaning profile input cfg p)
    (c : input.certified.detectedMultiCenterMolecule.Center) (outcome : Option LocalizedAuxiliaryLabel)
    (entry : (c.1.val, outcome) ∈ analyze profile input)
    (different :
      let frame := frames input.certified input.molecule input.agreement input.admissible input.supported input.single
      outcome ≠ solution input.certified input.molecule input.single frame .current (inputGeometry input.certified)
        [] (finalQuery input.certified input.molecule input.agreement c)) :
    let frame := frames input.certified input.molecule input.agreement input.admissible input.supported input.single
    let geom := inputGeometry input.certified
    ∃ (d : SourceQuery input.certified input.molecule) (g : LocalizedGenericMarkedRecalculation.Geometry)
      (a : input.certified.Atom),
      LocalizedMarkedTerminalReferenceScope.StrictDescendant input.molecule (canonicalCenterRoot c.1.val) d.1 ∧
      (g = geom ∨ g = LocalizedGenericMarkedRecalculation.mirror geom) ∧
      let data := (frame d).2
      let family := LocalizedChemicalRingJointPreparedSourceModel.profileFamily input.certified input.molecule p d
      let k := LocalizedChemicalRingJointPreparedSourceStep.sourceKeysAt input.certified input.single family
        data.target data.frame g [a]
      ∃ i ∈ LocalizedChemicalRingJointPreparedSourceStep.sourceSelectedSlots k,
        LocalizedChemicalRingReferencePolicy.policyFallback input.certified input.single .accumulated .regenerated
          family data.target data.frame g [a] i ≠
        LocalizedChemicalRingReferencePolicy.policyFallback input.certified input.single .current .regenerated
          family data.target data.frame g [a] i := by
  let q := finalQuery input.certified input.molecule input.agreement c
  let frame := frames input.certified input.molecule input.agreement input.admissible input.supported input.single
  have source := accumulated_eq_sourceModel input.certified input.molecule input.admissible input.single
    frame p meaning.model
  rw [analyze_eq_prepared, LocalizedChemicalRingJointPreparedReport.mem_analyze_at_center_iff,
    LocalizedChemicalRingJointPreparedSourceModelExistence.assignCenter_eq_sourceModel input.certified
      input.molecule input.agreement input.admissible input.supported input.single meaning.model] at entry
  change p _ [] q = outcome at entry
  have diff : solution input.certified input.molecule input.single frame .accumulated (inputGeometry input.certified) [] q ≠
      solution input.certified input.molecule input.single frame .current (inputGeometry input.certified) [] q := by
    rw [source, entry]
    exact different
  have witness := disagreement_singleton_promotion input.certified input.molecule input.admissible input.single
    frame q (inputGeometry input.certified) diff
  rw [source] at witness
  exact witness

/-- The source profile evaluated on the reflected geometry exchanges uppercase letters and
preserves lowercase letters and refusals at every actual public report entry. -/
theorem ExactSourceMeaning.mirror_entry {profile : Profile} {input : Input} {cfg p}
    (meaning : ExactSourceMeaning profile input cfg p)
    (c : input.certified.detectedMultiCenterMolecule.Center) (outcome : Option LocalizedAuxiliaryLabel)
    (member : (c.1.val, outcome) ∈ analyze profile input) :
    p (LocalizedGenericMarkedRecalculation.mirror (inputGeometry input.certified)) []
      (finalQuery input.certified input.molecule input.agreement c) =
      outcome.map LocalizedChemicalRingDescriptorSpatialMirror.spatialMirror := by
  rw [analyze_eq_prepared, LocalizedChemicalRingJointPreparedReport.mem_analyze_at_center_iff] at member
  rw [← LocalizedChemicalRingJointPreparedSourceModelExistence.assignCenter_eq_sourceModel input.certified
    input.molecule input.agreement input.admissible input.supported input.single meaning.model,
    ← member]
  exact LocalizedChemicalRingJointPreparedReflection.descriptorOfStep_spatialMirror _ _ _ _ _ _ _

/-- The published mirror-invariance test for lowercase, expressed as equality of actual
letters on the two geometries, with no proper-distinguishability assumption. -/
theorem ExactSourceMeaning.lowercase_iff_mirror_fixed {profile : Profile} {input : Input} {cfg p}
    (meaning : ExactSourceMeaning profile input cfg p)
    (c : input.certified.detectedMultiCenterMolecule.Center) (label : LocalizedAuxiliaryLabel)
    (member : (c.1.val, some label) ∈ analyze profile input) :
    label.IsLowercase ↔
      p (LocalizedGenericMarkedRecalculation.mirror (inputGeometry input.certified)) []
        (finalQuery input.certified input.molecule input.agreement c) = some label := by
  rw [meaning.mirror_entry c _ member]
  rcases label with raw | raw <;> cases raw <;>
    simp [LocalizedTetrahedralRSPseudoDescriptor.IsLowercase,
      LocalizedChemicalRingDescriptorSpatialMirror.spatialMirror, RS.swap]

/-- For an input with only one detected center, both reference lifetimes and both auxiliary
chronologies give its actual public entry. The auxiliary table may be chosen arbitrarily. -/
theorem ExactSourceMeaning.singleCenter_policy_entry {profile : Profile} {input : Input} {cfg p}
    (meaning : ExactSourceMeaning profile input cfg p)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (onlyCenter : ∀ other : input.certified.detectedMultiCenterMolecule.Center, other = c)
    (life : LocalizedChemicalRingReferencePolicy.ReferenceLifetime)
    (chronology : LocalizedChemicalRingReferencePolicy.AuxiliaryChronology)
    (table : LocalizedChemicalRingJointPreparedSourceModel.Profile input.certified input.molecule)
    (outcome : Option LocalizedAuxiliaryLabel) :
    (c.1.val, outcome) ∈ analyze profile input ↔
      let frame := frames input.certified input.molecule input.agreement input.admissible input.supported input.single
      let q := finalQuery input.certified input.molecule input.agreement c
      let read := fun geom => rawWith input.certified input.molecule input.single frame life chronology table q geom []
      let geom := inputGeometry input.certified
      LocalizedGenericMarkedRecalculation.caseFromMirror? (read geom)
        (read (LocalizedGenericMarkedRecalculation.mirror geom)) = outcome := by
  let q := finalQuery input.certified input.molecule input.agreement c
  let frame := frames input.certified input.molecule input.agreement input.admissible input.supported input.single
  have terminal := single_center_no_descendants input.certified input.molecule input.agreement c onlyCenter
  have eqn := raw_without_descendants input.certified input.molecule input.single frame q terminal life
    chronology table p
  dsimp only
  rw [eqn, eqn, analyze_eq_prepared, LocalizedChemicalRingJointPreparedReport.mem_analyze_at_center_iff,
    LocalizedChemicalRingJointPreparedSourceModelExistence.assignCenter_eq_sourceModel input.certified
      input.molecule input.agreement input.admissible input.supported input.single meaning.model]
  exact iff_of_eq (congrArg (· = outcome)
    (meaning.model (inputGeometry input.certified) [] q (frame q).1 (frame q).2).symm)

/-- A copied frame retains each strict pair and asks the new comparison only about ties.
Both comparators are total on the admitted four-ligand frame. -/
def copyPriorities {α : Type} (prior next : α → α → Ordering) (a b : α) : Ordering :=
  (prior a b).then (next a b)

/-- Exact pairwise obligations for replacing an accumulated ranking by one active
reference plus a copied partition. This includes ties in the resulting partition. -/
theorem copyPriorities_eq_iff {α : Type} (prior next accumulated : α → α → Ordering) :
    copyPriorities prior next = accumulated ↔
      (∀ a b, prior a b ≠ .eq → accumulated a b = prior a b) ∧
      (∀ a b, prior a b = .eq → accumulated a b = next a b) := by
  constructor
  · rintro rfl
    constructor
    · intro a b h
      cases e : prior a b <;> simp_all [copyPriorities]
    · intro a b h
      simp [copyPriorities, h]
  · rintro ⟨strictPairs, tiedPairs⟩
    funext a b
    cases h : prior a b with
    | lt => simpa [copyPriorities,h] using (strictPairs a b (by simp [h])).symm
    | eq => simpa [copyPriorities,h] using (tiedPairs a b h).symm
    | gt => simpa [copyPriorities,h] using (strictPairs a b (by simp [h])).symm

/-- The criterion suffices for the full order of the four slots and every adjacent
decision, including unresolved ligand pairs. -/
theorem copiedFrame_partition_eq (prior next accumulated : Fin 4 → Fin 4 → Ordering)
    (strictPairs : ∀ a b, prior a b ≠ .eq → accumulated a b = prior a b)
    (tiedPairs : ∀ a b, prior a b = .eq → accumulated a b = next a b) :
    let rank := fun (cmp : Fin 4 → Fin 4 → Ordering) => do
      let before := fun a b => some (cmp a b)
      let order ← LocalizedMarkedRetainedOrdinaryRanking.sortBy? before (List.finRange 4)
      pure (order, LocalizedMarkedRetainedOrdinaryRanking.adjacentBy before order)
    rank (copyPriorities prior next) = rank accumulated := by
  rw [(copyPriorities_eq_iff prior next accumulated).mpr ⟨strictPairs,tiedPairs⟩]

/-- Adding only a direct mark to a copied frame yields a strict order exactly when
all the *other* ligands were already mutually distinguishable. -/
theorem directMark_injective_iff {α β : Type} [DecidableEq α] (old : α → β) (mark : α) :
    Function.Injective (fun a => (old a, decide (a = mark))) ↔
      ∀ a b, a ≠ mark → b ≠ mark → old a = old b → a = b := by
  constructor
  · intro injective a b ha hb h
    apply injective
    simp [ha,hb,h]
  · intro others a b h
    have labels := congrArg Prod.fst h
    have marked := congrArg Prod.snd h
    by_cases ha : a = mark <;> by_cases hb : b = mark
    · exact ha.trans hb.symm
    · simp [ha,hb] at marked
    · simp [ha,hb] at marked
    · exact others a b ha hb labels

/-- With at most two inherited classes, one direct point mark can never separate
four ligands. A successful trial at this gate requires additional pair distinctions. -/
theorem twoClasses_directMark_unresolved (old : Fin 4 → Bool) (mark : Fin 4) :
    ¬ Function.Injective (fun a => (old a, decide (a = mark))) := by
  intro all
  have rest := (directMark_injective_iff old mark).mp all
  have inj : Function.Injective (fun i : Fin 3 => old (mark.succAbove i)) := by
    intro i j h
    exact Fin.succAbove_right_injective
      (rest _ _ (mark.succAbove_ne i) (mark.succAbove_ne j) h)
  have impossible := Fintype.card_le_of_injective _ inj
  simp at impossible

end TetraStereo.Engine.LocalizedChemicalRing

assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.ExactSourceMeaning
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.existsUnique_exactSourceMeaning
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.existsUnique_exactSourceMeaning_of_coordinates
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.ExactSourceMeaning.scheduled_entry
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.ExactSourceMeaning.replacement_disagreement
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.ExactSourceMeaning.mirror_entry
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.ExactSourceMeaning.lowercase_iff_mirror_fixed
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.ExactSourceMeaning.singleCenter_policy_entry
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.ExactSourceMeaning.replacement_entry_of_singleton_agreement
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.ExactSourceMeaning.replacement_promotion_witness
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.copyPriorities_eq_iff
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.copiedFrame_partition_eq
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.directMark_injective_iff
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.twoClasses_directMark_unresolved
