import TetraStereo.OneCenter.LocalizedActualOrderedRootMirrorRule5Decision
import TetraStereo.OneCenter.DeclarativeCIPMultiReferenceProblem
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The eight-rule connection at a multi-reference root

For an arbitrary detected centre in the physical domain (`ActualCentrePhysicalSetup`: finite,
acyclic, simple-bonded, constant charge, no double-bond records, general rigid / terminal-twin)
whose four ligand branches are pairwise properly distinguishable, and with **no** restriction on
the number of nearest Rule-4b references (multiple nearest references, empty-reference branches
and mirror pairs are all retained, and no key separation is assumed):

* `ordering_eq_gt_iff_higher` — the ordered evaluator's through-Rule-5 comparison of two root
  ligands is `gt` exactly when the declarative `Problem.Higher` holds in the specialized molecular
  problem `multiReferenceProblem` (`DeclarativeCIPMultiReferenceProblem`), i.e. some rule among
  `1a, 1b, 2, 3, 4a, 4b, 4c, 5` is decisive after every earlier rule ties, its `RuleOutcome`
  quantified over every faithful exact expansion of both ligands;
* `ordering_eq_lt_iff_higher` — `lt` exactly when the reverse `Higher` holds;
* `ordering_eq_eq_iff_tied` — `eq` exactly when every ordinary rule ties.

The proof derives every declarative ordinary outcome and identifies it with the corresponding
production column (`ruleOutcome_*_iff`):

* Rules 1a, 1b, 2: the accepted localized constitutional bridge;
* Rule 3: tie after a constitutional tie — the Rule-3 component carries `⊥` everywhere on a
  simple-bonded molecule, so it is the constitutional shape;
* Rule 4a: the Rule-4a table bridge at the pair's common layout;
* Rule 4b: C5, the ordered compound Rules-4b/4c comparison is the signature comparison;
* Rule 4c: tie after a constitutional tie — on the physical domain no pseudoasymmetric
  descriptor is read at any node (`arm4a_noPseudo`, from the physical reader and the arm's
  molecular readback), so the Rule-4c component carries one constant label;
* Rule 5: after a prior tie the pair is enantiomorphic (R3), the ordered heads are matched (R4)
  with the declarative head references (`headSense_eq`), both ligands lay out one observation
  function (`observation_eq`), and R4's first-chiral-address decision is the declarative
  first difference of the two common-`R` seniority streams (`seniorityMirror_gt_iff`).

The first-decisive assembly (`higher_iff_chain8`, `tied_iff_chain8`) is generic.  This is a
comparison theorem; it is not a whole-molecule `CIPSpec` fixed point and it does not cover rings.
-/

namespace TetraStereo.OneCenter

open DeclarativeCIP

noncomputable section
open scoped Classical

/-! ## A canonical detected frame -/

namespace CertifiedLocalizedCIPInput

/-- The four neighbours of a detected occurrence's atom, in ascending atom order. -/
def localizedDetectedFrame (input : CertifiedLocalizedCIPInput) :
    DetectedFrame input.moleculeGraph where
  ligand unit index :=
    ((input.moleculeGraph.neighborFinset unit.1.atom).sort (· ≤ ·)).get
      (Fin.cast (by rw [Finset.length_sort]; exact unit.2.symm) index)
  adjacent unit index :=
    (input.moleculeGraph.mem_neighborFinset _ _).1 ((Finset.mem_sort _).1 (List.get_mem _ _))

theorem localizedDetectedFrame_ligand_topUnit (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4) :
    input.localizedDetectedFrame.ligand (input.topUnit center) index =
      input.canonicalLigandAtom center index :=
  rfl

/-- Every node of a realized decorated tree has a source reachable from the tree's source. -/
theorem subtreeAt?_source_reachable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel} :
    ∀ {tree : LocalizedCumulativeDecoratedTree input carrierFuel},
      LocalizedCumulativeTreeRealizes input read tree →
        ∀ {path : List Nat} {node : LocalizedCumulativeDecoratedTree input carrierFuel},
          _root_.TetraStereo.OneCenter.subtreeAt? tree path = some node →
            Relation.ReflTransGen (E input) tree.source node.source := by
  intro tree realizes path
  induction path generalizing tree with
  | nil =>
      intro node lookup
      cases Option.some.inj lookup
      exact Relation.ReflTransGen.refl
  | cons slot rest ih =>
      intro node lookup
      obtain ⟨child, hchild, hrest⟩ :=
        _root_.TetraStereo.OneCenter.subtreeAt?_cons_eq_some_iff.1 lookup
      cases realizes with
      | mk cursor children sortedChildren childrenComputed sourcePerm childrenRealize =>
          have hmem : child ∈ sortedChildren := List.mem_of_getElem? hchild
          have hsrc : child.source ∈ children :=
            sourcePerm.subset (List.mem_map_of_mem hmem)
          rw [input.localizedRerootChildren?_eq_some_executable] at childrenComputed
          cases Option.some.inj childrenComputed
          exact Relation.ReflTransGen.head hsrc (ih (childrenRealize child hmem) hrest)

end CertifiedLocalizedCIPInput

/-! ## Generic first-decisive assembly over the eight ordinary rules -/

namespace EightRuleAssembly

theorem then_eq_gt_iff (a b : Ordering) : a.then b = .gt ↔ a = .gt ∨ (a = .eq ∧ b = .gt) := by
  cases a <;> simp [Ordering.then]

theorem then_eq_eq_iff (a b : Ordering) : a.then b = .eq ↔ a = .eq ∧ b = .eq := by
  cases a <;> simp [Ordering.then]

theorem then_assoc (a b c : Ordering) : (a.then b).then c = a.then (b.then c) := by
  cases a <;> rfl

theorem oriented_lt_iff {α : Type*} (cmp : α → α → Ordering) [Std.OrientedCmp cmp] (a b : α) :
    cmp a b = .lt ↔ cmp b a = .gt := by
  rw [Std.OrientedCmp.eq_swap (cmp := cmp) (a := a) (b := b)]
  cases cmp b a <;> simp [Ordering.swap]

theorem oriented_self {α : Type*} (cmp : α → α → Ordering) [Std.OrientedCmp cmp] (a : α) :
    cmp a a = .eq := by
  have h := Std.OrientedCmp.eq_swap (cmp := cmp) (a := a) (b := a)
  cases hc : cmp a a <;> rw [hc] at h <;> simp_all [Ordering.swap]

theorem firstDifference_compare_lt_iff (a b : List ℕ → ℕ) :
    FirstDifferenceOutcome (fun p o => compare (a p) (b p) = o) .lt ↔
      FirstDifferenceOutcome (fun p o => compare (b p) (a p) = o) .gt := by
  simp only [FirstDifferenceOutcome]
  constructor
  · rintro ⟨p, hp, he⟩
    exact ⟨p, compare_gt_iff_gt.2 (compare_lt_iff_lt.1 hp),
      fun e h => compare_eq_iff_eq.2 (compare_eq_iff_eq.1 (he e h)).symm⟩
  · rintro ⟨p, hp, he⟩
    exact ⟨p, compare_lt_iff_lt.2 (compare_gt_iff_gt.1 hp),
      fun e h => compare_eq_iff_eq.2 (compare_eq_iff_eq.1 (he e h)).symm⟩

theorem firstDifference_compare_eq_not_gt (a b : List ℕ → ℕ)
    (heq : FirstDifferenceOutcome (fun p o => compare (a p) (b p) = o) .eq)
    (hgt : FirstDifferenceOutcome (fun p o => compare (a p) (b p) = o) .gt) : False := by
  simp only [FirstDifferenceOutcome] at heq hgt
  obtain ⟨p, hp, _⟩ := hgt
  rw [heq p] at hp
  cases hp

theorem firstDifference_compare_eq_not_lt (a b : List ℕ → ℕ)
    (heq : FirstDifferenceOutcome (fun p o => compare (a p) (b p) = o) .eq)
    (hlt : FirstDifferenceOutcome (fun p o => compare (a p) (b p) = o) .lt) : False := by
  simp only [FirstDifferenceOutcome] at heq hlt
  obtain ⟨p, hp, _⟩ := hlt
  rw [heq p] at hp
  cases hp

theorem firstDifference_compare_self_iff (a : List ℕ → ℕ) (o : Ordering) :
    FirstDifferenceOutcome (fun p o => compare (a p) (a p) = o) o ↔ Ordering.eq = o := by
  have hself : ∀ p, compare (a p) (a p) = .eq := fun p => compare_eq_iff_eq.2 rfl
  cases o with
  | lt =>
      simp only [FirstDifferenceOutcome]
      constructor
      · rintro ⟨p, hp, _⟩
        rw [hself] at hp
        cases hp
      · intro h
        cases h
  | eq => exact ⟨fun _ => rfl, fun _ => hself⟩
  | gt =>
      simp only [FirstDifferenceOutcome]
      constructor
      · rintro ⟨p, hp, _⟩
        rw [hself] at hp
        cases hp
      · intro h
        cases h

/-- Eight production values chained in rule order. -/
def chain8 (d : SequenceRule → Ordering) : Ordering :=
  (d .rule1aAtomicNumber).then ((d .rule1bDuplicateNodeProximity).then ((d .rule2AtomicMass).then
    ((d .rule3DoubleBondGeometry).then ((d .rule4aStereogenicUnitKind).then
      ((d .rule4bLikeUnlikeDescriptorPairs).then ((d .rule4cPseudoasymmetricDescriptor).then
        (d .rule5EnantiomorphicDescriptor)))))))

theorem before_of_rank {e r : SequenceRule} (h : e.rank < r.rank) : e.Before r := h

theorem not_before_of_rank {e r : SequenceRule} (h : ¬ e.rank < r.rank) : ¬ e.Before r := h

theorem ne_rule6_of_before {e r : SequenceRule} (h6 : r ≠ .rule6ReferencePromotion)
    (h : e.Before r) : e ≠ .rule6ReferencePromotion := by
  rintro rfl
  cases r <;> first | exact absurd rfl h6 | exact absurd h (not_before_of_rank (by decide))

theorem chain8_eq_gt_iff (d : SequenceRule → Ordering) :
    chain8 d = .gt ↔ ∃ r, r ≠ .rule6ReferencePromotion ∧ (∀ e, e.Before r → d e = .eq) ∧
      d r = .gt := by
  constructor
  · intro h
    simp only [chain8, then_eq_gt_iff] at h
    rcases h with h | ⟨h1, h | ⟨h2, h | ⟨h3, h | ⟨h4, h | ⟨h5, h | ⟨h6, h | ⟨h7, h⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨.rule1aAtomicNumber, by decide, fun e he => by
        cases e <;> exact absurd he (not_before_of_rank (by decide)), h⟩
    · exact ⟨.rule1bDuplicateNodeProximity, by decide, fun e he => by
        cases e <;> first | exact absurd he (not_before_of_rank (by decide)) | assumption, h⟩
    · exact ⟨.rule2AtomicMass, by decide, fun e he => by
        cases e <;> first | exact absurd he (not_before_of_rank (by decide)) | assumption, h⟩
    · exact ⟨.rule3DoubleBondGeometry, by decide, fun e he => by
        cases e <;> first | exact absurd he (not_before_of_rank (by decide)) | assumption, h⟩
    · exact ⟨.rule4aStereogenicUnitKind, by decide, fun e he => by
        cases e <;> first | exact absurd he (not_before_of_rank (by decide)) | assumption, h⟩
    · exact ⟨.rule4bLikeUnlikeDescriptorPairs, by decide, fun e he => by
        cases e <;> first | exact absurd he (not_before_of_rank (by decide)) | assumption, h⟩
    · exact ⟨.rule4cPseudoasymmetricDescriptor, by decide, fun e he => by
        cases e <;> first | exact absurd he (not_before_of_rank (by decide)) | assumption, h⟩
    · exact ⟨.rule5EnantiomorphicDescriptor, by decide, fun e he => by
        cases e <;> first | exact absurd he (not_before_of_rank (by decide)) | assumption, h⟩
  · rintro ⟨r, h6, hpre, hr⟩
    unfold chain8
    cases r with
    | rule1aAtomicNumber => rw [hr]; rfl
    | rule1bDuplicateNodeProximity =>
        rw [hpre .rule1aAtomicNumber (before_of_rank (by decide)), hr]; rfl
    | rule2AtomicMass =>
        rw [hpre .rule1aAtomicNumber (before_of_rank (by decide)), hpre .rule1bDuplicateNodeProximity (before_of_rank (by decide)),
          hr]; rfl
    | rule3DoubleBondGeometry =>
        rw [hpre .rule1aAtomicNumber (before_of_rank (by decide)), hpre .rule1bDuplicateNodeProximity (before_of_rank (by decide)),
          hpre .rule2AtomicMass (before_of_rank (by decide)), hr]; rfl
    | rule4aStereogenicUnitKind =>
        rw [hpre .rule1aAtomicNumber (before_of_rank (by decide)), hpre .rule1bDuplicateNodeProximity (before_of_rank (by decide)),
          hpre .rule2AtomicMass (before_of_rank (by decide)), hpre .rule3DoubleBondGeometry (before_of_rank (by decide)), hr]; rfl
    | rule4bLikeUnlikeDescriptorPairs =>
        rw [hpre .rule1aAtomicNumber (before_of_rank (by decide)), hpre .rule1bDuplicateNodeProximity (before_of_rank (by decide)),
          hpre .rule2AtomicMass (before_of_rank (by decide)), hpre .rule3DoubleBondGeometry (before_of_rank (by decide)),
          hpre .rule4aStereogenicUnitKind (before_of_rank (by decide)), hr]; rfl
    | rule4cPseudoasymmetricDescriptor =>
        rw [hpre .rule1aAtomicNumber (before_of_rank (by decide)), hpre .rule1bDuplicateNodeProximity (before_of_rank (by decide)),
          hpre .rule2AtomicMass (before_of_rank (by decide)), hpre .rule3DoubleBondGeometry (before_of_rank (by decide)),
          hpre .rule4aStereogenicUnitKind (before_of_rank (by decide)),
          hpre .rule4bLikeUnlikeDescriptorPairs (before_of_rank (by decide)), hr]; rfl
    | rule5EnantiomorphicDescriptor =>
        rw [hpre .rule1aAtomicNumber (before_of_rank (by decide)), hpre .rule1bDuplicateNodeProximity (before_of_rank (by decide)),
          hpre .rule2AtomicMass (before_of_rank (by decide)), hpre .rule3DoubleBondGeometry (before_of_rank (by decide)),
          hpre .rule4aStereogenicUnitKind (before_of_rank (by decide)),
          hpre .rule4bLikeUnlikeDescriptorPairs (before_of_rank (by decide)),
          hpre .rule4cPseudoasymmetricDescriptor (before_of_rank (by decide)), hr]; rfl
    | rule6ReferencePromotion => exact absurd rfl h6

theorem chain8_eq_eq_iff (d : SequenceRule → Ordering) :
    chain8 d = .eq ↔ ∀ r, r ≠ .rule6ReferencePromotion → d r = .eq := by
  simp only [chain8, then_eq_eq_iff]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ r hr
    cases r <;> first | assumption | exact absurd rfl hr
  · intro h
    exact ⟨h _ (by decide), h _ (by decide), h _ (by decide), h _ (by decide), h _ (by decide),
      h _ (by decide), h _ (by decide), h _ (by decide)⟩

variable {Atom Unit : Type} [Fintype Atom] [DecidableEq Atom]
  (problem : Problem Atom Unit) (descriptorMap : DescriptorMap Unit) (unit : Unit) (i j : Fin 4)
  (d : SequenceRule → Ordering)

/-- The characterization obligation: once every earlier production value ties, the declarative
rule outcome is the production value. -/
def Characterizes : Prop :=
  ∀ r, r ≠ .rule6ReferencePromotion → (∀ e, e.Before r → d e = .eq) →
    ∀ o, problem.RuleOutcome descriptorMap r unit i j o ↔ d r = o

variable {problem descriptorMap unit i j d}

theorem prefix_of_d (hchar : Characterizes problem descriptorMap unit i j d) {r : SequenceRule}
    (h6 : r ≠ .rule6ReferencePromotion) (hd : ∀ e, e.Before r → d e = .eq) :
    ∀ e, e.Before r → problem.RuleOutcome descriptorMap e unit i j .eq := by
  intro e he
  exact (hchar e (ne_rule6_of_before h6 he)
    (fun e' he' => hd e' (SequenceRule.before_trans he' he)) .eq).2 (hd e he)

theorem prefix_of_ruleOutcome (hchar : Characterizes problem descriptorMap unit i j d)
    {r : SequenceRule} (h6 : r ≠ .rule6ReferencePromotion)
    (hP : ∀ e, e.Before r → problem.RuleOutcome descriptorMap e unit i j .eq) :
    ∀ e, e.Before r → d e = .eq := by
  suffices H : ∀ n, ∀ e : SequenceRule, e.rank = n → e.Before r → d e = .eq from
    fun e he => H _ e rfl he
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro e hen he
      exact (hchar e (ne_rule6_of_before h6 he)
        (fun e' he' => ih e'.rank (by rw [← hen]; exact he') e' rfl
          (SequenceRule.before_trans he' he)) .eq).1 (hP e he)

/-- **Strict priority is the first decisive production value.** -/
theorem higher_iff_chain8 (hchar : Characterizes problem descriptorMap unit i j d)
    (h6 : ∀ o, ¬ problem.RuleOutcome descriptorMap .rule6ReferencePromotion unit i j o) :
    problem.Higher descriptorMap unit i j ↔ chain8 d = .gt := by
  rw [chain8_eq_gt_iff]
  constructor
  · rintro ⟨r, htie, hgt⟩
    have hr6 : r ≠ .rule6ReferencePromotion := by
      rintro rfl
      exact h6 _ hgt
    have hd := prefix_of_ruleOutcome hchar hr6 htie
    exact ⟨r, hr6, hd, (hchar r hr6 hd .gt).1 hgt⟩
  · rintro ⟨r, hr6, hd, hr⟩
    exact ⟨r, prefix_of_d hchar hr6 hd, (hchar r hr6 hd .gt).2 hr⟩

/-- **An ordinary tie is a tie of every production value.** -/
theorem tied_iff_chain8 (hchar : Characterizes problem descriptorMap unit i j d) :
    (∀ r, r ≠ .rule6ReferencePromotion → problem.RuleOutcome descriptorMap r unit i j .eq) ↔
      chain8 d = .eq := by
  rw [chain8_eq_eq_iff]
  constructor
  · intro h r hr
    exact (hchar r hr (prefix_of_ruleOutcome hchar hr (fun e he => h e
      (ne_rule6_of_before hr he))) .eq).1 (h r hr)
  · intro h r hr
    exact (hchar r hr (fun e he => h e (ne_rule6_of_before hr he)) .eq).2 (h r hr)

end EightRuleAssembly

/-! ## The physical root -/

namespace Rule4aTableBridge
namespace ActualCentrePhysicalSetup

open CertifiedLocalizedCIPInput
open CertifiedLocalizedCIPInput.OriginalRootArm
open RootedTetrahedralBranchSymmetry
open EightRuleAssembly

variable {input : LocalizedUniversalReference.Input} (S : ActualCentrePhysicalSetup input)

/-- The specialized molecular problem of the input, with a given orientation judgment. -/
abbrev declProblem
    (orientation : DetectedOccurrence input.certified.moleculeGraph → Equiv.Perm (Fin 4) →
      Descriptor → Prop) :=
  multiReferenceProblem input.certified.moleculeGraph input.certified.localizedDetectedFrame
    orientation

/-- The actual generated descriptor map. -/
abbrev declMap : DescriptorMap (DetectedOccurrence input.certified.moleculeGraph) :=
  actualReferenceDescriptorMap input

/-- The root unit. -/
abbrev declUnit : DetectedOccurrence input.certified.moleculeGraph :=
  input.certified.topUnit S.center

/-- The ligand graph read on the stage-`.rule4a` arm. -/
abbrev armG (ℓ : Fin 4) : RootedDigraph input.certified.Atom := armGraph (S.arm4a ℓ)

abbrev pW (ℓ m : Fin 4) : ℕ := pairWidth (S.armG ℓ) (S.armG m)

abbrev pH (ℓ m : Fin 4) : ℕ := pairHeight (S.armG ℓ) (S.armG m)

theorem admissible_arm
    (orientation : DetectedOccurrence input.certified.moleculeGraph → Equiv.Perm (Fin 4) →
      Descriptor → Prop) (ℓ : Fin 4) :
    (declProblem orientation).admissibleExpansion S.declUnit ℓ (S.armG ℓ) :=
  (S.arm4a ℓ).faithful

theorem width_le_pW_left (ℓ m : Fin 4) : (S.armG ℓ).width ≤ S.pW ℓ m := le_max_left _ _
theorem width_le_pW_right (ℓ m : Fin 4) : (S.armG m).width ≤ S.pW ℓ m := le_max_right _ _
theorem height_le_pH_left (ℓ m : Fin 4) : (S.armG ℓ).height ≤ S.pH ℓ m := le_max_left _ _
theorem height_le_pH_right (ℓ m : Fin 4) : (S.armG m).height ≤ S.pH ℓ m := le_max_right _ _

/-! ### Production columns -/

def c1a (ℓ m : Fin 4) : Ordering :=
  OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
    (S.arm4a ℓ).key.constitutional.rule1a (S.arm4a m).key.constitutional.rule1a

def c1b (ℓ m : Fin 4) : Ordering :=
  OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b
    (S.arm4a ℓ).key.constitutional.rule1b (S.arm4a m).key.constitutional.rule1b

def c2 (ℓ m : Fin 4) : Ordering :=
  OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
    (S.arm4a ℓ).key.constitutional.rule2 (S.arm4a m).key.constitutional.rule2

def cdesc (ℓ m : Fin 4) : Ordering :=
  OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
    (S.arm4a ℓ).key.descriptor (S.arm4a m).key.descriptor

/-- The compound comparison after the Rule-4a key: reference count, Rule-4b readings, Rule-4c
readings, in outcome order. -/
def c4b (ℓ m : Fin 4) : Ordering :=
  compareLex (Ordering.byKey (fun key => key.referenceCountPriority) compare)
    (compareLex
      (Ordering.byKey (fun key => key.readings) input.certified.compareLocalizedRerootCompoundRule4bReadings)
      (Ordering.byKey (fun key => key.readings)
        input.certified.compareLocalizedRerootCompoundRule4cReadings))
    (input.certified.outcomeOrdered (S.slotKey ℓ).prior)
    (input.certified.outcomeOrdered (S.slotKey m).prior)

/-- The Rule-5 comparison of the ordered readings under the common reference `R`. -/
def c5 (ℓ m : Fin 4) : Ordering :=
  input.certified.compareLocalizedRerootCompoundRule5Readings .R
    (input.certified.outcomeOrdered45 (S.slotKey ℓ)).rule5Readings
    (input.certified.outcomeOrdered45 (S.slotKey m)).rule5Readings

/-- The production values in rule order (Rules 3 and 4c are inactive on this domain). -/
def prodValue (ℓ m : Fin 4) : SequenceRule → Ordering
  | .rule1aAtomicNumber => S.c1a ℓ m
  | .rule1bDuplicateNodeProximity => S.c1b ℓ m
  | .rule2AtomicMass => S.c2 ℓ m
  | .rule3DoubleBondGeometry => .eq
  | .rule4aStereogenicUnitKind => S.cdesc ℓ m
  | .rule4bLikeUnlikeDescriptorPairs => S.c4b ℓ m
  | .rule4cPseudoasymmetricDescriptor => .eq
  | .rule5EnantiomorphicDescriptor => S.c5 ℓ m
  | .rule6ReferencePromotion => .eq

theorem constitutional_compare_eq (ℓ m : Fin 4) :
    OfficialRuleMajorKey.compare (S.arm4a ℓ).key.constitutional (S.arm4a m).key.constitutional =
      (S.c1a ℓ m).then ((S.c1b ℓ m).then (S.c2 ℓ m)) := rfl

theorem rule4aKey_compare_eq (ℓ m : Fin 4) :
    input.certified.compareLocalizedRerootCumulativeRule45Keys (S.slotKey ℓ).prior.rule4aKey
        (S.slotKey m).prior.rule4aKey =
      ((S.c1a ℓ m).then ((S.c1b ℓ m).then (S.c2 ℓ m))).then (S.cdesc ℓ m) := by
  rw [S.rule4aKey_eq (S.arm4a ℓ), S.rule4aKey_eq (S.arm4a m)]
  rfl

theorem prior_compare_eq (ℓ m : Fin 4) :
    input.certified.compareLocalizedRerootCompoundRule4bcKeys
        (input.certified.outcomeOrdered (S.slotKey ℓ).prior)
        (input.certified.outcomeOrdered (S.slotKey m).prior) =
      (((S.c1a ℓ m).then ((S.c1b ℓ m).then (S.c2 ℓ m))).then (S.cdesc ℓ m)).then (S.c4b ℓ m) := by
  rw [← S.rule4aKey_compare_eq ℓ m]
  rfl

/-- **The production comparison is the chain of the production values.** -/
theorem ordering_eq_chain8 (ℓ m : Fin 4) :
    (S.orderedRootComparison ℓ m).ordering = chain8 (S.prodValue ℓ m) := by
  unfold orderedRootComparison
  rw [compareLocalizedRerootCompoundThroughRule5_ordering]
  have h : input.certified.compareLocalizedRerootCompoundRule45Keys
      (input.certified.outcomeOrdered45 (S.slotKey ℓ))
      (input.certified.outcomeOrdered45 (S.slotKey m)) =
        (input.certified.compareLocalizedRerootCompoundRule4bcKeys
          (input.certified.outcomeOrdered (S.slotKey ℓ).prior)
          (input.certified.outcomeOrdered (S.slotKey m).prior)).then (S.c5 ℓ m) := rfl
  rw [h, S.prior_compare_eq ℓ m]
  simp only [then_assoc]
  rfl

/-! ### Rules 1a, 1b, 2 -/

theorem ruleOutcome_constitutional_iff
    (orientation : DetectedOccurrence input.certified.moleculeGraph → Equiv.Perm (Fin 4) →
      Descriptor → Prop) (rule : ConstitutionalRule) (ℓ m : Fin 4) (o : Ordering) :
    (declProblem orientation).RuleOutcome (actualReferenceDescriptorMap input) rule.toSequenceRule S.declUnit ℓ m o ↔
      input.certified.localizedConstitutionalProblemData.withCanonicalAddressing.toProblem.RuleOutcome
        (fun _ => none) rule.toSequenceRule S.center ℓ m o := by
  cases rule <;> exact Iff.rfl

variable (orientation : DetectedOccurrence input.certified.moleculeGraph → Equiv.Perm (Fin 4) →
  Descriptor → Prop)

theorem ruleOutcome_1a_iff (ℓ m : Fin 4) (o : Ordering) :
    (declProblem orientation).RuleOutcome (actualReferenceDescriptorMap input) .rule1aAtomicNumber S.declUnit ℓ m o ↔
      S.c1a ℓ m = o :=
  (S.ruleOutcome_constitutional_iff orientation .rule1aAtomicNumber ℓ m o).trans
    (ruleOutcome_rule1a_iff_compare (S.arm4a ℓ) (S.arm4a m) _ o)

theorem ruleOutcome_1b_iff (ℓ m : Fin 4) (h1a : S.c1a ℓ m = .eq) (o : Ordering) :
    (declProblem orientation).RuleOutcome (actualReferenceDescriptorMap input) .rule1bDuplicateNodeProximity S.declUnit ℓ m
        o ↔ S.c1b ℓ m = o :=
  (S.ruleOutcome_constitutional_iff orientation .rule1bDuplicateNodeProximity ℓ m o).trans
    (ruleOutcome_rule1b_iff_compare (S.arm4a ℓ) (S.arm4a m) _ h1a o)

theorem ruleOutcome_2_iff (ℓ m : Fin 4) (h1a : S.c1a ℓ m = .eq) (o : Ordering) :
    (declProblem orientation).RuleOutcome (actualReferenceDescriptorMap input) .rule2AtomicMass S.declUnit ℓ m o ↔
      S.c2 ℓ m = o :=
  (S.ruleOutcome_constitutional_iff orientation .rule2AtomicMass ℓ m o).trans
    (ruleOutcome_rule2_iff_compare (S.arm4a ℓ) (S.arm4a m) _ h1a o)

/-! ### Rule 3 -/

theorem ruleKey_eq_of_const (ℓ m : Fin 4)
    (hconst : (S.c1a ℓ m).then ((S.c1b ℓ m).then (S.c2 ℓ m)) = .eq) :
    ruleKey input.certified.moleculeGraph (S.armG ℓ) (S.pW ℓ m) (S.pH ℓ m) (S.armG ℓ).root =
      ruleKey input.certified.moleculeGraph (S.armG m) (S.pW ℓ m) (S.pH ℓ m) (S.armG m).root := by
  have h := arm_compare_eq_compare_vector (S.arm4a ℓ) (S.arm4a m) (S.width_le_pW_left ℓ m)
    (S.height_le_pH_left ℓ m) (S.width_le_pW_right ℓ m) (S.height_le_pH_right ℓ m)
  rw [S.constitutional_compare_eq, hconst] at h
  exact (listKey_compare_eq_iff _ _).1 h.symm

theorem ruleOutcome_3_iff (ℓ m : Fin 4)
    (hconst : (S.c1a ℓ m).then ((S.c1b ℓ m).then (S.c2 ℓ m)) = .eq) (o : Ordering) :
    (declProblem orientation).RuleOutcome (actualReferenceDescriptorMap input) .rule3DoubleBondGeometry S.declUnit ℓ m o ↔
      Ordering.eq = o := by
  rw [ruleOutcome_iff_judgment _ _ orientation _ _ (by decide) (by decide) _
    (S.admissible_arm orientation ℓ) (S.admissible_arm orientation m)]
  have hbot : ∀ (G : RootedDigraph input.certified.Atom) (node : G.Node),
      stereoLabel G (rankEvidence input.certified.moleculeGraph (actualReferenceDescriptorMap input) S.declUnit G)
        .rule3DoubleBondGeometry node = ⊥ := fun G node =>
    rule4aOnly_rankEvidence_of_simpleBonded S.singleBonded _ _ G _ (by decide) node
  have hkey : ligandRule3Key input.certified.moleculeGraph (actualReferenceDescriptorMap input) S.declUnit (S.armG ℓ)
      (S.pW ℓ m) (S.pH ℓ m) =
        ligandRule3Key input.certified.moleculeGraph (actualReferenceDescriptorMap input) S.declUnit (S.armG m)
          (S.pW ℓ m) (S.pH ℓ m) :=
    constComponent_eq_of_ruleKey_eq input.certified.moleculeGraph _ _ _ ⊥ (hbot _) (hbot _) _ _
      (S.ruleKey_eq_of_const ℓ m hconst)
  show compare _ _ = o ↔ _
  rw [hkey, (key_compare_eq_iff _ _).2 rfl]

/-! ### Rule 4a -/

theorem represents4a_pair (ℓ : Fin 4) {W D : ℕ} (hW : (S.armG ℓ).width ≤ W)
    (hD : (S.armG ℓ).height ≤ D) :
    Represents4a W D
      (ligandRule4aKey input.certified.moleculeGraph (actualReferenceDescriptorMap input) S.declUnit (S.armG ℓ) W D)
      (S.arm4a ℓ).key :=
  (arm_node_bridge4a (S.arm4a ℓ) (S.armReadback4a ℓ) hW hD (armGraph (S.arm4a ℓ)).root
    (S.arm4a ℓ).tree (S.arm4a ℓ).key (S.arm4a ℓ).trace
    (by
      change (S.arm4a ℓ).tree.decoratedSubtreeAt? [] = some (S.arm4a ℓ).tree
      rw [LocalizedCumulativeDecoratedTree.decoratedSubtreeAt?])).2

theorem ruleOutcome_4a_iff (ℓ m : Fin 4)
    (hconst : (S.c1a ℓ m).then ((S.c1b ℓ m).then (S.c2 ℓ m)) = .eq) (o : Ordering) :
    (declProblem orientation).RuleOutcome (actualReferenceDescriptorMap input) .rule4aStereogenicUnitKind S.declUnit ℓ m o ↔
      S.cdesc ℓ m = o := by
  rw [ruleOutcome_iff_judgment _ _ orientation _ _ (by decide) (by decide) _
    (S.admissible_arm orientation ℓ) (S.admissible_arm orientation m)]
  have h1a : S.c1a ℓ m = .eq := ((then_eq_eq_iff _ _).1 hconst).1
  have h := compare_descriptor_eq_compare_key (S.arm4a ℓ).tableMatch (S.arm4a m).tableMatch
    (S.arm4a ℓ).realizes (S.arm4a m).realizes h1a
    (ordinaryKey_stereo_wellShaped input.certified.moleculeGraph (S.armG ℓ)
      (rankEvidence input.certified.moleculeGraph (actualReferenceDescriptorMap input) S.declUnit (S.armG ℓ))
      (S.pW ℓ m) (S.pH ℓ m) .rule4aStereogenicUnitKind (S.armG ℓ).root)
    (ordinaryKey_stereo_wellShaped input.certified.moleculeGraph (S.armG m)
      (rankEvidence input.certified.moleculeGraph (actualReferenceDescriptorMap input) S.declUnit (S.armG m))
      (S.pW ℓ m) (S.pH ℓ m) .rule4aStereogenicUnitKind (S.armG m).root)
    (S.represents4a_pair ℓ (S.width_le_pW_left ℓ m) (S.height_le_pH_left ℓ m))
    (S.represents4a_pair m (S.width_le_pW_right ℓ m) (S.height_le_pH_right ℓ m))
  show compare _ _ = o ↔ _
  unfold cdesc
  rw [h]
  rfl

/-! ### Rule 4b -/

theorem ruleOutcome_4b_iff (ℓ m : Fin 4)
    (h4a : ((S.c1a ℓ m).then ((S.c1b ℓ m).then (S.c2 ℓ m))).then (S.cdesc ℓ m) = .eq)
    (o : Ordering) :
    (declProblem orientation).RuleOutcome (actualReferenceDescriptorMap input) .rule4bLikeUnlikeDescriptorPairs S.declUnit ℓ m
        o ↔ S.c4b ℓ m = o := by
  rw [ruleOutcome_iff_judgment _ _ orientation _ _ (by decide) (by decide) _
    (S.admissible_arm orientation ℓ) (S.admissible_arm orientation m)]
  have tie4a := (S.rule4aKey_compare_eq ℓ m).trans h4a
  have h := S.compound_eq_signatureCompare (S.arm4a ℓ) (S.arm4a m) (S.width_le_pW_left ℓ m)
    (S.height_le_pH_left ℓ m) (S.width_le_pW_right ℓ m) (S.height_le_pH_right ℓ m) tie4a
  rw [S.prior_compare_eq ℓ m, h4a] at h
  show signatureCompare _ _ = o ↔ _
  rw [← h]
  rfl

/-! ### Rule 4c -/

/-- **No pseudoasymmetric descriptor is read at any node of a ligand graph.** -/
theorem arm4a_noPseudo (ℓ : Fin 4) :
    ∀ (node : (S.armG ℓ).Node) (value : Descriptor),
      occurrenceReading input.certified.moleculeGraph (actualReferenceDescriptorMap input) S.declUnit (S.armG ℓ) node =
          .descriptor value → value.pseudoSense = none := by
  intro node value hread
  obtain ⟨actual, lookup, hlabel, _⟩ := molecularReader_arm_observations (actualReferenceDescriptorMap input)
    (ActualReaderPhysicalBranchInverse.topTarget input S.c) (S.arm4a ℓ)
    ((ActualReaderPhysicalBranchInverse.topTarget_root input S.c).trans S.hcenter.symm)
    (ActualReaderPhysicalBranchInverse.topTarget_address input S.c) S.singleBonded S.acyclic node
  have hread' := LocalizedCumulativeDecoratedTree.subtreeAt?_node_label_eq_read
    (S.arm4a ℓ).realizes lookup
  have hreach := subtreeAt?_source_reachable (S.arm4a ℓ).realizes lookup
  rw [(S.arm4a ℓ).source, ← S.cursorAt_slot ℓ] at hreach
  have hnp := physicalReader_noPseudo (S.slotSetup ℓ) actual.source (by
    rw [ActualSlotPhysicalSetup.tree_source]
    exact hreach)
  change LocalizedNoPseudoLabel
    (ActualReaderPhysicalBranchInverse.dependencyReader input S.c actual.source) at hnp
  rw [← S.read_eq] at hnp
  change LocalizedNoPseudoLabel (S.read actual.source) at hnp
  rw [← hread', hlabel, hread] at hnp
  cases value <;> first | rfl | exact hnp.elim

/-- The present scalar zero: the Rule-4c label of a node without a pseudoasymmetric reading. -/
def rule4cZero : StereoLabel :=
  ((encodeHierarchy id (singleEntry 0) : StereoCode) : StereoLabel)

theorem rule4cLabel_eq (ℓ : Fin 4) (node : (S.armG ℓ).Node) :
    stereoLabel (S.armG ℓ)
        (molecularEvidence input.certified.moleculeGraph (actualReferenceDescriptorMap input) S.declUnit (S.armG ℓ))
        .rule4cPseudoasymmetricDescriptor node = rule4cZero := by
  have havail := (S.armReadback4a ℓ).available node
  have hnp := S.arm4a_noPseudo ℓ node
  unfold stereoLabel stereoValue
  simp only [Option.bind_some, molecularEvidence]
  unfold rule4cObservation
  cases hread : occurrenceReading input.certified.moleculeGraph (actualReferenceDescriptorMap input) S.declUnit (S.armG ℓ)
      node with
  | unavailable => exact absurd hread havail
  | outsideInventory => rfl
  | unassigned => rfl
  | descriptor value =>
      simp only
      rw [hnp value hread]
      rfl

theorem ruleOutcome_4c_iff (ℓ m : Fin 4)
    (hconst : (S.c1a ℓ m).then ((S.c1b ℓ m).then (S.c2 ℓ m)) = .eq) (o : Ordering) :
    (declProblem orientation).RuleOutcome (actualReferenceDescriptorMap input) .rule4cPseudoasymmetricDescriptor S.declUnit
        ℓ m o ↔ Ordering.eq = o := by
  rw [ruleOutcome_iff_judgment _ _ orientation _ _ (by decide) (by decide) _
    (S.admissible_arm orientation ℓ) (S.admissible_arm orientation m)]
  have hkey : ligandRule4cKey input.certified.moleculeGraph (actualReferenceDescriptorMap input) S.declUnit (S.armG ℓ)
      (S.pW ℓ m) (S.pH ℓ m) =
        ligandRule4cKey input.certified.moleculeGraph (actualReferenceDescriptorMap input) S.declUnit (S.armG m)
          (S.pW ℓ m) (S.pH ℓ m) :=
    constComponent_eq_of_ruleKey_eq input.certified.moleculeGraph _ _ _ rule4cZero
      (S.rule4cLabel_eq ℓ) (S.rule4cLabel_eq m) _ _ (S.ruleKey_eq_of_const ℓ m hconst)
  show compare _ _ = o ↔ _
  rw [hkey, (key_compare_eq_iff _ _).2 rfl]

/-! ### Rule 5 -/

theorem slotEquiv_symm_slot (k : Fin 4) : S.slotEquiv.symm (S.slot k) = k := by
  have : S.slotEquiv k = S.slot k := rfl
  rw [← this, Equiv.symm_apply_apply]

theorem rankRule5Readings_ne_nil {l : List input.certified.LocalizedRerootRule5Reading}
    (h : l ≠ []) : input.certified.rankRule5Readings l ≠ [] := by
  intro h'
  apply h
  have := (input.certified.rankRule5Readings_perm l).length_eq
  rw [h'] at this
  exact List.length_eq_zero_iff.1 this.symm

theorem readings_ne_nil (ℓ : Fin 4) : (S.slotKey ℓ).prior.readings ≠ [] := by
  have hshape := S.readings_shape (S.arm4a ℓ) (S.arm4b ℓ .R) (S.arm4b ℓ .S)
  rcases hsel : S.selection (S.arm4a ℓ) with _ | ⟨_ | _⟩ | _ <;> rw [hsel] at hshape
  · obtain ⟨r, h, _⟩ := hshape; rw [h]; simp
  · obtain ⟨r, h, _⟩ := hshape; rw [h]; simp
  · obtain ⟨r, h, _⟩ := hshape; rw [h]; simp
  · obtain ⟨r, s, h, _⟩ := hshape; rw [h]; simp

theorem exists_head (ℓ : Fin 4) :
    ∃ (u : input.certified.LocalizedRerootRule5Reading)
      (tail : List input.certified.LocalizedRerootRule5Reading),
      (orderedKeys input.certified S.frameKey (S.slot ℓ)).rule5Readings = u :: tail := by
  have hmap := (S.frameKey_readings (S.slot ℓ)).1
  have hne : (S.frameKey (S.slot ℓ)).rule5Readings ≠ [] := by
    intro h
    rw [h] at hmap
    exact S.readings_ne_nil ℓ hmap.symm
  exact List.exists_cons_of_ne_nil (rankRule5Readings_ne_nil hne)

/-- **The declarative head reference is the production head reference.** -/
theorem headSense_eq (ℓ : Fin 4) {u : input.certified.LocalizedRerootRule5Reading} {tail}
    (hu : (orderedKeys input.certified S.frameKey (S.slot ℓ)).rule5Readings = u :: tail)
    {ρ : RS} (hρ : u.prior.reference? = some ρ) :
    headSense (referenceSelection input.certified.moleculeGraph (actualReferenceDescriptorMap input) S.declUnit (S.armG ℓ))
        (readingAt input.certified.moleculeGraph (actualReferenceDescriptorMap input) S.declUnit (S.armG ℓ)
          (S.armG ℓ).width (S.armG ℓ).height) = some (senseOf ρ) := by
  have hmap : (S.slotKey ℓ).rule5Readings.map (·.prior) = (S.slotKey ℓ).prior.readings :=
    (S.frameKey_readings (S.slot ℓ)).1
  have hu' : input.certified.rankRule5Readings (S.slotKey ℓ).rule5Readings = u :: tail := hu
  have hshape := S.readings_shape (S.arm4a ℓ) (S.arm4b ℓ .R) (S.arm4b ℓ .S)
  change headSense (S.selection (S.arm4a ℓ)) _ = _
  rcases hsel : S.selection (S.arm4a ℓ) with _ | ⟨_ | _⟩ | _ <;> rw [hsel] at hshape
  · exfalso
    obtain ⟨r, hr, hrref, _⟩ := hshape
    rw [hr] at hmap
    obtain ⟨u₁, rest, hcons, hu₁, hrest⟩ := List.map_eq_cons_iff.1 hmap
    rw [List.map_eq_nil_iff] at hrest
    subst hrest
    rw [hcons] at hu'
    cases (List.cons.inj hu').1
    rw [hu₁, hrref] at hρ
    cases hρ
  · obtain ⟨r, hr, hrref, _⟩ := hshape
    rw [hr] at hmap
    obtain ⟨u₁, rest, hcons, hu₁, hrest⟩ := List.map_eq_cons_iff.1 hmap
    rw [List.map_eq_nil_iff] at hrest
    subst hrest
    rw [hcons] at hu'
    cases (List.cons.inj hu').1
    rw [hu₁, hrref] at hρ
    cases hρ
    rfl
  · obtain ⟨r, hr, hrref, _⟩ := hshape
    rw [hr] at hmap
    obtain ⟨u₁, rest, hcons, hu₁, hrest⟩ := List.map_eq_cons_iff.1 hmap
    rw [List.map_eq_nil_iff] at hrest
    subst hrest
    rw [hcons] at hu'
    cases (List.cons.inj hu').1
    rw [hu₁, hrref] at hρ
    cases hρ
    rfl
  · obtain ⟨r, s, hrs, hrref, hsref, hr4b, hs4b⟩ := hshape
    rw [hrs] at hmap
    obtain ⟨u₁, rest, hcons, hu₁, hrest⟩ := List.map_eq_cons_iff.1 hmap
    obtain ⟨u₂, rest', hcons', hu₂, hrest'⟩ := List.map_eq_cons_iff.1 hrest
    rw [List.map_eq_nil_iff] at hrest'
    subst hrest'
    subst hcons'
    rw [hcons] at hu'
    have hobs : input.certified.localizedRerootCumulativeRule45Observable
        (S.slotKey ℓ).prior.rule4aKey =
          input.certified.localizedRerootCumulativeRule45Observable (S.slotKey ℓ).prior.rule4aKey :=
      rfl
    have hW := le_refl (S.armG ℓ).width
    have hD := le_refl (S.armG ℓ).height
    have h4b := S.cmp4b_eq (S.arm4a ℓ) (S.arm4a ℓ) (S.arm4b ℓ .R) (S.arm4b ℓ .S) hobs hW hD hW hD
      r s hr4b hs4b
    have hrmem : r ∈ (S.slotKey ℓ).prior.readings := by rw [hrs]; simp
    have hsmem : s ∈ (S.slotKey ℓ).prior.readings := by rw [hrs]; simp
    have h4c := S.cmp4c_eq_cmp4b hobs hrmem hsmem (by rw [hrref, hsref]; rfl)
    have hcomplete : input.certified.compareRule4bcReadingsComplete r s =
        input.certified.compareLocalizedRerootRule4bcReadingsByRule4b r s := by
      unfold compareRule4bcReadingsComplete compareLex
      cases hb : input.certified.compareLocalizedRerootRule4bcReadingsByRule4b r s with
      | lt => rfl
      | gt => rfl
      | eq =>
          show (Ordering.eq).then _ = _
          show OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
            r.rule4cKey.descriptor s.rule4cKey.descriptor = .eq
          rw [h4c]
          exact hb
    have hrank : input.certified.rankRule5Readings [u₁, u₂] =
        if input.certified.compareRule4bcReadingsComplete u₁.prior u₂.prior = .lt then [u₂, u₁]
        else [u₁, u₂] := rfl
    rw [hrank, hu₁, hu₂, hcomplete, h4b] at hu'
    show some (if compare _ _ = Ordering.lt then DescriptorSense.junior else DescriptorSense.senior) = _
    by_cases hlt : compare
        (readingAt input.certified.moleculeGraph (actualReferenceDescriptorMap input) S.declUnit
          (S.armG ℓ) (S.armG ℓ).width (S.armG ℓ).height DescriptorSense.senior)
        (readingAt input.certified.moleculeGraph (actualReferenceDescriptorMap input) S.declUnit
          (S.armG ℓ) (S.armG ℓ).width (S.armG ℓ).height DescriptorSense.junior) = Ordering.lt
    · have hlt' : compare
          (S.readingOf (S.arm4a ℓ) (S.armG ℓ).width (S.armG ℓ).height (senseOf .R))
          (S.readingOf (S.arm4a ℓ) (S.armG ℓ).width (S.armG ℓ).height (senseOf .S)) = .lt := hlt
      rw [if_pos hlt'] at hu'
      cases (List.cons.inj hu').1
      rw [hu₂, hsref] at hρ
      cases hρ
      rw [if_pos hlt]
      rfl
    · have hlt' : ¬ compare
          (S.readingOf (S.arm4a ℓ) (S.armG ℓ).width (S.armG ℓ).height (senseOf .R))
          (S.readingOf (S.arm4a ℓ) (S.armG ℓ).width (S.armG ℓ).height (senseOf .S)) = .lt := hlt
      rw [if_neg hlt'] at hu'
      cases (List.cons.inj hu').1
      rw [hu₁, hrref] at hρ
      cases hρ
      rw [if_neg hlt]
      rfl

/-- The observation function of ligand `ℓ`'s reading under `ρ`, at its own layout. -/
def observation (ℓ : Fin 4) (ρ : RS) (path : List ℕ) : WithBot StereoLabel :=
  Certificate.CanonicalSphereKey.pathObservationOf (S.armG ℓ).width (S.armG ℓ).height
    (readingAt input.certified.moleculeGraph (actualReferenceDescriptorMap input) S.declUnit (S.armG ℓ) (S.armG ℓ).width
      (S.armG ℓ).height (senseOf ρ)) path

/-- The observation is the reading of the stage-`.rule4b ρ` arm's graph, which represents that
arm's key. -/
theorem observation_eq_encoded4b (ℓ : Fin 4) (ρ : RS) (path : List ℕ) :
    S.observation ℓ ρ path = encoded4b (S.arm4b ℓ ρ).key path := by
  have hW := width_eq_of_faithful input.certified.moleculeGraph S.center.1 _
    (S.arm4b ℓ ρ).faithful (S.arm4a ℓ).faithful
  have hD := height_eq_of_faithful input.certified.moleculeGraph S.center.1 _
    (S.arm4b ℓ ρ).faithful (S.arm4a ℓ).faithful
  have hK := readingAt_eq_of_faithful input.certified.moleculeGraph (actualReferenceDescriptorMap input) S.declUnit
    S.center.1 _ (S.arm4b ℓ ρ).faithful (S.arm4a ℓ).faithful (S.armG ℓ).width (S.armG ℓ).height
    (senseOf ρ)
  have hrep := arm_root_represents4b (S.arm4b ℓ ρ) (S.armReadback4b (S.arm4b ℓ ρ)) path
  unfold observation
  rw [← hK, ← hW, ← hD]
  exact hrep

theorem addressBefore_iff (earlier later : List ℕ) :
    Certificate.CanonicalSphereKey.AddressBefore earlier later ↔
      HierarchyAddressBefore earlier later := by
  unfold Certificate.CanonicalSphereKey.AddressBefore HierarchyAddressBefore HierarchyAddressKey
  rw [List.cons_lt_cons_iff]

theorem code_eq_seniorObservation (ρ : RS) :
    (((code (if ρ = RS.R then 1 else 0) : StereoCode) : StereoLabel) : WithBot StereoLabel) =
      seniorObservation (senseOf ρ) := by
  cases ρ <;> rfl

theorem not_code_iff (ℓ : Fin 4) (ρ : RS) (path : List ℕ) :
    (∀ b : ℕ, S.observation ℓ ρ path ≠
        (((code b : StereoCode) : StereoLabel) : WithBot StereoLabel)) ↔
      S.observation ℓ ρ path ≠ likeObservation ∧ S.observation ℓ ρ path ≠ unlikeObservation := by
  constructor
  · intro h
    exact ⟨h 1, h 0⟩
  · rintro ⟨hl, hu⟩ b hb
    have hle : b ≤ 1 := by
      rw [S.observation_eq_encoded4b] at hb
      have := (encoded4b_eq_code_iff (S.arm4b ℓ ρ).tableMatch path b).1 hb
      rw [← this.2]
      exact tableValue_scalar4b_le_one (S.arm4b ℓ ρ).tableMatch path
    interval_cases b
    · exact hu hb
    · exact hl hb

section Distinct

variable (distinct : ∀ i j : Fin 4, i ≠ j →
  ¬ ProperTransport input.certified.detectedMultiCenterMolecule S.cfg S.c i j)
include distinct

theorem head_reference {ℓ m : Fin 4} (hℓm : ℓ ≠ m)
    (tie : priorKeyTie input.certified (orderedKeys input.certified S.frameKey) (S.slot ℓ)
      (S.slot m))
    {u : input.certified.LocalizedRerootRule5Reading} {tailU}
    (hu : (orderedKeys input.certified S.frameKey (S.slot ℓ)).rule5Readings = u :: tailU)
    {v : input.certified.LocalizedRerootRule5Reading} {tailV}
    (hv : (orderedKeys input.certified S.frameKey (S.slot m)).rule5Readings = v :: tailV) :
    ∃ ρ : RS, u.prior.reference? = some ρ := by
  have hij : S.slot ℓ ≠ S.slot m := S.slot_injective.ne hℓm
  obtain ⟨_, _, matched⟩ := input.certified.orderedPriorTie_matched _ _ tie
    (S.frameKey_readings (S.slot ℓ)).1 (S.frameKey_readings (S.slot m)).1
  have matched' : List.Forall₂ (fun u v : input.certified.LocalizedRerootRule5Reading =>
      input.certified.compareRule4bcReadingsComplete u.prior v.prior = .eq)
      (orderedKeys input.certified S.frameKey (S.slot ℓ)).rule5Readings
      (orderedKeys input.certified S.frameKey (S.slot m)).rule5Readings := matched
  rw [hu, hv] at matched'
  have hcomplete := (List.forall₂_cons.1 matched').1
  have memU : u ∈ (S.frameKey (S.slot ℓ)).rule5Readings :=
    input.certified.mem_of_mem_rankRule5Readings (by
      rw [show input.certified.rankRule5Readings (S.frameKey (S.slot ℓ)).rule5Readings =
        u :: tailU from hu]
      exact List.mem_cons_self)
  have memV : v ∈ (S.frameKey (S.slot m)).rule5Readings :=
    input.certified.mem_of_mem_rankRule5Readings (by
      rw [show input.certified.rankRule5Readings (S.frameKey (S.slot m)).rule5Readings =
        v :: tailV from hv]
      exact List.mem_cons_self)
  obtain ⟨ρ₁, _, hρ₁, _⟩ := S.matched_classification distinct hij tie memU memV hcomplete
  exact ⟨ρ₁, hρ₁⟩

/-- **Both ligands of a matched pair lay out one observation function.** -/
theorem observation_eq {ℓ m : Fin 4} (hℓm : ℓ ≠ m)
    (tie : priorKeyTie input.certified (orderedKeys input.certified S.frameKey) (S.slot ℓ)
      (S.slot m))
    (tie4a : input.certified.compareLocalizedRerootCumulativeRule45Keys
      (S.slotKey ℓ).prior.rule4aKey (S.slotKey m).prior.rule4aKey = .eq)
    {u : input.certified.LocalizedRerootRule5Reading} {tailU}
    (hu : (orderedKeys input.certified S.frameKey (S.slot ℓ)).rule5Readings = u :: tailU)
    {v : input.certified.LocalizedRerootRule5Reading} {tailV}
    (hv : (orderedKeys input.certified S.frameKey (S.slot m)).rule5Readings = v :: tailV)
    {ρ : RS} (hρ : u.prior.reference? = some ρ) :
    v.prior.reference? = some (RS.swap ρ) ∧
      S.observation m (RS.swap ρ) = S.observation ℓ ρ := by
  have hij : S.slot ℓ ≠ S.slot m := S.slot_injective.ne hℓm
  obtain ⟨memU, memV, hσ, sameTable⟩ := S.head_matched distinct hij tie hu hv hρ
  refine ⟨hσ, ?_⟩
  have keyU := S.rule4bKey_eq_arm4b memU hρ
  have keyV := S.rule4bKey_eq_arm4b memV hσ
  rw [S.slotEquiv_symm_slot] at keyU keyV
  rw [keyU, keyV] at sameTable
  have hobs := S.observable_eq_of_tie tie4a
  have h1a := (compareSparseLayers_compareNat_eq_iff _ _).1
    (S.tied1a_of_observable (S.arm4b ℓ ρ) (S.arm4b m (RS.swap ρ)) hobs)
  funext path
  rw [S.observation_eq_encoded4b, S.observation_eq_encoded4b]
  unfold encoded4b scalar4a scalar4b
  rw [← h1a, ← sameTable]

/-- **Rule 5 at a distinct prior-tied pair.** -/
theorem ruleOutcome_5_gt_iff {ℓ m : Fin 4} (hℓm : ℓ ≠ m)
    (tie : priorKeyTie input.certified (orderedKeys input.certified S.frameKey) (S.slot ℓ)
      (S.slot m))
    (tie4a : input.certified.compareLocalizedRerootCumulativeRule45Keys
      (S.slotKey ℓ).prior.rule4aKey (S.slotKey m).prior.rule4aKey = .eq) :
    MultiReferenceJudgment input.certified.moleculeGraph (actualReferenceDescriptorMap input) S.declUnit
        .rule5EnantiomorphicDescriptor (S.armG ℓ) (S.armG m) .gt ↔ S.c5 ℓ m = .gt := by
  have hij : S.slot ℓ ≠ S.slot m := S.slot_injective.ne hℓm
  obtain ⟨u, tailU, hu⟩ := S.exists_head ℓ
  obtain ⟨v, tailV, hv⟩ := S.exists_head m
  obtain ⟨ρ, hρ⟩ := S.head_reference distinct hℓm tie hu hv
  obtain ⟨hσ, hobsEq⟩ := S.observation_eq distinct hℓm tie tie4a hu hv hρ
  have headL := S.headSense_eq ℓ hu hρ
  have headR := S.headSense_eq m hv hσ
  have hstreamL : ligandRule5Stream input.certified.moleculeGraph (actualReferenceDescriptorMap input) S.declUnit (S.armG ℓ) =
      fun path => seniorityOf (senseOf ρ) (S.observation ℓ ρ path) := by
    funext path
    unfold ligandRule5Stream
    rw [headL]
    rfl
  have hstreamR : ligandRule5Stream input.certified.moleculeGraph (actualReferenceDescriptorMap input) S.declUnit (S.armG m) =
      fun path => seniorityOf (senseOf ρ).mirror (S.observation ℓ ρ path) := by
    funext path
    unfold ligandRule5Stream
    have hmirror : senseOf (RS.swap ρ) = (senseOf ρ).mirror := by cases ρ <;> rfl
    rw [headR, ← hobsEq, ← hmirror]
    rfl
  -- production side
  have hc5 : S.c5 ℓ m = OfficialRuleMajorKey.compareSparseLayers
      compareLocalizedCumulativeRule45Priority u.commonR.descriptor v.commonR.descriptor := by
    unfold c5
    rw [show (input.certified.outcomeOrdered45 (S.slotKey ℓ)).rule5Readings = u :: tailU from hu,
      show (input.certified.outcomeOrdered45 (S.slotKey m)).rule5Readings = v :: tailV from hv,
      input.certified.compareLocalizedRerootCompoundRule5Readings_cons_of_ne .R u v tailU tailV
        (S.head_commonR_ne_eq distinct hij tie hu hv)]
    rfl
  rw [hc5, S.commonR_decision_gt_iff_reading distinct hij tie hu hv hρ, S.slotEquiv_symm_slot]
  simp only [MultiReferenceJudgment, hstreamL, hstreamR]
  rw [seniorityMirror_gt_iff]
  have hobsK : ∀ path, Certificate.CanonicalSphereKey.pathObservationOf
      (armGraph (S.arm4b ℓ ρ)).width (armGraph (S.arm4b ℓ ρ)).height
      (reading input.certified.moleculeGraph (actualReferenceDescriptorMap input)
        (input.certified.topUnit S.center) (armGraph (S.arm4b ℓ ρ)) (senseOf ρ)) path =
        S.observation ℓ ρ path := by
    intro path
    rw [S.observation_eq_encoded4b]
    exact arm_root_represents4b (S.arm4b ℓ ρ) (S.armReadback4b (S.arm4b ℓ ρ)) path
  simp only [hobsK, code_eq_seniorObservation]
  constructor
  · rintro ⟨path, hpath, hearlier⟩
    exact ⟨path, hpath, fun earlier he =>
      (S.not_code_iff ℓ ρ earlier).2 (hearlier earlier ((addressBefore_iff _ _).1 he))⟩
  · rintro ⟨path, hpath, hearlier⟩
    exact ⟨path, hpath, fun earlier he =>
      (S.not_code_iff ℓ ρ earlier).1 (hearlier earlier ((addressBefore_iff _ _).2 he))⟩

theorem c5_eq_head {ℓ m : Fin 4} (hℓm : ℓ ≠ m)
    (tie : priorKeyTie input.certified (orderedKeys input.certified S.frameKey) (S.slot ℓ)
      (S.slot m))
    {u : input.certified.LocalizedRerootRule5Reading} {tailU}
    (hu : (orderedKeys input.certified S.frameKey (S.slot ℓ)).rule5Readings = u :: tailU)
    {v : input.certified.LocalizedRerootRule5Reading} {tailV}
    (hv : (orderedKeys input.certified S.frameKey (S.slot m)).rule5Readings = v :: tailV) :
    S.c5 ℓ m = OfficialRuleMajorKey.compareSparseLayers
      compareLocalizedCumulativeRule45Priority u.commonR.descriptor v.commonR.descriptor := by
  have hij : S.slot ℓ ≠ S.slot m := S.slot_injective.ne hℓm
  unfold c5
  rw [show (input.certified.outcomeOrdered45 (S.slotKey ℓ)).rule5Readings = u :: tailU from hu,
    show (input.certified.outcomeOrdered45 (S.slotKey m)).rule5Readings = v :: tailV from hv,
    input.certified.compareLocalizedRerootCompoundRule5Readings_cons_of_ne .R u v tailU tailV
      (S.head_commonR_ne_eq distinct hij tie hu hv)]
  rfl

/-- **Rule 5 after a prior tie, every outcome.** -/
theorem judgment5_iff {ℓ m : Fin 4}
    (tie : priorKeyTie input.certified (orderedKeys input.certified S.frameKey) (S.slot ℓ)
      (S.slot m))
    (tie4a : input.certified.compareLocalizedRerootCumulativeRule45Keys
      (S.slotKey ℓ).prior.rule4aKey (S.slotKey m).prior.rule4aKey = .eq) (o : Ordering) :
    MultiReferenceJudgment input.certified.moleculeGraph (actualReferenceDescriptorMap input)
        S.declUnit .rule5EnantiomorphicDescriptor (S.armG ℓ) (S.armG m) o ↔ S.c5 ℓ m = o := by
  haveI := input.certified.compareLocalizedRerootCompoundRule5Readings_transCmp .R
  by_cases hℓm : ℓ = m
  · subst hℓm
    have hc : S.c5 ℓ ℓ = .eq :=
      oriented_self (input.certified.compareLocalizedRerootCompoundRule5Readings .R) _
    rw [hc]
    exact firstDifference_compare_self_iff _ o
  · have hij : S.slot ℓ ≠ S.slot m := S.slot_injective.ne hℓm
    have hgt := S.ruleOutcome_5_gt_iff distinct hℓm tie tie4a
    have tie' : priorKeyTie input.certified (orderedKeys input.certified S.frameKey) (S.slot m)
        (S.slot ℓ) :=
      ((S.orderedPriorTie_iff_enantiomorphic distinct (S.slot m) (S.slot ℓ)).2
        (enantiomorphic_symm _ _ _
          ((S.orderedPriorTie_iff_enantiomorphic distinct (S.slot ℓ) (S.slot m)).1
            ⟨hij, tie⟩))).2
    have tie4a' : input.certified.compareLocalizedRerootCumulativeRule45Keys
        (S.slotKey m).prior.rule4aKey (S.slotKey ℓ).prior.rule4aKey = .eq := by
      have h : input.certified.compareLocalizedRerootCompoundRule4bcKeys
          (input.certified.outcomeOrdered (S.slotKey m).prior)
          (input.certified.outcomeOrdered (S.slotKey ℓ).prior) = .eq := tie'
      rw [S.prior_compare_eq m ℓ, then_eq_eq_iff] at h
      rw [S.rule4aKey_compare_eq m ℓ]
      exact h.1
    have hgt' := S.ruleOutcome_5_gt_iff distinct (Ne.symm hℓm) tie' tie4a'
    have hlt : MultiReferenceJudgment input.certified.moleculeGraph
        (actualReferenceDescriptorMap input) S.declUnit .rule5EnantiomorphicDescriptor
        (S.armG ℓ) (S.armG m) .lt ↔ S.c5 ℓ m = .lt :=
      (firstDifference_compare_lt_iff _ _).trans (hgt'.trans
        (oriented_lt_iff (input.certified.compareLocalizedRerootCompoundRule5Readings .R) _ _).symm)
    obtain ⟨u, tailU, hu⟩ := S.exists_head ℓ
    obtain ⟨v, tailV, hv⟩ := S.exists_head m
    have hne : S.c5 ℓ m ≠ .eq := by
      rw [S.c5_eq_head distinct hℓm tie hu hv]
      exact S.head_commonR_ne_eq distinct hij tie hu hv
    cases o with
    | lt => exact hlt
    | gt => exact hgt
    | eq =>
        constructor
        · intro heq
          exfalso
          cases hc : S.c5 ℓ m with
          | eq => exact hne hc
          | lt => exact firstDifference_compare_eq_not_lt _ _ heq (hlt.2 hc)
          | gt => exact firstDifference_compare_eq_not_gt _ _ heq (hgt.2 hc)
        · intro h
          exact absurd h hne

omit distinct in
theorem rule6_never (ℓ m : Fin 4) (o : Ordering) :
    ¬ (declProblem orientation).RuleOutcome (actualReferenceDescriptorMap input)
      .rule6ReferencePromotion S.declUnit ℓ m o := by
  intro h
  obtain ⟨_, hfalse, _⟩ := h (S.armG ℓ) (S.armG m) (S.admissible_arm orientation ℓ)
    (S.admissible_arm orientation m)
  exact hfalse

/-- **Every declarative ordinary outcome is the production value once the earlier values tie.** -/
theorem characterizes (ℓ m : Fin 4) :
    Characterizes (declProblem orientation) (actualReferenceDescriptorMap input) S.declUnit ℓ m
      (S.prodValue ℓ m) := by
  intro r hr6 hpre o
  cases r with
  | rule1aAtomicNumber => exact S.ruleOutcome_1a_iff orientation ℓ m o
  | rule1bDuplicateNodeProximity =>
      exact S.ruleOutcome_1b_iff orientation ℓ m
        (hpre .rule1aAtomicNumber (before_of_rank (by decide))) o
  | rule2AtomicMass =>
      exact S.ruleOutcome_2_iff orientation ℓ m
        (hpre .rule1aAtomicNumber (before_of_rank (by decide))) o
  | rule6ReferencePromotion => exact absurd rfl hr6
  | _ =>
      have e1 : S.c1a ℓ m = .eq := hpre .rule1aAtomicNumber (before_of_rank (by decide))
      have e2 : S.c1b ℓ m = .eq := hpre .rule1bDuplicateNodeProximity (before_of_rank (by decide))
      have e3 : S.c2 ℓ m = .eq := hpre .rule2AtomicMass (before_of_rank (by decide))
      have hconst : (S.c1a ℓ m).then ((S.c1b ℓ m).then (S.c2 ℓ m)) = .eq := by
        rw [e1, e2, e3]; rfl
      first
      | exact S.ruleOutcome_3_iff orientation ℓ m hconst o
      | exact S.ruleOutcome_4a_iff orientation ℓ m hconst o
      | exact S.ruleOutcome_4c_iff orientation ℓ m hconst o
      | (have e4 : S.cdesc ℓ m = .eq := hpre .rule4aStereogenicUnitKind (before_of_rank (by decide))
         have h4a : ((S.c1a ℓ m).then ((S.c1b ℓ m).then (S.c2 ℓ m))).then (S.cdesc ℓ m) = .eq := by
           rw [hconst, e4]; rfl
         first
         | exact S.ruleOutcome_4b_iff orientation ℓ m h4a o
         | (have e5 : S.c4b ℓ m = .eq :=
              hpre .rule4bLikeUnlikeDescriptorPairs (before_of_rank (by decide))
            have tie4a := (S.rule4aKey_compare_eq ℓ m).trans h4a
            have tie : priorKeyTie input.certified (orderedKeys input.certified S.frameKey)
                (S.slot ℓ) (S.slot m) := by
              show input.certified.compareLocalizedRerootCompoundRule4bcKeys
                (input.certified.outcomeOrdered (S.slotKey ℓ).prior)
                (input.certified.outcomeOrdered (S.slotKey m).prior) = .eq
              rw [S.prior_compare_eq ℓ m, h4a, e5]
              rfl
            rw [ruleOutcome_iff_judgment _ _ orientation _ _ (by decide) (by decide) _
              (S.admissible_arm orientation ℓ) (S.admissible_arm orientation m)]
            exact S.judgment5_iff distinct tie tie4a o))

/-! ## The eight-rule connection -/

/-- **`gt` is declarative strict priority.** -/
theorem ordering_eq_gt_iff_higher (ℓ m : Fin 4) :
    (S.orderedRootComparison ℓ m).ordering = .gt ↔
      (declProblem orientation).Higher (actualReferenceDescriptorMap input) S.declUnit ℓ m := by
  rw [S.ordering_eq_chain8]
  exact (higher_iff_chain8 (S.characterizes orientation distinct ℓ m)
    (S.rule6_never orientation ℓ m)).symm

/-- **`lt` is the reverse declarative strict priority.** -/
theorem ordering_eq_lt_iff_higher (ℓ m : Fin 4) :
    (S.orderedRootComparison ℓ m).ordering = .lt ↔
      (declProblem orientation).Higher (actualReferenceDescriptorMap input) S.declUnit m ℓ := by
  have h : (S.orderedRootComparison ℓ m).ordering = .lt ↔
      (S.orderedRootComparison m ℓ).ordering = .gt := by
    unfold orderedRootComparison
    rw [compareLocalizedRerootCompoundThroughRule5_ordering,
      compareLocalizedRerootCompoundThroughRule5_ordering]
    haveI := input.certified.compareLocalizedRerootCompoundRule45Keys_transCmp
    exact oriented_lt_iff _ _ _
  rw [h]
  exact S.ordering_eq_gt_iff_higher orientation distinct m ℓ

/-- **`eq` is a tie of every ordinary rule.** -/
theorem ordering_eq_eq_iff_tied (ℓ m : Fin 4) :
    (S.orderedRootComparison ℓ m).ordering = .eq ↔
      ∀ rule, rule ≠ .rule6ReferencePromotion →
        (declProblem orientation).RuleOutcome (actualReferenceDescriptorMap input) rule
          S.declUnit ℓ m .eq := by
  rw [S.ordering_eq_chain8]
  exact (tied_iff_chain8 (S.characterizes orientation distinct ℓ m)).symm

end Distinct

end ActualCentrePhysicalSetup
end Rule4aTableBridge

end

end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.subtreeAt?_source_reachable
assert_kernel_only TetraStereo.OneCenter.EightRuleAssembly.higher_iff_chain8
assert_kernel_only TetraStereo.OneCenter.EightRuleAssembly.tied_iff_chain8
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.ordering_eq_chain8
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.ruleOutcome_3_iff
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.ruleOutcome_4a_iff
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.ruleOutcome_4b_iff
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.arm4a_noPseudo
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.ruleOutcome_4c_iff
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.headSense_eq
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.ruleOutcome_5_gt_iff
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.judgment5_iff
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.characterizes
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.ordering_eq_gt_iff_higher
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.ordering_eq_lt_iff_higher
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.ordering_eq_eq_iff_tied
