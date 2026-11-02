import TetraStereo.OneCenter.P91DescriptorSyntax

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Independent P-93.4 acyclic configuration semantics

This module captures descriptor-family applicability and naming constraints for acyclic centers,
double bonds, and cumulenes.  Ligand ranking and geometry perception are inputs to these relations;
the module does not call production code to manufacture its reference answers.
-/

namespace BlueBookP93.Acyclic

inductive Descriptor where
  | R | S | r | s
  | E | Z
  | cis | trans
  | M | P
  | Ra | Sa
  deriving DecidableEq, Repr

inductive UnitKind where
  | chiralCenter
  | pseudoasymmetricCenter
  | ordinaryDoubleBond
  | heteroatomDoubleBond
  | evenDoubleBondCumulene
  | oddDoubleBondCumulene
  | nonstereogenic
  deriving DecidableEq, Repr

def DescriptorApplies : UnitKind → Descriptor → Prop
  | .chiralCenter, .R | .chiralCenter, .S => True
  | .pseudoasymmetricCenter, .r | .pseudoasymmetricCenter, .s => True
  | .ordinaryDoubleBond, .E | .ordinaryDoubleBond, .Z => True
  | .ordinaryDoubleBond, .cis | .ordinaryDoubleBond, .trans => True
  | .heteroatomDoubleBond, .E | .heteroatomDoubleBond, .Z => True
  | .evenDoubleBondCumulene, .M | .evenDoubleBondCumulene, .P => True
  | .evenDoubleBondCumulene, .Ra | .evenDoubleBondCumulene, .Sa => True
  | .oddDoubleBondCumulene, .E | .oddDoubleBondCumulene, .Z => True
  | .oddDoubleBondCumulene, .cis | .oddDoubleBondCumulene, .trans => True
  | _, _ => False

theorem nonstereogenic_unit_has_no_descriptor (descriptor : Descriptor) :
    ¬DescriptorApplies .nonstereogenic descriptor := by
  cases descriptor <;> simp [DescriptorApplies]

inductive NomenclatureContext where
  | preferredIUPACName
  | general
  deriving DecidableEq, Repr

def DescriptorRecommended :
    NomenclatureContext → UnitKind → Descriptor → Prop
  | .preferredIUPACName, .chiralCenter, .R
  | .preferredIUPACName, .chiralCenter, .S
  | .preferredIUPACName, .pseudoasymmetricCenter, .r
  | .preferredIUPACName, .pseudoasymmetricCenter, .s
  | .preferredIUPACName, .ordinaryDoubleBond, .E
  | .preferredIUPACName, .ordinaryDoubleBond, .Z
  | .preferredIUPACName, .heteroatomDoubleBond, .E
  | .preferredIUPACName, .heteroatomDoubleBond, .Z
  | .preferredIUPACName, .evenDoubleBondCumulene, .M
  | .preferredIUPACName, .evenDoubleBondCumulene, .P
  | .preferredIUPACName, .oddDoubleBondCumulene, .E
  | .preferredIUPACName, .oddDoubleBondCumulene, .Z => True
  | .general, unit, descriptor => DescriptorApplies unit descriptor
  | _, _, _ => False

theorem even_cumulene_PIN_prefers_helicity (descriptor : Descriptor)
    (recommended : DescriptorRecommended .preferredIUPACName
      .evenDoubleBondCumulene descriptor) :
    descriptor = .M ∨ descriptor = .P := by
  cases descriptor <;> simp_all [DescriptorRecommended]

theorem axial_Ra_Sa_are_general_only :
    DescriptorRecommended .general .evenDoubleBondCumulene .Ra ∧
    ¬DescriptorRecommended .preferredIUPACName .evenDoubleBondCumulene .Ra := by
  constructor <;> simp [DescriptorRecommended, DescriptorApplies]

/-! ## Equivalent axial descriptors for even cumulenes -/

/-- P-92.1.2.2.3 and the paired examples in P-93.4.2.2 identify the two equivalent
descriptor-family spellings for a chirality axis: `Rₐ` corresponds to `M`, while `Sₐ`
corresponds to `P`.  The argument order is the general `Rₐ/Sₐ` spelling followed by the
preferred-IUPAC-name `M/P` spelling.

This relation deliberately concerns axes.  P-92 states the opposite `R/S`--`M/P`
correspondence for stereogenic planes. -/
def EvenCumuleneAxialDescriptorCorrespondence : Descriptor → Descriptor → Prop
  | .Ra, .M | .Sa, .P => True
  | _, _ => False



def preferredEvenCumuleneAxialDescriptor? : Descriptor → Option Descriptor
  | .Ra => some .M
  | .Sa => some .P
  | _ => none

/-- The executable P-93 conversion is exactly the independent axial correspondence relation. -/
theorem preferredEvenCumuleneAxialDescriptor?_eq_some_iff
    (general preferred : Descriptor) :
    preferredEvenCumuleneAxialDescriptor? general = some preferred ↔
      EvenCumuleneAxialDescriptorCorrespondence general preferred := by
  cases general <;> cases preferred <;>
    simp [preferredEvenCumuleneAxialDescriptor?, EvenCumuleneAxialDescriptorCorrespondence]

/-- Every descriptor produced by the P-93.4.2.2 conversion is both applicable to an even
cumulene and recommended for a preferred IUPAC name. -/
theorem preferredEvenCumuleneAxialDescriptor?_recommended
    (general preferred : Descriptor)
    (converted : preferredEvenCumuleneAxialDescriptor? general = some preferred) :
    DescriptorApplies .evenDoubleBondCumulene preferred ∧
      DescriptorRecommended .preferredIUPACName .evenDoubleBondCumulene preferred := by
  cases general <;> cases preferred <;>
    simp_all [preferredEvenCumuleneAxialDescriptor?, DescriptorApplies,
      DescriptorRecommended]

/-- The two P-93.4.2.2 axial spellings are total and unique on the general `Rₐ/Sₐ` family. -/
theorem existsUnique_preferred_even_cumulene_axial_descriptor
    (general : Descriptor) (axialGeneral : general = .Ra ∨ general = .Sa) :
    ∃! preferred,
      EvenCumuleneAxialDescriptorCorrespondence general preferred := by
  rcases axialGeneral with rfl | rfl
  · exact ⟨.M, trivial, by
      intro preferred corresponding
      cases preferred <;> simp_all [EvenCumuleneAxialDescriptorCorrespondence]⟩
  · exact ⟨.P, trivial, by
      intro preferred corresponding
      cases preferred <;> simp_all [EvenCumuleneAxialDescriptorCorrespondence]⟩

/-! ## Planar odd-cumulene `E/Z` assignment

P-91.2.1.2.1 and P-93.4.2.3 treat an odd cumulene as one planar extended double-bond
system.  The highest-priority terminal ligand at each end is compared across that whole system:
the descriptor is `Z` when those two ligands are together and `E` when they are opposite.

The geometry domain and relation below are independent of the production Rule-3 geometry type.
This keeps the final production-to-authority correspondence a proved theorem rather than a
shared implementation definition.
-/

/-- Relative placement of the two independently selected highest-priority terminal ligands of
one planar odd cumulene. -/
inductive OddCumuleneTerminalGeometry where
  | together
  | opposite
  deriving DecidableEq, Repr

/-- Independent P-93.4.2.3 assignment relation for one odd cumulene considered as a single
extended planar unit. -/
def OddCumuleneEZAssignment : OddCumuleneTerminalGeometry → Descriptor → Prop
  | .together, .Z
  | .opposite, .E => True
  | _, _ => False

/-- Executable transcription of the independent odd-cumulene `E/Z` relation. -/
def oddCumuleneEZDescriptor? : OddCumuleneTerminalGeometry → Option Descriptor
  | .together => some .Z
  | .opposite => some .E

/-- The reference evaluator is exactly the independent P-93.4.2.3 assignment relation. -/
theorem oddCumuleneEZDescriptor?_eq_some_iff
    (geometry : OddCumuleneTerminalGeometry) (descriptor : Descriptor) :
    oddCumuleneEZDescriptor? geometry = some descriptor ↔
      OddCumuleneEZAssignment geometry descriptor := by
  cases geometry <;> cases descriptor <;>
    simp [oddCumuleneEZDescriptor?, OddCumuleneEZAssignment]

/-- Every descriptor returned by the odd-cumulene reference evaluator is applicable and
recommended for a preferred IUPAC name. -/
theorem oddCumuleneEZDescriptor?_recommended
    (geometry : OddCumuleneTerminalGeometry) (descriptor : Descriptor)
    (computed : oddCumuleneEZDescriptor? geometry = some descriptor) :
    DescriptorApplies .oddDoubleBondCumulene descriptor ∧
      DescriptorRecommended .preferredIUPACName
        .oddDoubleBondCumulene descriptor := by
  cases geometry <;> cases descriptor <;>
    simp_all [oddCumuleneEZDescriptor?, DescriptorApplies, DescriptorRecommended]

/-- P-93.4.2.3 determines one and only one preferred `E/Z` descriptor from the relative
terminal-ligand geometry. -/
theorem existsUnique_odd_cumulene_EZ_descriptor
    (geometry : OddCumuleneTerminalGeometry) :
    ∃! descriptor, OddCumuleneEZAssignment geometry descriptor := by
  cases geometry
  · refine ⟨.Z, trivial, ?_⟩
    intro descriptor assigned
    cases descriptor <;> simp_all [OddCumuleneEZAssignment]
  · refine ⟨.E, trivial, ?_⟩
    intro descriptor assigned
    cases descriptor <;> simp_all [OddCumuleneEZAssignment]

/-! ## Center locants, isotopes, and multiple units -/

structure SingleCenterCitation (Locant : Type*) where
  descriptor : Descriptor
  locant? : Option Locant
  centerNeedsLocantInBaseName : Bool

def SingleCenterLocantConforms {Locant : Type*}
    (citation : SingleCenterCitation Locant) : Prop :=
  citation.locant?.isSome = citation.centerNeedsLocantInBaseName

inductive AffixKind where
  | stereochemical
  | isotopic
  deriving DecidableEq, Repr

/-- At one insertion point, stereochemical affixes precede isotopic affixes. -/
def AffixPrecedes : AffixKind → AffixKind → Prop
  | .stereochemical, .isotopic => True
  | _, _ => False

inductive IsotopicRuleUse where
  | sequenceRule1Only
  | sequenceRules1And2
  deriving DecidableEq, Repr

structure LocatedUnit (Locant Component : Type*) where
  locant : Locant
  component : Component
  kind : UnitKind
  descriptor : Descriptor
  deriving Repr

def LocatedUnit.Valid {Locant Component : Type*}
    (unit : LocatedUnit Locant Component) : Prop :=
  DescriptorApplies unit.kind unit.descriptor

def InAscendingLocantOrder {Locant Component : Type*} [LT Locant]
    (units : List (LocatedUnit Locant Component)) : Prop :=
  units.Pairwise fun first second => first.locant < second.locant

theorem nonstereogenic_cannot_appear_in_valid_descriptor_set
    {Locant Component : Type*} (unit : LocatedUnit Locant Component)
    (valid : unit.Valid) :
    unit.kind ≠ .nonstereogenic := by
  intro nonstereogenic
  change DescriptorApplies unit.kind unit.descriptor at valid
  rw [nonstereogenic] at valid
  exact nonstereogenic_unit_has_no_descriptor unit.descriptor valid

inductive CitationPosition (Component : Type*) where
  | frontOfCompleteName
  | immediatelyBeforeComponent (component : Component)
  deriving DecidableEq, Repr

def CorrectComponentPlacement {Locant Component : Type*}
    (unit : LocatedUnit Locant Component)
    (position : CitationPosition Component) : Prop :=
  match position with
  | .immediatelyBeforeComponent component => component = unit.component
  | .frontOfCompleteName => False

/-! ## Double-bond and cumulene conditions -/

structure CarbonDoubleBondContext where
  firstCarbonHasHydrogen : Bool
  secondCarbonHasHydrogen : Bool

def CisTransGeneralApplicable (context : CarbonDoubleBondContext) : Prop :=
  context.firstCarbonHasHydrogen = true ∧ context.secondCarbonHasHydrogen = true

theorem cisTrans_requires_one_hydrogen_at_each_end
    (context : CarbonDoubleBondContext)
    (applicable : CisTransGeneralApplicable context) :
    context.firstCarbonHasHydrogen = true ∧ context.secondCarbonHasHydrogen = true :=
  applicable

inductive DoubleBondAttachmentKind where
  | carbonCarbon
  | involvesHeteroatom
  deriving DecidableEq, Repr

def LonePairAtomicNumberForHeteroDoubleBond : ℕ := 0

@[simp] theorem hetero_double_bond_lone_pair_has_zero_priority_number :
    LonePairAtomicNumberForHeteroDoubleBond = 0 :=
  rfl

def HeteroDoubleBondDescriptorRecommended :
    NomenclatureContext → Descriptor → Prop
  | .preferredIUPACName, .E | .preferredIUPACName, .Z => True
  | .general, .E | .general, .Z => True
  | _, _ => False

theorem hetero_double_bond_rejects_cis_trans_syn_anti_surrogates :
    ¬HeteroDoubleBondDescriptorRecommended .general .cis ∧
    ¬HeteroDoubleBondDescriptorRecommended .general .trans := by
  constructor <;> simp [HeteroDoubleBondDescriptorRecommended]

structure CumulatedSystem where
  numberOfDoubleBonds : ℕ
  startingLocant : ℕ
  locantsConsecutive : Prop

def IsEvenCumulene (system : CumulatedSystem) : Prop :=
  Even system.numberOfDoubleBonds

def IsOddCumulene (system : CumulatedSystem) : Prop :=
  Odd system.numberOfDoubleBonds

theorem no_cumulene_is_even_and_odd (system : CumulatedSystem) :
    ¬(IsEvenCumulene system ∧ IsOddCumulene system) := by
  rintro ⟨even, odd⟩
  exact Nat.not_even_iff_odd.mpr odd even

/-- The locant attached to a consecutive cumulene descriptor is its starting point. -/
def cumuleneDescriptorLocant (system : CumulatedSystem) : ℕ :=
  system.startingLocant

/-! ### Topology before descriptor assignment

The Blue Book definition of a cumulative system is chain-shaped.  A connected order-two
network can therefore present three materially different authority cases: an open consecutive
chain, a closed cyclic chain, or a branch at which there is no unique cumulative chain.  The
last case does not make its constituent double bonds nonstereogenic; it changes the unit of
analysis from one cumulene to the individual physical double bonds.

These types are deliberately independent of the production molecule graph and its occurrence
zipper.  They state the routing obligation against which that implementation is proved below.
-/

/-- Global shape of one connected network of consecutive physical double bonds. -/
inductive ConsecutiveDoubleBondTopology where
  | openChain (numberOfDoubleBonds : ℕ) (nonempty : numberOfDoubleBonds ≠ 0)
  | closedCycle (numberOfDoubleBonds : ℕ) (nonempty : numberOfDoubleBonds ≠ 0)
  | branchedNetwork

/-- The chemically distinct analysis routes induced by the topology and open-chain parity. -/
inductive DoubleBondAnalysisRoute where
  | individualDoubleBond
  | oddOpenCumulene
  | evenOpenCumulene
  | cyclicCumulenePerception
  | eachBondOfBranchedNetwork
  deriving DecidableEq, Repr

/-- Independent P-93 routing relation.  A one-bond open chain is an ordinary double bond;
longer open chains are routed by parity; a closed cycle needs cyclic-cumulene perception; and
a branched non-chain network exposes each physical double bond as a separate candidate unit.

`eachBondOfBranchedNetwork` asserts only the unit boundary.  Each candidate must still pass the
ordinary P-92 stereogenic-unit test, endpoint ranking, and geometrical assignment before an
`E/Z` descriptor exists. -/
def DoubleBondAnalysisRouteApplies :
    ConsecutiveDoubleBondTopology → DoubleBondAnalysisRoute → Prop
  | .openChain count _, .individualDoubleBond => count = 1
  | .openChain count _, .oddOpenCumulene => count ≠ 1 ∧ Odd count
  | .openChain count _, .evenOpenCumulene => count ≠ 1 ∧ ¬Odd count
  | .closedCycle _ _, .cyclicCumulenePerception => True
  | .branchedNetwork, .eachBondOfBranchedNetwork => True
  | _, _ => False

/-- The topology/parity split chooses exactly one analysis route.  This is a routing theorem,
not a claim that the routed candidate is stereogenic. -/
theorem existsUnique_doubleBondAnalysisRoute
    (topology : ConsecutiveDoubleBondTopology) :
    ∃! route, DoubleBondAnalysisRouteApplies topology route := by
  cases topology with
  | openChain count nonempty =>
      by_cases ordinary : count = 1
      · refine ⟨.individualDoubleBond, ordinary, ?_⟩
        intro route applies
        cases route with
        | individualDoubleBond => rfl
        | oddOpenCumulene | evenOpenCumulene =>
            change count ≠ 1 ∧ _ at applies
            exact (applies.1 ordinary).elim
        | cyclicCumulenePerception | eachBondOfBranchedNetwork =>
            exact applies.elim
      · by_cases planar : Odd count
        · refine ⟨.oddOpenCumulene, ⟨ordinary, planar⟩, ?_⟩
          intro route applies
          cases route with
          | individualDoubleBond =>
              change count = 1 at applies
              exact (ordinary applies).elim
          | oddOpenCumulene => rfl
          | evenOpenCumulene =>
              change count ≠ 1 ∧ ¬Odd count at applies
              exact (applies.2 planar).elim
          | cyclicCumulenePerception | eachBondOfBranchedNetwork =>
              exact applies.elim
        · refine ⟨.evenOpenCumulene, ⟨ordinary, planar⟩, ?_⟩
          intro route applies
          cases route with
          | individualDoubleBond =>
              change count = 1 at applies
              exact (ordinary applies).elim
          | oddOpenCumulene =>
              change count ≠ 1 ∧ Odd count at applies
              exact (planar applies.2).elim
          | evenOpenCumulene => rfl
          | cyclicCumulenePerception | eachBondOfBranchedNetwork =>
              exact applies.elim
  | closedCycle count nonempty =>
      refine ⟨.cyclicCumulenePerception, trivial, ?_⟩
      intro route applies
      cases route <;> simp_all [DoubleBondAnalysisRouteApplies]
  | branchedNetwork =>
      refine ⟨.eachBondOfBranchedNetwork, trivial, ?_⟩
      intro route applies
      cases route <;> simp_all [DoubleBondAnalysisRouteApplies]

/-- Local continuation cardinality visible from one oriented physical double bond.  Unlike the
global topology, terminal and linear observations alone do not decide how the opposite side of
the connected network will end. -/
inductive LocalDoubleBondTopologyCase where
  | terminal
  | linearContinuation
  | cyclicClosure
  | multipleContinuations
  deriving DecidableEq, Repr

@[simp] theorem branched_network_route_is_per_bond :
    DoubleBondAnalysisRouteApplies .branchedNetwork .eachBondOfBranchedNetwork :=
  trivial

@[simp] theorem closed_cycle_route_is_separate_perception
    (numberOfDoubleBonds : ℕ) (nonempty : numberOfDoubleBonds ≠ 0) :
    DoubleBondAnalysisRouteApplies (.closedCycle numberOfDoubleBonds nonempty)
      .cyclicCumulenePerception :=
  trivial

inductive RelativeAttachment where
  | cis
  | trans
  deriving DecidableEq, Repr

/-- When otherwise permitted alternative numberings exist, cis (`Z`) wins at the first
stereochemical point of difference. -/
def PreferredAtFirstDifference : RelativeAttachment → Prop
  | .cis => True
  | .trans => False

@[simp] theorem cis_preferred_at_first_numbering_difference :
    PreferredAtFirstDifference .cis :=
  trivial

end BlueBookP93.Acyclic

end TetraStereo.OneCenter
